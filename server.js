'use strict';

const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const p2 = require('p2');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: '*' }
});

const PORT = process.env.PORT || 3000;
app.use(express.static(path.join(__dirname)));

// ─── Shape Library ────────────────────────────────────────────────────────────
// All shapes defined as convex polygons with LOCAL vertices (centred at origin)
// Vertices in counter-clockwise order, units = metres

const SHAPES = {
  square: {
    name: 'square',
    vertices: [[-0.5,-0.5],[0.5,-0.5],[0.5,0.5],[-0.5,0.5]],
    color: '#6ee7f7'
  },
  rectangle: {
    name: 'rectangle',
    vertices: [[-0.8,-0.35],[0.8,-0.35],[0.8,0.35],[-0.8,0.35]],
    color: '#a78bfa'
  },
  triangle: {
    name: 'triangle',
    vertices: [[0,-0.6],[0.55,0.5],[-0.55,0.5]],
    color: '#fbbf24'
  },
  trapezoid: {
    name: 'trapezoid',
    vertices: [[-0.9,-0.35],[0.9,-0.35],[0.55,0.35],[-0.55,0.35]],
    color: '#34d399'
  },
  hexagon: {
    name: 'hexagon',
    vertices: (()=>{
      const pts = [];
      for(let i=0;i<6;i++){
        const a = Math.PI/6 + i*Math.PI/3;
        pts.push([Math.cos(a)*0.6, Math.sin(a)*0.6]);
      }
      return pts;
    })(),
    color: '#f472b6'
  },
  lshape: {
    // L-shape decomposed into a single convex approximation (wider at base)
    name: 'lshape',
    vertices: [[-0.6,-0.6],[0.6,-0.6],[0.6,0.0],[0.1,0.0],[0.1,0.6],[-0.6,0.6]],
    color: '#fb923c',
    convexParts: [
      [[-0.6,-0.6],[0.6,-0.6],[0.6,0.0],[-0.6,0.0]],
      [[-0.6,0.0],[0.1,0.0],[0.1,0.6],[-0.6,0.6]]
    ]
  },
  irregular: {
    name: 'irregular',
    vertices: [[-0.7,-0.4],[0.3,-0.6],[0.7,0.1],[0.2,0.6],[-0.5,0.5]],
    color: '#e879f9'
  }
};

// Round configurations
const ROUND_CONFIG = [
  { platformWidth: 6,   shapes: ['square','rectangle','triangle'] },
  { platformWidth: 4.5, shapes: ['square','rectangle','triangle','trapezoid','hexagon'] },
  { platformWidth: 3,   shapes: ['square','rectangle','triangle','trapezoid','hexagon','lshape','irregular'] }
];

const PLATFORM_HEIGHT = 0.3;
const PLATFORM_Y     = 0;      // world-space y of platform top surface
const FALL_THRESHOLD = -6;     // if body centre.y < this, it "fell"
const DROP_HEIGHT    = 8;      // y above platform where shape spawns
const PHYSICS_STEP   = 1/60;
const SETTLE_IDLE_STEPS = 90;  // consecutive steps all bodies near-zero before "settled"
const VELOCITY_THRESHOLD = 0.05;
const ANGULAR_THRESHOLD  = 0.05;

// ─── Room Manager ─────────────────────────────────────────────────────────────
const rooms = {};  // roomId → RoomState

function createPhysicsWorld(platformWidth) {
  const world = new p2.World({ gravity: [0, -9.82] });
  world.sleepMode = p2.World.BODY_SLEEPING;

  // Platform body (static)
  const platformBody = new p2.Body({ mass: 0, position: [0, PLATFORM_Y - PLATFORM_HEIGHT/2] });
  const platformShape = new p2.Box({ width: platformWidth, height: PLATFORM_HEIGHT });
  platformShape.material = new p2.Material();
  platformBody.addShape(platformShape);
  world.addBody(platformBody);

  // Contact material for decent friction & restitution
  const dynMat = new p2.Material();
  const contact = new p2.ContactMaterial(platformShape.material, dynMat, {
    friction: 0.6,
    restitution: 0.1
  });
  world.addContactMaterial(contact);
  world._dynMat = dynMat;
  world._contact = contact;

  return world;
}

function randomShape(round) {
  const pool = ROUND_CONFIG[round].shapes;
  return pool[Math.floor(Math.random() * pool.length)];
}

function createRoom(roomId) {
  const room = {
    id: roomId,
    players: {},          // socketId → playerName
    playerNames: new Set(),
    scores: { rizwan: 0, anha: 0 },
    round: 0,             // 0-indexed
    turn: 'rizwan',
    bodies: [],           // serialisable body records
    world: null,
    physicsBodies: [],    // p2 body refs parallel to bodies[]
    settling: false,
    matchOver: false,
    winner: null,
    currentShape: null,   // { shapeName, rotation }
    chatMessages: [],
    roundActive: false
  };
  initRound(room);
  return room;
}

function initRound(room) {
  const cfg = ROUND_CONFIG[room.round];

  // Destroy old world
  room.world = createPhysicsWorld(cfg.platformWidth);
  room.bodies = [];
  room.physicsBodies = [];
  room.settling = false;
  room.roundActive = true;
  room.matchOver = false;

  // Decide who starts this round
  room.turn = room.round === 0 ? 'rizwan' : (room.round === 1 ? 'anha' : 'rizwan');
  room.currentShape = { shapeName: randomShape(room.round), rotation: 0 };
}

function serializeState(room) {
  const cfg = ROUND_CONFIG[room.round];
  return {
    scores: room.scores,
    round: room.round,
    turn: room.turn,
    settling: room.settling,
    matchOver: room.matchOver,
    winner: room.winner,
    roundActive: room.roundActive,
    platformWidth: cfg.platformWidth,
    currentShape: room.currentShape,
    bodies: room.bodies.map(b => ({
      id: b.id,
      shapeName: b.shapeName,
      vertices: b.vertices,
      position: [...b.position],
      angle: b.angle,
      color: b.color
    }))
  };
}

// ─── Physics drop & settle ────────────────────────────────────────────────────
let bodyIdCounter = 0;

function dropShape(room) {
  const cfg = ROUND_CONFIG[room.round];
  const shapeDef = SHAPES[room.currentShape.shapeName];
  const angle    = room.currentShape.rotation;
  const xOffset  = (Math.random() - 0.5) * (cfg.platformWidth / 1.8);
  const spawnY   = DROP_HEIGHT;

  // Build p2 body
  const body = new p2.Body({
    mass: 1,
    position: [xOffset, spawnY],
    angle: angle,
    angularDamping: 0.3,
    damping: 0.1
  });
  body.sleepSpeedLimit = VELOCITY_THRESHOLD;
  body.sleepTimeLimit  = 0.5;

  let pShape;
  if (room.currentShape.shapeName === 'lshape') {
    // Decompose into two convex parts
    shapeDef.convexParts.forEach(part => {
      const cs = new p2.Convex({ vertices: part });
      cs.material = room.world._dynMat;
      body.addShape(cs);
    });
    pShape = body.shapes[0];
  } else {
    pShape = new p2.Convex({ vertices: shapeDef.vertices });
    pShape.material = room.world._dynMat;
    body.addShape(pShape);
  }

  body.updateMassProperties();
  room.world.addBody(body);
  room.physicsBodies.push(body);

  const bId = ++bodyIdCounter;
  room.bodies.push({
    id: bId,
    shapeName: room.currentShape.shapeName,
    vertices: shapeDef.vertices,
    position: [xOffset, spawnY],
    angle: angle,
    color: shapeDef.color,
    _ref: body
  });

  room.settling = true;
  simulateUntilSettled(room);
}

function simulateUntilSettled(room) {
  let idleSteps = 0;
  const MAX_STEPS = 600; // hard cap ~10 seconds
  let stepCount = 0;

  function step() {
    if (!room.settling) return;

    room.world.step(PHYSICS_STEP);
    stepCount++;

    // Sync positions back to serialisable records
    room.bodies.forEach((b, i) => {
      const pb = room.physicsBodies[i];
      if (pb) {
        b.position = [...pb.position];
        b.angle    = pb.angle;
      }
    });

    // Broadcast live positions during settling (rate-limited)
    if (stepCount % 3 === 0) {
      io.to(room.id).emit('stateUpdate', serializeState(room));
    }

    // Check if all bodies are calm
    const allSleeping = room.physicsBodies.every(pb => {
      const vx = Math.abs(pb.velocity[0]);
      const vy = Math.abs(pb.velocity[1]);
      const av = Math.abs(pb.angularVelocity);
      return vx < VELOCITY_THRESHOLD && vy < VELOCITY_THRESHOLD && av < ANGULAR_THRESHOLD;
    });

    if (allSleeping) idleSteps++;
    else              idleSteps = 0;

    if (idleSteps >= SETTLE_IDLE_STEPS || stepCount >= MAX_STEPS) {
      onSettled(room);
      return;
    }

    setImmediate(step);
  }

  setImmediate(step);
}

function onSettled(room) {
  room.settling = false;

  // Check for fallen bodies
  const fell = room.bodies.some(b => b.position[1] < FALL_THRESHOLD);

  if (fell) {
    // The current turn player caused the fall → opponent wins the round
    const loser  = room.turn;
    const winner = loser === 'rizwan' ? 'anha' : 'rizwan';
    room.scores[winner]++;
    room.roundActive = false;

    // Check match winner (best of 3)
    if (room.scores[winner] >= 2) {
      room.matchOver = true;
      room.winner    = winner;
    } else {
      // Advance round
      room.round = (room.round + 1) % 3;
      // Delay so clients can show "round over" for a moment
      setTimeout(() => {
        initRound(room);
        room.turn = winner === 'rizwan' ? 'anha' : 'rizwan'; // loser starts next
        room.currentShape = { shapeName: randomShape(room.round), rotation: 0 };
        io.to(room.id).emit('stateUpdate', serializeState(room));
      }, 3000);
    }
  } else {
    // Switch turns
    room.turn = room.turn === 'rizwan' ? 'anha' : 'rizwan';
    room.currentShape = { shapeName: randomShape(room.round), rotation: 0 };
  }

  io.to(room.id).emit('stateUpdate', serializeState(room));
}

// ─── Socket.io ────────────────────────────────────────────────────────────────
io.on('connection', socket => {
  let currentRoom = null;
  let playerName  = null;

  socket.on('join', ({ room: roomId, player }) => {
    const name = (player || '').toLowerCase().trim();

    if (name !== 'rizwan' && name !== 'anha') {
      socket.emit('rejected', { message: '🔒 This game is private — only Rizwan and Anha can play.' });
      return;
    }

    if (!rooms[roomId]) rooms[roomId] = createRoom(roomId);
    const rm = rooms[roomId];

    currentRoom = roomId;
    playerName  = name;
    rm.players[socket.id] = name;
    rm.playerNames.add(name);

    socket.join(roomId);
    socket.emit('joined', { playerName: name });
    socket.emit('stateUpdate', serializeState(rm));

    // Notify room
    io.to(roomId).emit('playerJoined', {
      name,
      players: [...rm.playerNames]
    });
  });

  socket.on('rotate', ({ direction }) => {
    if (!currentRoom || !rooms[currentRoom]) return;
    const rm = rooms[currentRoom];
    if (rm.settling || rm.turn !== playerName || rm.matchOver) return;

    const delta = direction === 'left' ? -0.4 : 0.4;
    rm.currentShape.rotation = (rm.currentShape.rotation + delta) % (Math.PI * 2);
    io.to(currentRoom).emit('stateUpdate', serializeState(rm));
  });

  socket.on('drop', () => {
    if (!currentRoom || !rooms[currentRoom]) return;
    const rm = rooms[currentRoom];
    if (rm.settling || rm.turn !== playerName || rm.matchOver || !rm.roundActive) return;

    dropShape(rm);
  });

  socket.on('chat', ({ message }) => {
    if (!currentRoom || !playerName || !message) return;
    const msg = {
      sender: playerName,
      text: message.slice(0, 200),
      time: new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' })
    };
    if (rooms[currentRoom]) rooms[currentRoom].chatMessages.push(msg);
    io.to(currentRoom).emit('chat', msg);
  });

  socket.on('playAgain', () => {
    if (!currentRoom || !rooms[currentRoom]) return;
    const rm = rooms[currentRoom];
    if (!rm.matchOver) return;

    rm.scores  = { rizwan: 0, anha: 0 };
    rm.round   = 0;
    rm.winner  = null;
    rm.matchOver = false;
    initRound(rm);
    io.to(currentRoom).emit('stateUpdate', serializeState(rm));
  });

  socket.on('disconnect', () => {
    if (currentRoom && rooms[currentRoom]) {
      const rm = rooms[currentRoom];
      delete rm.players[socket.id];
      // Keep room alive for reconnection; clean up if completely empty
      if (Object.keys(rm.players).length === 0) {
        setTimeout(() => {
          if (rooms[currentRoom] && Object.keys(rooms[currentRoom].players).length === 0) {
            delete rooms[currentRoom];
          }
        }, 60000);
      }
    }
  });
});

server.listen(PORT, () => console.log(`🎮 Tower game server on port ${PORT}`));
