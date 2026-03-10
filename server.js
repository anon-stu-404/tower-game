'use strict';
const express = require('express');
const http    = require('http');
const { Server } = require('socket.io');
const p2      = require('p2');
const path    = require('path');

const app    = express();
const server = http.createServer(app);
const io     = new Server(server, { cors: { origin: '*' }, pingInterval: 10000, pingTimeout: 5000 });
const PORT   = process.env.PORT || 3000;
app.use(express.static(path.join(__dirname)));
// Explicit fallback: serve index.html for all GET requests (SPA-style)
app.get('*', (req, res) => {
  res.sendFile(path.join(__dirname, 'index.html'));
});

// ─── SHAPES ──────────────────────────────────────────────────────────────────
const SHAPES = {
  square:    { v:[[-0.40,-0.40],[0.40,-0.40],[0.40,0.40],[-0.40,0.40]],           c:'#6ee7f7' },
  rectangle: { v:[[-0.72,-0.24],[0.72,-0.24],[0.72,0.24],[-0.72,0.24]],           c:'#a78bfa' },
  tallrect:  { v:[[-0.20,-0.70],[0.20,-0.70],[0.20,0.70],[-0.20,0.70]],           c:'#67e8f9' },
  triangle:  { v:[[0,-0.60],[0.58,0.52],[-0.58,0.52]],                            c:'#fbbf24' },
  thintri:   { v:[[0,-0.78],[0.22,0.78],[-0.22,0.78]],                            c:'#fde68a' },
  trapezoid: { v:[[-0.78,-0.26],[0.78,-0.26],[0.42,0.26],[-0.42,0.26]],           c:'#34d399' },
  hexagon:   { v:(()=>{const p=[];for(let i=0;i<6;i++){const a=Math.PI/6+i*Math.PI/3;p.push([+(Math.cos(a)*0.50).toFixed(4),+(Math.sin(a)*0.50).toFixed(4)]);}return p;})(), c:'#f472b6' },
  lshape:    { v:[[-0.52,-0.52],[0.52,-0.52],[0.52,0.0],[0.10,0.0],[0.10,0.52],[-0.52,0.52]], c:'#fb923c',
               parts:[[[-0.52,-0.52],[0.52,-0.52],[0.52,0.0],[-0.52,0.0]],[[-0.52,0.0],[0.10,0.0],[0.10,0.52],[-0.52,0.52]]] },
  irregular: { v:[[-0.62,-0.36],[0.26,-0.60],[0.66,0.10],[0.16,0.56],[-0.46,0.48]], c:'#e879f9' },
  diamond:   { v:[[0,-0.62],[0.42,0],[0,0.62],[-0.42,0]],                         c:'#f9a8d4' },
  wedge:     { v:[[-0.68,-0.32],[0.68,-0.32],[0.68,0.32],[-0.68,0.04]],           c:'#86efac' },
  zigzag:    { v:[[-0.60,-0.36],[-0.10,-0.36],[0.10,0.0],[0.60,0.0],[0.60,0.36],[0.10,0.36],[-0.10,0.0],[-0.60,0.0]],
               parts:[[[-0.60,-0.36],[0.10,-0.36],[0.10,0.0],[-0.60,0.0]],[[-0.10,0.0],[0.60,0.0],[0.60,0.36],[-0.10,0.36]]], c:'#f87171' },
};

const ROUNDS = [
  { pw:5.5, pool:['square','rectangle','tallrect','triangle'] },
  { pw:4.0, pool:['rectangle','tallrect','triangle','thintri','trapezoid','hexagon','wedge'] },
  { pw:2.8, pool:['thintri','trapezoid','hexagon','lshape','irregular','diamond','wedge','zigzag'] },
];

const PLAT_H=0.3, FALL_Y=-8, DROP_Y=9;
const STEP=1/60, SETTLE_N=50, VT=0.10, AT=0.10, MAX_STEPS=420;
const MOVE_D=0.28; // metres per press

let gBodyId=0;
const rooms={};

// ─── WORLD ───────────────────────────────────────────────────────────────────
function mkWorld(pw){
  const w=new p2.World({gravity:[0,-14]});
  w.sleepMode=p2.World.BODY_SLEEPING;
  w.solver.iterations=7;
  const pm=new p2.Material(), dm=new p2.Material();
  const pb=new p2.Body({mass:0,position:[0,-PLAT_H/2]});
  const ps=new p2.Box({width:pw,height:PLAT_H});
  ps.material=pm; pb.addShape(ps); w.addBody(pb);
  w.addContactMaterial(new p2.ContactMaterial(pm,dm,{friction:0.28,restitution:0.22,relaxation:4}));
  w.addContactMaterial(new p2.ContactMaterial(dm,dm,{friction:0.22,restitution:0.20}));
  w._dm=dm; return w;
}

function rndShape(r){ const p=ROUNDS[r].pool; return p[Math.floor(Math.random()*p.length)]; }
function clampX(x,pw){ const l=pw*0.50; return Math.max(-l,Math.min(l,x)); }

function mkRoom(id){
  const room={id,players:{},names:new Set(),scores:{rizwan:0,anha:0},round:0,turn:'rizwan',
    bodies:[],world:null,pbodies:[],settling:false,matchOver:false,winner:null,
    shape:null,chat:[],active:false};
  startRound(room); return room;
}

function startRound(rm){
  rm.world=mkWorld(ROUNDS[rm.round].pw);
  rm.bodies=[]; rm.pbodies=[]; rm.settling=false; rm.active=true; rm.matchOver=false;
  rm.turn=rm.round===0?'rizwan':rm.round===1?'anha':'rizwan';
  rm.shape={name:rndShape(rm.round),rot:0,x:0};
}

function serial(rm){
  return {
    scores:rm.scores, round:rm.round, turn:rm.turn, settling:rm.settling,
    matchOver:rm.matchOver, winner:rm.winner, active:rm.active,
    pw:ROUNDS[rm.round].pw, shape:{...rm.shape},
    bodies:rm.bodies.map(b=>({id:b.id,name:b.name,v:b.v,pos:[...b.pos],angle:b.angle,c:b.c}))
  };
}

// ─── PHYSICS SETTLE ──────────────────────────────────────────────────────────
function drop(rm){
  const sd=SHAPES[rm.shape.name];
  const jitter=(Math.random()-0.5)*0.10;
  const x=rm.shape.x+jitter, y=DROP_Y, angle=rm.shape.rot;

  const body=new p2.Body({mass:1,position:[x,y],angle,angularDamping:0.15,damping:0.04});
  body.sleepSpeedLimit=VT; body.sleepTimeLimit=0.3;

  if(sd.parts){
    sd.parts.forEach(pts=>{ const s=new p2.Convex({vertices:pts}); s.material=rm.world._dm; body.addShape(s); });
  } else {
    const s=new p2.Convex({vertices:sd.v}); s.material=rm.world._dm; body.addShape(s);
  }
  body.updateMassProperties();
  rm.world.addBody(body); rm.pbodies.push(body);
  rm.bodies.push({id:++gBodyId,name:rm.shape.name,v:sd.v,pos:[x,y],angle,c:sd.c});
  rm.settling=true;
  settle(rm);
}

function settle(rm){
  let idle=0,steps=0;
  function tick(){
    if(!rm.settling) return;
    // 3 sub-steps per tick — faster convergence, still stable
    rm.world.step(STEP); rm.world.step(STEP); rm.world.step(STEP);
    steps+=3;
    rm.bodies.forEach((b,i)=>{ const p=rm.pbodies[i]; if(p){b.pos=[...p.position];b.angle=p.angle;} });
    // Broadcast every 9 sub-steps
    if(steps%9===0) io.to(rm.id).emit('S',serial(rm));
    const calm=rm.pbodies.every(p=>Math.abs(p.velocity[0])<VT&&Math.abs(p.velocity[1])<VT&&Math.abs(p.angularVelocity)<AT);
    idle=calm?idle+1:0;
    if(idle>=SETTLE_N||steps>=MAX_STEPS){ done(rm); return; }
    setImmediate(tick);
  }
  setImmediate(tick);
}

function done(rm){
  rm.settling=false;
  const fell=rm.bodies.some(b=>b.pos[1]<FALL_Y);
  if(fell){
    const loser=rm.turn, winner=loser==='rizwan'?'anha':'rizwan';
    rm.scores[winner]++; rm.active=false;
    if(rm.scores[winner]>=2){ rm.matchOver=true; rm.winner=winner; io.to(rm.id).emit('S',serial(rm)); }
    else {
      io.to(rm.id).emit('S',serial(rm));
      rm.round=(rm.round+1)%3;
      setTimeout(()=>{ startRound(rm); rm.turn=winner==='rizwan'?'anha':'rizwan'; rm.shape={name:rndShape(rm.round),rot:0,x:0}; io.to(rm.id).emit('S',serial(rm)); },3000);
    }
  } else {
    rm.turn=rm.turn==='rizwan'?'anha':'rizwan';
    rm.shape={name:rndShape(rm.round),rot:0,x:0};
    io.to(rm.id).emit('S',serial(rm));
  }
}

// ─── SOCKETS ─────────────────────────────────────────────────────────────────
io.on('connection',sock=>{
  let room=null,name=null;

  sock.on('join',({r,p})=>{
    const n=(p||'').toLowerCase().trim();
    if(n!=='rizwan'&&n!=='anha'){ sock.emit('rejected','🔒 Private game — only Rizwan and Anha can play.'); return; }
    if(!rooms[r]) rooms[r]=mkRoom(r);
    const rm=rooms[r]; room=r; name=n;
    rm.players[sock.id]=n; rm.names.add(n);
    sock.join(r);
    sock.emit('you',n);
    sock.emit('S',serial(rm));
    io.to(r).emit('joined',{n,all:[...rm.names]});
  });

  sock.on('move',dir=>{
    if(!room||!rooms[room]) return;
    const rm=rooms[room];
    if(rm.settling||rm.turn!==name||rm.matchOver||!rm.active) return;
    const d=dir==='L'?-MOVE_D:MOVE_D;
    rm.shape.x=clampX(rm.shape.x+d, ROUNDS[rm.round].pw);
    sock.emit('S',serial(rm));           // only emit to mover for instant feedback
    sock.to(room).emit('S',serial(rm));  // opponent sees it too
  });

  sock.on('rot',dir=>{
    if(!room||!rooms[room]) return;
    const rm=rooms[room];
    if(rm.settling||rm.turn!==name||rm.matchOver) return;
    rm.shape.rot=(rm.shape.rot+(dir==='L'?-0.4:0.4))%(Math.PI*2);
    io.to(room).emit('S',serial(rm));
  });

  sock.on('drop',()=>{
    if(!room||!rooms[room]) return;
    const rm=rooms[room];
    if(rm.settling||rm.turn!==name||rm.matchOver||!rm.active) return;
    drop(rm);
  });

  sock.on('chat',msg=>{
    if(!room||!name) return;
    const m={from:name,text:(msg||'').slice(0,200),t:new Date().toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'})};
    io.to(room).emit('chat',m);
  });

  sock.on('again',()=>{
    if(!room||!rooms[room]) return;
    const rm=rooms[room];
    if(!rm.matchOver) return;
    rm.scores={rizwan:0,anha:0}; rm.round=0; rm.winner=null; rm.matchOver=false;
    startRound(rm); io.to(room).emit('S',serial(rm));
  });

  sock.on('disconnect',()=>{
    if(room&&rooms[room]){ delete rooms[room].players[sock.id];
      if(!Object.keys(rooms[room].players).length) setTimeout(()=>{ if(rooms[room]&&!Object.keys(rooms[room].players).length) delete rooms[room]; },60000); }
  });
});

server.listen(PORT,()=>console.log('Tower :'+PORT));
