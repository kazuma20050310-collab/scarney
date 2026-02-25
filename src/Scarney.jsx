import { useState, useCallback, useEffect, useRef } from "react";
import {
  getRoom, setRoom, deleteRoom, subscribeRoom,
  getSession, saveSession, clearSession,
  joinQueue, tryMatch, leaveQueue, getQueueCount,
} from "./supabase";

const SUITS = ["♠","♥","♦","♣"];
const RANKS = ["2","3","4","5","6","7","8","9","10","J","Q","K","A"];
const RV = {2:2,3:3,4:4,5:5,6:6,7:7,8:8,9:9,10:10,J:11,Q:12,K:13,A:14};
const LP = {2:2,3:3,4:4,5:5,6:6,7:7,8:8,9:9,10:10,J:10,Q:10,K:10,A:1};
const HN = ["ハイカード","ワンペア","ツーペア","スリーカード","ストレート","フラッシュ","フルハウス","フォーカード","ストレートフラッシュ","ロイヤルフラッシュ"];
const STACKS = [5000,10000,20000,40000];
const ANTE = 200;
const MATCH_STACK = 10000;
const PH_LIST = ["deal","flop","turn","river","showdown"];
const PH_JP = {deal:"ディール",flop:"フロップ",turn:"ターン",river:"リバー",showdown:"ショーダウン"};

function shuffle(a){const b=[...a];for(let i=b.length-1;i>0;i--){const j=0|Math.random()*(i+1);[b[i],b[j]]=[b[j],b[i]];}return b;}
function makeDeck(){const d=[];for(const s of SUITS)for(const r of RANKS)d.push({rank:r,suit:s});return shuffle(d);}
function isRed(c){return c.suit==="♥"||c.suit==="♦";}
function lowPts(h){return h.reduce((s,c)=>s+LP[c.rank],0);}
function uid(){return Math.random().toString(36).slice(2,10);}
function rcode(){const ch="ABCDEFGHJKLMNPQRSTUVWXYZ23456789";let r="";for(let i=0;i<4;i++)r+=ch[0|Math.random()*ch.length];return r;}
function dc(o){return JSON.parse(JSON.stringify(o));}

function combos(a,k){if(!k)return[[]];if(a.length<k)return[];const[f,...r]=a;return[...combos(r,k-1).map(c=>[f,...c]),...combos(r,k)];}
function eval5(cards){
  const v=cards.map(c=>RV[c.rank]).sort((a,b)=>a-b);
  const fl=cards.every(c=>c.suit===cards[0].suit);
  const u=[...new Set(v)].sort((a,b)=>a-b);
  const st=u.length===5&&(u[4]-u[0]===4||u.join()==="2,3,4,5,14");
  const lo=u.join()==="2,3,4,5,14";
  const cn={};v.forEach(x=>cn[x]=(cn[x]||0)+1);
  const g=Object.entries(cn).map(([x,c])=>({v:+x,c})).sort((a,b)=>b.c-a.c||b.v-a.v);
  if(fl&&st)return v.join()==="10,11,12,13,14"?{rank:9,name:HN[9],score:9e12}:{rank:8,name:HN[8],score:8e12+(lo?5:v[4])};
  if(g[0].c===4)return{rank:7,name:HN[7],score:7e12+g[0].v*1e6+(g[1]?g[1].v:0)};
  if(g[0].c===3&&g.length>1&&g[1].c===2)return{rank:6,name:HN[6],score:6e12+g[0].v*1e6+g[1].v};
  if(fl)return{rank:5,name:HN[5],score:5e12+v[4]*1e8+v[3]*1e6+v[2]*1e4+v[1]*100+v[0]};
  if(st)return{rank:4,name:HN[4],score:4e12+(lo?5:v[4])};
  if(g[0].c===3)return{rank:3,name:HN[3],score:3e12+g[0].v*1e6};
  if(g[0].c===2&&g.length>1&&g[1].c===2){const h2=Math.max(g[0].v,g[1].v),l2=Math.min(g[0].v,g[1].v);return{rank:2,name:HN[2],score:2e12+h2*1e6+l2*1e4+(g[2]?g[2].v:0)};}
  if(g[0].c===2)return{rank:1,name:HN[1],score:1e12+g[0].v*1e6};
  return{rank:0,name:HN[0],score:v[4]*1e8+v[3]*1e6+v[2]*1e4+v[1]*100+v[0]};
}
function evalHand(cards){if(!cards||cards.length<5)return{rank:-1,name:"—",score:-1};let b=null;for(const c of combos(cards,5)){const e=eval5(c);if(!b||e.score>b.score)b=e;}return b;}

const CPU_NAMES=["CPU-1","CPU-2","CPU-3","CPU-4","CPU-5"];
function isCpu(p){return!!p.cpu;}
function cpuDecide(gs,room,pid){
  const chips=room.chips[pid]||0;if(chips===0)return{type:"check"};
  const cb=gs.betting.currentBet,myBet=gs.betting.bets[pid]||0,toCall=cb-myBet;
  const hand=gs.hands[pid]||[],top=(gs.top||[]).filter(Boolean);
  const ev=hand.length>=2&&top.length>=3?evalHand([...hand,...top]):null;
  const str=ev?ev.rank/9:0.3;
  if(cb===0){const r=Math.random();if(r<0.55-str*0.2)return{type:"check"};const amt=Math.min(Math.max(100,Math.floor(gs.pot*(0.3+str*0.4))),chips);return{type:"bet",amount:amt};}
  else{const r=Math.random(),ft=Math.max(0.05,0.35-str*0.3);if(r<ft&&toCall>chips*0.3)return{type:"fold"};if(r<ft+0.55||chips<=toCall)return{type:"call"};const ra=Math.min(cb+Math.max(gs.betting.minRaise||100,Math.floor(gs.pot*0.5)),chips+myBet);return{type:"raise",amount:ra};}
}

function aliveIds(gs,ps){return ps.filter(p=>!gs.folded[p.id]&&!gs.down[p.id]).map(p=>p.id);}
function findFirstActor(ps,btnIdx,gs){const n=ps.length;for(let i=1;i<=n;i++){const p=ps[(btnIdx+i)%n];if(!gs.folded[p.id]&&!gs.down[p.id])return p.id;}return null;}
function findNextActor(ps,curId,gs){const ids=ps.map(p=>p.id);const ci=ids.indexOf(curId);const n=ids.length;for(let i=1;i<n;i++){const id=ids[(ci+i)%n];if(gs.folded[id]||gs.down[id])continue;if(!gs.betting.acted[id]||(gs.betting.bets[id]||0)<gs.betting.currentBet)return id;}return null;}
function allAliveAllIn(gs,ps,chips){const alive=aliveIds(gs,ps);if(alive.length<=1)return true;return alive.every(id=>(chips[id]||0)===0);}
function startBetting(gs,ps,chips){const alive=aliveIds(gs,ps);if(alive.length<=1)return null;if(allAliveAllIn(gs,ps,chips))return null;const fid=findFirstActor(ps,gs.btn,gs);if(!fid)return null;return{currentBet:0,bets:{},acted:{},actorId:fid,minRaise:10};}

function makeGame(ps,round,btn,chips){
  const deck=makeDeck();const hands={},disc={},down={},reason={},folded={};let pot=0;const log=[];
  ps.forEach(p=>{hands[p.id]=deck.splice(0,6);disc[p.id]=[];down[p.id]=false;reason[p.id]="";folded[p.id]=false;
    const ante=Math.min(ANTE,chips[p.id]||0);chips[p.id]-=ante;pot+=ante;});
  log.push("R"+(round||1)+" — BTN: "+ps[btn||0].name);
  log.push("💰 ボムポット "+ANTE+" × "+ps.length+" → "+pot);
  return{deck,hands,disc,down,reason,folded,top:Array(6).fill(null),bot:Array(6).fill(null),phase:"deal",pot,round:round||1,btn:btn||0,betting:null,results:null,allInShow:false,log};
}
function openCards(gs,ps){
  const s=dc(gs);const n=s.phase==="deal"?3:s.phase==="flop"?2:s.phase==="turn"?1:0;if(!n)return s;
  const tI=s.top.filter(Boolean).length,bI=s.bot.filter(Boolean).length;const nr=new Set();
  for(let i=0;i<n;i++)if(s.deck.length)s.top[tI+i]=s.deck.shift();
  for(let i=0;i<n;i++)if(s.deck.length){const c=s.deck.shift();s.bot[bI+i]=c;nr.add(c.rank);}
  const next=s.phase==="deal"?"flop":s.phase==="flop"?"turn":"river";
  s.log.push("── "+PH_JP[next]+" ──");
  for(const p of ps){if(s.folded[p.id]||s.down[p.id])continue;const kept=[],toss=[];
    for(const c of(s.hands[p.id]||[]))nr.has(c.rank)?toss.push(c):kept.push(c);
    s.hands[p.id]=kept;s.disc[p.id]=[...(s.disc[p.id]||[]),...toss];
    s.log.push(p.name+": "+(toss.length?toss.map(c=>c.rank+c.suit).join(" ")+"捨て":"—")+"(残"+kept.length+")");}
  if(next==="river"){for(const p of ps){if(s.folded[p.id]||s.down[p.id])continue;const hl=(s.hands[p.id]||[]).length;
    if(hl===0){s.down[p.id]=true;s.reason[p.id]="0枚";s.log.push("💀"+p.name+" バースト(0枚)");}
    else if(hl===6){s.down[p.id]=true;s.reason[p.id]="6枚";s.log.push("💀"+p.name+" バースト(6枚)");}}}
  s.phase=next;return s;
}
function doAdvancePhase(gs,ps,chips){
  let s=openCards(gs,ps);const alive=aliveIds(s,ps);
  if(alive.length<=1)return doShowdown(s,ps);
  const bet=startBetting(s,ps,chips);
  if(bet){s.betting=bet;s.log.push("🎲 "+((ps.find(p=>p.id===bet.actorId)||{}).name||"?"));return s;}
  if(s.phase==="river"){s.log.push("⚡ All-in → SD");return doShowdown(s,ps);}
  s.allInShow=true;s.log.push("⚡ All-in公開");return s;
}
function doBetAction(gs,room,ps,pid,action,amount){
  const s=dc(gs),r=dc(room);const pn=(ps.find(p=>p.id===pid)||{}).name||"?";const chips=r.chips;
  if(action==="check"){s.betting.acted[pid]=true;s.log.push(pn+": チェック");}
  else if(action==="fold"){s.folded[pid]=true;s.log.push(pn+": フォールド");}
  else if(action==="bet"){const amt=Math.min(amount,chips[pid]||0);s.betting.bets[pid]=amt;s.betting.currentBet=amt;s.betting.minRaise=amt;aliveIds(s,ps).forEach(id=>{s.betting.acted[id]=false;});s.betting.acted[pid]=true;chips[pid]-=amt;s.pot+=amt;s.log.push(pn+": Bet "+amt+(chips[pid]===0?" AI":""));}
  else if(action==="call"){const owed=Math.min(s.betting.currentBet-(s.betting.bets[pid]||0),chips[pid]||0);s.betting.bets[pid]=(s.betting.bets[pid]||0)+owed;s.betting.acted[pid]=true;chips[pid]-=owed;s.pot+=owed;s.log.push(pn+": Call "+owed+(chips[pid]===0?" AI":""));}
  else if(action==="raise"){const already=s.betting.bets[pid]||0;const total=Math.min(amount,already+(chips[pid]||0));const pay=total-already;s.betting.minRaise=Math.max(total-s.betting.currentBet,s.betting.minRaise);s.betting.bets[pid]=total;s.betting.currentBet=total;aliveIds(s,ps).forEach(id=>{s.betting.acted[id]=false;});s.betting.acted[pid]=true;chips[pid]-=pay;s.pot+=pay;s.log.push(pn+": Raise "+total+(chips[pid]===0?" AI":""));}
  const alive=aliveIds(s,ps);
  if(alive.length<=1){s.betting=null;return{gs:doShowdown(s,ps),room:r};}
  if(allAliveAllIn(s,ps,chips)){s.betting=null;if(s.phase==="river"){s.log.push("⚡ All-in → SD");return{gs:doShowdown(s,ps),room:r};}s.allInShow=true;s.log.push("⚡ All-in公開");return{gs:s,room:r};}
  const ni=findNextActor(ps,pid,s);
  if(ni){s.betting.actorId=ni;return{gs:s,room:r};}
  s.betting=null;s.log.push("Betting終了");
  if(s.phase==="river"){return{gs:doShowdown(s,ps),room:r};}
  const ng=doAdvancePhase(s,ps,chips);return{gs:ng,room:r};
}
function doShowdown(gs,ps){
  const s=dc(gs);s.phase="showdown";s.betting=null;s.log.push("── SHOWDOWN ──");
  const tc=(s.top||[]).filter(Boolean);const ids=ps.map(p=>p.id);const hi={},lw={};
  ids.forEach(id=>{if(s.folded[id]||s.down[id]){hi[id]={rank:-1,name:s.folded[id]?"Fold":"Bust",score:-1};lw[id]=Infinity;}
    else{const h=s.hands[id]||[];hi[id]=evalHand([...h,...tc]);lw[id]=h.length?lowPts(h):Infinity;}});
  const act=ids.filter(id=>!s.folded[id]&&!s.down[id]);const w={};ids.forEach(id=>w[id]=0);
  if(!act.length){const busted=ids.filter(id=>s.down[id]&&!s.folded[id]);if(busted.length){const sh=Math.floor(s.pot/busted.length);busted.forEach(id=>w[id]=sh);s.log.push("全員バースト→折半");}else{const sh=Math.floor(s.pot/ids.length);ids.forEach(id=>w[id]=sh);s.log.push("返還");}}
  else if(act.length===1){w[act[0]]=s.pot;s.log.push("🏆"+((ps.find(p=>p.id===act[0])||{}).name||"?")+" +"+s.pot);}
  else{const hiHalf=Math.floor(s.pot/2),loHalf=s.pot-hiHalf;
    const mH=Math.max(...act.map(id=>hi[id].score));const hiWinners=act.filter(id=>hi[id].score===mH);
    const mL=Math.min(...act.map(id=>lw[id]));const loWinners=mL===Infinity?hiWinners:act.filter(id=>lw[id]===mL);
    const hiEach=Math.floor(hiHalf/hiWinners.length),hiRem=hiHalf-hiEach*hiWinners.length;
    hiWinners.forEach((id,i)=>w[id]+=hiEach+(i===0?hiRem:0));
    const loEach=Math.floor(loHalf/loWinners.length),loRem=loHalf-loEach*loWinners.length;
    loWinners.forEach((id,i)=>w[id]+=loEach+(i===0?loRem:0));
    s.log.push("🏆Hi: "+hiWinners.map(id=>(ps.find(p=>p.id===id)||{}).name||"?").join(",")+" "+hi[hiWinners[0]].name+(hiWinners.length>1?" (÷"+hiWinners.length+")":"")+" +"+(hiWinners.length>1?hiEach+"ea":hiHalf));
    s.log.push("🏆Lo: "+loWinners.map(id=>(ps.find(p=>p.id===id)||{}).name||"?").join(",")+" "+(mL===Infinity?"—":mL+"pt")+(loWinners.length>1?" (÷"+loWinners.length+")":"")+" +"+(loWinners.length>1?loEach+"ea":loHalf));}
  s.results={hi,lw,w};return s;
}

/* ═══════ COMPONENT ═══════ */
export default function Scarney(){
  const[myId]=useState(()=>{const s=getSession();return s?s.id:uid();});
  const[scr,setScr]=useState("home");
  const[name,setName]=useState(()=>{const s=getSession();return s?s.name||"":"";});
  const[code,setCode]=useState("");
  const[ji,setJi]=useState("");
  const[room,setRS]=useState(null);
  const[err,setErr]=useState("");
  const[stack,setStack]=useState(10000);
  const[betAmt,setBetAmt]=useState(100);
  const[queueCount,setQueueCount]=useState(0);
  const[searchTime,setSearchTime]=useState(0);
  const unR=useRef(null);const logR=useRef(null);const matchRef=useRef(null);const roomRef=useRef(null);

  const isDlr=room?room.dealerId===myId:false;
  const gs=room?room.gameState:null;
  const isSD=gs?gs.phase==="showdown":false;
  const isBetting=gs&&gs.betting;
  const isMyTurn=isBetting&&gs.betting.actorId===myId;
  const myChips=(room&&room.chips&&room.chips[myId])||0;
  const showHands=gs&&gs.allInShow;
  const myH=(gs&&gs.hands&&gs.hands[myId])||[];
  const topCards=(gs?(gs.top||[]):[]).filter(Boolean);
  const liveEval=(!isSD&&myH.length>0&&topCards.length>0)?evalHand([...myH,...topCards]):null;
  const myLow=myH.length>0?lowPts(myH):0;

  useEffect(()=>{if(logR.current)logR.current.scrollTop=1e6;});
  useEffect(()=>{if(room&&room.gameState&&scr==="lobby")setScr("game");},[room,scr]);
  useEffect(()=>()=>{if(unR.current)unR.current();if(matchRef.current)clearInterval(matchRef.current);},[]);
  const sub=useCallback(c=>{if(unR.current)unR.current();unR.current=subscribeRoom(c,d=>setRS(dc(d)));},[]);
  useEffect(()=>{let x=false;(async()=>{const s=getSession();if(!s)return;const d=await getRoom(s.room);if(x)return;if(d&&d.players&&d.players.find(p=>p.id===s.id)){setCode(s.room);setRS(dc(d));setScr(d.gameState?"game":"lobby");sub(s.room);}})();return()=>{x=true;};},[sub]);
  const upd=useCallback(async(c,d,s)=>{const cp=dc(d);setRS(cp);roomRef.current=cp;if(s)setScr(s);await setRoom(c,cp);},[]);

  /* CPU auto-action */
  useEffect(()=>{roomRef.current=room;},[room]);
  useEffect(()=>{
    if(!gs||!gs.betting||!room)return;
    const aid=gs.betting.actorId;const actor=(room.players||[]).find(p=>p.id===aid);
    if(!actor||!actor.cpu)return;
    const t=setTimeout(async()=>{
      const r=roomRef.current;if(!r||!r.gameState||!r.gameState.betting)return;
      if(r.gameState.betting.actorId!==aid)return;
      const dec=cpuDecide(r.gameState,r,aid);
      const{gs:ng,room:nr}=doBetAction(r.gameState,r,r.players,aid,dec.type,dec.amount);
      nr.gameState=ng;await upd(code,nr);
    },600+Math.random()*800);
    return()=>clearTimeout(t);
  },[gs?.betting?.actorId,gs?.phase,gs?.pot]);

  const onMatchSearch=async()=>{if(!name.trim()){setErr("名前を入力");return;}setErr("");await joinQueue(myId,name.trim());setScr("matching");setSearchTime(0);
    if(matchRef.current)clearInterval(matchRef.current);
    matchRef.current=setInterval(async()=>{setSearchTime(t=>t+2);const cnt=await getQueueCount();setQueueCount(cnt);
      const res=await tryMatch(myId);if(res.matched){clearInterval(matchRef.current);matchRef.current=null;const rc=res.roomCode;
        if(res.isCreator){const d={code:rc,players:[{id:myId,name:name.trim()},res.opponent],dealerId:myId,chips:{[myId]:MATCH_STACK,[res.opponent.id]:MATCH_STACK},gameState:null,stack:MATCH_STACK};setCode(rc);saveSession(myId,name.trim(),rc);await upd(rc,d,"lobby");sub(rc);}
        else{let at=0;const ji2=setInterval(async()=>{at++;const d=await getRoom(rc);if(d&&d.players){clearInterval(ji2);if(!d.players.find(p=>p.id===myId)){d.players.push({id:myId,name:name.trim()});d.chips[myId]=MATCH_STACK;await setRoom(rc,d);}setCode(rc);saveSession(myId,name.trim(),rc);setRS(dc(d));setScr("lobby");sub(rc);}if(at>15)clearInterval(ji2);},1000);}}},2000);};
  const onCancelMatch=async()=>{if(matchRef.current){clearInterval(matchRef.current);matchRef.current=null;}await leaveQueue(myId);setScr("home");setSearchTime(0);};

  const onCreate=async()=>{if(!name.trim()){setErr("名前を入力");return;}setErr("");const c=rcode();const d={code:c,players:[{id:myId,name:name.trim()}],dealerId:myId,chips:{[myId]:stack},gameState:null,stack};setCode(c);saveSession(myId,name.trim(),c);await upd(c,d,"lobby");sub(c);};
  const onJoin=async()=>{if(!name.trim()){setErr("名前を入力");return;}if(!ji.trim()){setErr("コードを入力");return;}setErr("");const c=ji.trim().toUpperCase();const d=await getRoom(c);if(!d||!d.players){setErr("ルーム見つかりません");return;}if(d.gameState&&d.gameState.phase!=="showdown"&&!d.players.find(p=>p.id===myId)){setErr("ゲーム進行中");return;}if(d.players.length>=6&&!d.players.find(p=>p.id===myId)){setErr("満員");return;}if(!d.players.find(p=>p.id===myId)){d.players.push({id:myId,name:name.trim()});d.chips[myId]=d.stack||10000;}setCode(c);setStack(d.stack||10000);saveSession(myId,name.trim(),c);await upd(c,d,"lobby");sub(c);};
  const onStart=async()=>{if(!room||room.players.length<2)return;const d=dc(room);d.gameState=makeGame(d.players,1,0,d.chips);await upd(code,d,"game");};
  const onAdvance=async()=>{if(!room||!gs||isBetting)return;const d=dc(room);const g=doAdvancePhase(gs,room.players,d.chips);d.gameState=g;await upd(code,d);};
  const onBetAct=async(action,amount)=>{if(!room||!gs||!isBetting||gs.betting.actorId!==myId)return;const{gs:ng,room:nr}=doBetAction(gs,room,room.players,myId,action,amount);nr.gameState=ng;await upd(code,nr);};
  const onNext=async()=>{if(!room||!gs||!gs.results)return;const d=dc(room);const w=d.gameState.results.w;d.players.forEach(p=>{d.chips[p.id]=(d.chips[p.id]||0)+((w&&w[p.id])||0);});d.players.forEach(p=>{if(p.cpu&&(d.chips[p.id]||0)===0)d.chips[p.id]=d.stack||10000;});const nb=((d.gameState.btn||0)+1)%d.players.length;d.gameState=makeGame(d.players,(d.gameState.round||1)+1,nb,d.chips);await upd(code,d);};
  const onRebuy=async()=>{if(!room)return;const d=dc(room);d.chips[myId]=(d.chips[myId]||0)+(d.stack||10000);await upd(code,d);};
  const onSetStack=async v=>{setStack(v);if(room&&isDlr){const d=dc(room);d.stack=v;d.players.forEach(p=>d.chips[p.id]=v);await upd(code,d);}};
  const onLeave=async()=>{try{if(unR.current){unR.current();unR.current=null;}if(room){const d=dc(room);d.players=d.players.filter(p=>p.id!==myId);if(!d.players.length)await deleteRoom(code);else{if(d.dealerId===myId&&d.players.length)d.dealerId=d.players[0].id;await setRoom(code,d);}}clearSession();}catch(e){}setScr("home");setRS(null);setCode("");setErr("");};

  const onAddCPU=async()=>{if(!room||!isDlr||room.gameState)return;const d=dc(room);const cc=d.players.filter(p=>p.cpu).length;if(cc>=5||d.players.length>=6)return;const used=new Set(d.players.filter(p=>p.cpu).map(p=>p.name));let cn="";for(const n of CPU_NAMES)if(!used.has(n)){cn=n;break;}if(!cn)return;const id="cpu-"+uid();d.players.push({id,name:cn,cpu:true});d.chips[id]=d.stack||10000;await upd(code,d);};
  const onRemoveCPU=async()=>{if(!room||!isDlr||room.gameState)return;const d=dc(room);const last=[...d.players].reverse().find(p=>p.cpu);if(!last)return;d.players=d.players.filter(p=>p.id!==last.id);delete d.chips[last.id];await upd(code,d);};
  /* ═══════ CARD RENDER ═══════ */
  const crd=(card,o={})=>{
    const{faceDown,small,mini,discarded,glow,dim}=o;
    const w=mini?28:small?36:48,h=mini?40:small?52:70,fs=mini?7:small?9:12;
    if(faceDown)return<div style={{width:w,height:h,borderRadius:5,background:"linear-gradient(145deg,#1a472e,#0a2818)",border:"1.5px solid #2a6a3e",display:"flex",alignItems:"center",justifyContent:"center",flexShrink:0,boxShadow:"0 2px 6px rgba(0,0,0,0.4)"}}><span style={{fontSize:fs,opacity:0.2,color:"#4a9a62"}}>♠</span></div>;
    if(!card)return<div style={{width:w,height:h,borderRadius:5,border:"1.5px dashed rgba(255,255,255,0.05)",flexShrink:0}}/>;
    const rd=isRed(card);
    return<div style={{width:w,height:h,borderRadius:5,background:discarded?"#12121e":"linear-gradient(145deg,#fefef6,#eeeade)",border:glow?"2px solid #ffd700":discarded?"1.5px solid #8b2020":"1.5px solid #999",display:"flex",flexDirection:"column",justifyContent:"space-between",padding:mini?"1px 2px":small?"2px 3px":"3px 5px",color:discarded?"#444":rd?"#c0392b":"#1a1a2e",fontSize:fs,fontWeight:700,fontFamily:"Georgia,serif",position:"relative",flexShrink:0,opacity:discarded?0.35:dim?0.25:1,boxShadow:glow?"0 0 12px rgba(255,215,0,0.5)":"0 2px 6px rgba(0,0,0,0.3)",transition:"transform 0.15s"}}>
      <div>{card.rank}{card.suit}</div><div style={{textAlign:"right",transform:"rotate(180deg)"}}>{card.rank}{card.suit}</div>
      {discarded&&<div style={{position:"absolute",top:"50%",left:"50%",transform:"translate(-50%,-50%)",fontSize:mini?8:small?10:14,color:"#c0392b"}}>✕</div>}
    </div>;
  };

  const BG={minHeight:"100vh",background:"radial-gradient(ellipse at 50% 30%,#0a1a10,#050d08 60%,#020604)",color:"#e8e4d9",fontFamily:"'Segoe UI','Hiragino Sans','Noto Sans JP',sans-serif"};
  const TT={fontSize:22,fontWeight:900,textAlign:"center",background:"linear-gradient(90deg,#c9a227,#f5e07a,#c9a227)",WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent",letterSpacing:4};
  const goldBtn=(t,fn,dis,fl)=><button onClick={fn} disabled={dis} style={{padding:"10px 24px",borderRadius:8,width:fl?"100%":"auto",background:dis?"#222":"linear-gradient(145deg,#d4af37,#b8962e)",color:dis?"#555":"#0a0a0a",border:"none",cursor:dis?"default":"pointer",fontWeight:800,fontSize:14,opacity:dis?0.4:1,fontFamily:"inherit",boxShadow:dis?"none":"0 2px 8px rgba(212,175,55,0.3)",letterSpacing:1}}>{t}</button>;
  const darkBtn=(t,fn,bg)=><button onClick={fn} style={{padding:"10px 24px",borderRadius:8,background:bg||"rgba(255,255,255,0.06)",color:"#ccc",border:"1px solid rgba(255,255,255,0.08)",cursor:"pointer",fontWeight:700,fontSize:13,fontFamily:"inherit"}}>{t}</button>;

  /* ═══════ HOME ═══════ */
  if(scr==="home")return<div style={BG}><div style={{maxWidth:380,margin:"0 auto",padding:"40px 16px"}}>
    <h1 style={{...TT,fontSize:28,marginBottom:2}}>♠ SCARNEY ♣</h1>
    <p style={{textAlign:"center",color:"#4a6a4e",fontSize:11,marginBottom:24,letterSpacing:2}}>POKER LOUNGE</p>
    <div style={{fontSize:11,color:"#7a9a7e",marginBottom:4,fontWeight:600}}>PLAYER NAME</div>
    <input value={name} onChange={e=>{setName(e.target.value);setErr("");}} placeholder="名前を入力" maxLength={10} style={{width:"100%",padding:"10px 12px",borderRadius:8,border:"1px solid rgba(212,175,55,0.2)",background:"rgba(255,255,255,0.04)",color:"#e8e4d9",fontSize:15,fontFamily:"inherit",boxSizing:"border-box",outline:"none"}}/>
    <div style={{height:14}}/>
    <button onClick={onMatchSearch} style={{width:"100%",padding:"16px",borderRadius:10,background:"linear-gradient(135deg,#c0392b,#96281b)",color:"#fff",border:"none",fontWeight:900,fontSize:17,cursor:"pointer",fontFamily:"inherit",letterSpacing:2,boxShadow:"0 4px 20px rgba(192,57,43,0.4)",textTransform:"uppercase"}}>
      🔍 FIND MATCH
    </button>
    <div style={{textAlign:"center",fontSize:9,color:"#555",marginTop:4}}>Stack: {MATCH_STACK.toLocaleString()} fixed</div>
    <div style={{display:"flex",alignItems:"center",gap:10,margin:"18px 0"}}><div style={{flex:1,height:1,background:"rgba(212,175,55,0.12)"}}/><span style={{color:"#4a6a4e",fontSize:10,letterSpacing:2}}>PRIVATE</span><div style={{flex:1,height:1,background:"rgba(212,175,55,0.12)"}}/></div>
    <div style={{fontSize:10,color:"#7a9a7e",marginBottom:4,fontWeight:600}}>STACK</div>
    <div style={{display:"flex",gap:5,flexWrap:"wrap",marginBottom:12}}>
      {STACKS.map(v=><button key={v} onClick={()=>setStack(v)} style={{padding:"5px 12px",borderRadius:6,fontSize:12,fontWeight:700,fontFamily:"inherit",background:stack===v?"linear-gradient(145deg,#d4af37,#b8962e)":"rgba(255,255,255,0.04)",color:stack===v?"#0a0a0a":"#777",border:stack===v?"none":"1px solid rgba(255,255,255,0.06)",cursor:"pointer"}}>{v.toLocaleString()}</button>)}
    </div>
    {goldBtn("CREATE ROOM",onCreate,false,true)}
    <div style={{height:10}}/>
    <div style={{fontSize:10,color:"#7a9a7e",marginBottom:4,fontWeight:600}}>ROOM CODE</div>
    <input value={ji} onChange={e=>{setJi(e.target.value.toUpperCase());setErr("");}} placeholder="AB3X" maxLength={4} style={{width:"100%",padding:"10px",borderRadius:8,border:"1px solid rgba(212,175,55,0.2)",background:"rgba(255,255,255,0.04)",color:"#d4af37",fontSize:24,fontWeight:900,fontFamily:"monospace",boxSizing:"border-box",outline:"none",textAlign:"center",letterSpacing:12}}/>
    <div style={{height:6}}/>
    {darkBtn("JOIN",onJoin,"rgba(74,106,138,0.3)")}
    {err&&<div style={{marginTop:10,padding:"8px",borderRadius:6,background:"rgba(180,40,40,0.12)",border:"1px solid rgba(180,40,40,0.25)",color:"#e74c3c",fontSize:12,textAlign:"center"}}>{err}</div>}
    <div style={{marginTop:20,padding:10,borderRadius:8,background:"rgba(255,255,255,0.015)",border:"1px solid rgba(255,255,255,0.03)",fontSize:9,color:"#3a5a3e",lineHeight:1.9}}>
      <strong style={{color:"#5a7a5e"}}>📖 RULES</strong><br/>
      Bomb Pot: {ANTE} ante per player. Discard matching ranks each street.<br/>
      <span style={{color:"#c04040"}}>💀 River: 0 or 6 cards = BUST</span><br/>
      Hi (best hand) + Lo (lowest pts) split the pot.
    </div>
  </div></div>;

  /* ═══════ MATCHING ═══════ */
  if(scr==="matching")return<div style={BG}><div style={{maxWidth:380,margin:"0 auto",padding:"60px 16px",textAlign:"center"}}>
    <h1 style={TT}>♠ SCARNEY ♣</h1>
    <div style={{marginTop:50}}>
      <div style={{width:80,height:80,margin:"0 auto 20px",borderRadius:"50%",border:"3px solid #c0392b",display:"flex",alignItems:"center",justifyContent:"center",animation:"spin 2s linear infinite"}}>
        <span style={{fontSize:30}}>🔍</span>
      </div>
      <div style={{fontSize:16,fontWeight:700,color:"#d4af37",marginBottom:6,letterSpacing:1}}>SEARCHING...</div>
      <div style={{fontSize:12,color:"#888"}}>{name}</div>
      <div style={{fontSize:28,fontWeight:900,color:"#e8e4d9",fontFamily:"monospace",margin:"12px 0"}}>{Math.floor(searchTime/60)}:{String(searchTime%60).padStart(2,"0")}</div>
      <div style={{fontSize:10,color:"#555"}}>Waiting: {queueCount}</div>
    </div>
    <div style={{marginTop:30}}>{darkBtn("CANCEL",onCancelMatch,"rgba(90,51,51,0.5)")}</div>
    <style>{`@keyframes spin{from{transform:rotate(0deg)}to{transform:rotate(360deg)}}`}</style>
  </div></div>;

  /* ═══════ LOBBY ═══════ */
  if(scr==="lobby"){
    const ps=room?room.players||[]:[];const cs=room?room.stack||stack:stack;
    return<div style={BG}><div style={{maxWidth:380,margin:"0 auto",padding:"30px 16px"}}>
      <h1 style={TT}>♠ SCARNEY ♣</h1>
      <div style={{textAlign:"center",margin:"16px 0"}}>
        <div style={{fontSize:9,color:"#666",letterSpacing:2}}>ROOM CODE</div>
        <div style={{fontSize:40,fontWeight:900,letterSpacing:14,color:"#d4af37",fontFamily:"monospace",textShadow:"0 0 20px rgba(212,175,55,0.2)"}}>{code}</div>
      </div>
      <div style={{textAlign:"center",margin:"10px 0",padding:"8px",borderRadius:8,background:"rgba(212,175,55,0.06)",border:"1px solid rgba(212,175,55,0.15)"}}>
        <div style={{fontSize:11,color:"#d4af37",fontWeight:600}}>🪙 {cs.toLocaleString()}</div>
        {isDlr&&!room.gameState&&<div style={{display:"flex",gap:4,justifyContent:"center",flexWrap:"wrap",marginTop:5}}>
          {STACKS.map(v=><button key={v} onClick={()=>onSetStack(v)} style={{padding:"3px 10px",borderRadius:5,fontSize:10,fontWeight:700,fontFamily:"inherit",background:cs===v?"#d4af37":"rgba(255,255,255,0.04)",color:cs===v?"#0a0a0a":"#666",border:"none",cursor:"pointer"}}>{v.toLocaleString()}</button>)}
        </div>}
      </div>
      <div style={{background:"rgba(255,255,255,0.02)",borderRadius:10,padding:12,border:"1px solid rgba(255,255,255,0.04)",margin:"12px 0"}}>
        {ps.map((p,i)=><div key={p.id} style={{display:"flex",alignItems:"center",gap:10,padding:"8px 0",borderBottom:i<ps.length-1?"1px solid rgba(255,255,255,0.03)":"none"}}>
          <div style={{width:32,height:32,borderRadius:"50%",background:p.id===myId?"linear-gradient(135deg,#d4af37,#b8962e)":"linear-gradient(135deg,#2a4a3a,#1a3a2a)",display:"flex",alignItems:"center",justifyContent:"center",fontSize:14,fontWeight:900,color:p.id===myId?"#0a0a0a":"#6a8a6e"}}>{p.name[0]}</div>
          <div><div style={{fontSize:13,fontWeight:p.id===myId?700:400,color:p.id===myId?"#d4af37":"#ccc"}}>{p.cpu?"🤖 ":""}{p.name}</div>
            <div style={{fontSize:9,color:"#555"}}>{p.id===room.dealerId?"HOST":p.cpu?"CPU":""}</div></div>
        </div>)}
        {ps.length<2&&<div style={{fontSize:11,color:"#555",textAlign:"center",padding:"8px 0"}}>Waiting for players...</div>}
      </div>
      {isDlr&&!room.gameState&&<div style={{display:"flex",alignItems:"center",justifyContent:"center",gap:8,margin:"8px 0",padding:"10px",borderRadius:10,background:"rgba(255,255,255,0.02)",border:"1px solid rgba(255,255,255,0.04)"}}>
        <span style={{fontSize:10,color:"#7a9a7e",fontWeight:600}}>🤖 CPU</span>
        <button onClick={onRemoveCPU} disabled={!ps.some(p=>p.cpu)} style={{width:30,height:30,borderRadius:8,background:ps.some(p=>p.cpu)?"rgba(200,60,60,0.2)":"rgba(255,255,255,0.03)",color:ps.some(p=>p.cpu)?"#c04040":"#333",border:"1px solid rgba(255,255,255,0.06)",fontSize:16,fontWeight:900,cursor:ps.some(p=>p.cpu)?"pointer":"default",fontFamily:"inherit"}}>−</button>
        <span style={{fontSize:18,fontWeight:900,color:"#d4af37",minWidth:24,textAlign:"center",fontFamily:"monospace"}}>{ps.filter(p=>p.cpu).length}</span>
        <button onClick={onAddCPU} disabled={ps.filter(p=>p.cpu).length>=5||ps.length>=6} style={{width:30,height:30,borderRadius:8,background:ps.filter(p=>p.cpu).length<5&&ps.length<6?"rgba(42,122,66,0.2)":"rgba(255,255,255,0.03)",color:ps.filter(p=>p.cpu).length<5&&ps.length<6?"#2a7a42":"#333",border:"1px solid rgba(255,255,255,0.06)",fontSize:16,fontWeight:900,cursor:ps.filter(p=>p.cpu).length<5&&ps.length<6?"pointer":"default",fontFamily:"inherit"}}>+</button>
        <span style={{fontSize:9,color:"#555"}}>({ps.filter(p=>p.cpu).length}/5)</span>
      </div>}
      {isDlr?goldBtn("START GAME ▶",onStart,ps.length<2,true):<div style={{textAlign:"center",padding:12,color:"#666",fontSize:12}}>Waiting for host...</div>}
      <div style={{height:10}}/>
      <div style={{textAlign:"center"}}>{darkBtn("LEAVE",onLeave,"rgba(90,51,51,0.3)")}</div>
    </div></div>;
  }

  /* ═══════ GAME ═══════ */
  if(!gs||!room)return<div style={BG}><p style={{padding:60,textAlign:"center",color:"#555"}}>Loading...</p></div>;
  const players=room.players||[];const others=players.filter(p=>p.id!==myId);
  const myDisc=(gs.disc&&gs.disc[myId])||[];const myDn=(gs.down&&gs.down[myId])||false;const myFold=(gs.folded&&gs.folded[myId])||false;
  const canAdv=isDlr&&!isBetting&&!isSD;
  const myBetIn=isBetting?(gs.betting.bets[myId]||0):0;
  const toCall=isBetting?Math.max(0,gs.betting.currentBet-myBetIn):0;
  const minRaise=isBetting?(gs.betting.currentBet===0?100:gs.betting.currentBet+(gs.betting.minRaise||100)):100;
  const maxBet=myChips+myBetIn;
  const needRebuy=myChips===0&&gs.phase==="deal";

  return<div style={{...BG,padding:"6px 8px",display:"flex",flexDirection:"column",minHeight:"100vh"}}>
    {/* Top bar */}
    <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"4px 4px 8px"}}>
      <div style={{fontSize:12,fontWeight:900,background:"linear-gradient(90deg,#c9a227,#f5e07a)",WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent",letterSpacing:2}}>♠ SCARNEY</div>
      <div style={{display:"flex",gap:8,alignItems:"center"}}>
        <div style={{fontSize:8,color:"#555"}}>R{gs.round}・{code}</div>
        <div style={{background:myChips===0?"rgba(200,40,40,0.15)":"rgba(144,238,144,0.1)",border:myChips===0?"1px solid rgba(200,40,40,0.3)":"1px solid rgba(144,238,144,0.2)",borderRadius:8,padding:"4px 10px"}}>
          <span style={{fontSize:8,color:myChips===0?"#c04040":"#5a8a5e",fontWeight:600}}>STACK </span>
          <span style={{fontSize:14,fontWeight:900,color:myChips===0?"#e74c3c":"#90ee90",fontFamily:"Georgia"}}>{myChips.toLocaleString()}</span>
        </div>
      </div>
    </div>

    {/* ═══════ TABLE ═══════ */}
    <div style={{flex:1,display:"flex",flexDirection:"column",gap:4}}>

      {/* Opponents around table */}
      <div style={{display:"flex",justifyContent:"center",gap:6,flexWrap:"wrap",padding:"0 4px"}}>
        {others.map(p=>{
          const dn=gs.down&&gs.down[p.id];const fd=gs.folded&&gs.folded[p.id];
          const hd=(gs.hands&&gs.hands[p.id])||[];const dsc=(gs.disc&&gs.disc[p.id])||[];
          const wn=(gs.results&&gs.results.w&&gs.results.w[p.id])||0;
          const isActor=isBetting&&gs.betting.actorId===p.id;
          const pBet=isBetting?(gs.betting.bets[p.id]||0):0;
          const isBtn2=gs.btn===players.indexOf(p);
          const pChips=(room.chips&&room.chips[p.id])||0;
          const canSee=isSD||showHands;
          const pLow=hd.length>0?lowPts(hd):0;
          const pEval=canSee&&hd.length>0&&topCards.length>0?evalHand([...hd,...topCards]):null;
          return<div key={p.id} style={{background:isActor?"rgba(255,215,0,0.08)":"rgba(0,0,0,0.25)",borderRadius:10,padding:"6px 8px",border:isActor?"1.5px solid rgba(255,215,0,0.4)":fd?"1px solid rgba(100,100,100,0.2)":"1px solid rgba(255,255,255,0.05)",minWidth:100,flex:"1 1 100px",maxWidth:180,backdropFilter:"blur(4px)"}}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:3}}>
              <div style={{display:"flex",alignItems:"center",gap:4}}>
                <div style={{width:22,height:22,borderRadius:"50%",background:fd?"#333":dn?"#5a2020":"linear-gradient(135deg,#2a4a3a,#1a3a2a)",display:"flex",alignItems:"center",justifyContent:"center",fontSize:9,fontWeight:900,color:"#8aaa8e",border:isBtn2?"2px solid #d4af37":"none"}}>{p.name[0]}</div>
                <span style={{fontSize:9,fontWeight:700,color:fd?"#555":dn?"#c04040":"#ccc"}}>{p.cpu?"🤖 ":""}{p.name}{dn?"💀":fd?"✕":""}</span>
              </div>
              <span style={{fontSize:9,fontWeight:700,color:pChips===0?"#c04040":"#7aba7e"}}>{pChips.toLocaleString()}</span>
            </div>
            {pBet>0&&<div style={{fontSize:8,color:"#d4af37",textAlign:"center",marginBottom:2}}>BET {pBet.toLocaleString()}</div>}
            <div style={{display:"flex",gap:2,justifyContent:"center",flexWrap:"wrap"}}>
              {fd?<div style={{fontSize:8,color:"#444",padding:"4px 0"}}>FOLD</div>
              :canSee?hd.map((c,i)=><span key={i}>{crd(c,{mini:true,dim:dn})}</span>)
              :Array(hd.length).fill(null).map((_,i)=><span key={i}>{crd(null,{faceDown:true,mini:true})}</span>)}
              {canSee&&!fd&&dsc.map((c,i)=><span key={"d"+i}>{crd(c,{discarded:true,mini:true})}</span>)}
            </div>
            {canSee&&!fd&&!dn&&pEval&&pEval.rank>=0&&<div style={{fontSize:7,color:"#aaa",textAlign:"center",marginTop:2}}>{pEval.name}・<span style={{color:"#64b4ff"}}>{pLow}pt</span>{wn>0&&<strong style={{color:"#ffd700"}}> +{wn.toLocaleString()}</strong>}</div>}
          </div>;
        })}
      </div>

      {/* Green felt table */}
      <div style={{background:"radial-gradient(ellipse at 50% 50%,#1a5a32,#0f4025 50%,#0a3018 80%,#061a0e)",borderRadius:20,padding:"12px 10px",border:"3px solid #2a6a3e",boxShadow:"inset 0 0 30px rgba(0,0,0,0.5),0 0 20px rgba(10,48,24,0.5)",position:"relative",minHeight:140}}>

        {/* Phase indicator */}
        <div style={{display:"flex",gap:3,marginBottom:8,justifyContent:"center"}}>
          {PH_LIST.map(p=>{const on=PH_LIST.indexOf(gs.phase)>=PH_LIST.indexOf(p);return<div key={p} style={{padding:"2px 8px",borderRadius:10,fontSize:8,fontWeight:700,background:on?"rgba(212,175,55,0.2)":"rgba(0,0,0,0.2)",color:on?"#d4af37":"#2a4a3a",border:on?"1px solid rgba(212,175,55,0.3)":"1px solid rgba(0,0,0,0.2)"}}>{PH_JP[p]}</div>;})}
        </div>

        {/* POT */}
        <div style={{textAlign:"center",marginBottom:8}}>
          <span style={{background:"rgba(0,0,0,0.3)",padding:"4px 16px",borderRadius:20,fontSize:10,color:"#b8962e",fontWeight:700,letterSpacing:1}}>
            POT <span style={{fontSize:16,color:"#f0d060",fontFamily:"Georgia"}}>{gs.pot.toLocaleString()}</span>
          </span>
        </div>

        {/* Betting indicator */}
        {(isBetting||showHands&&!isSD)&&<div style={{textAlign:"center",marginBottom:6}}>
          {isBetting&&(isMyTurn?<span style={{background:"rgba(255,215,0,0.15)",padding:"3px 12px",borderRadius:10,fontSize:10,color:"#ffd700",fontWeight:700,border:"1px solid rgba(255,215,0,0.3)"}}>YOUR TURN{gs.betting.currentBet>0?" • Bet: "+gs.betting.currentBet.toLocaleString():""}</span>
          :<span style={{background:"rgba(0,0,0,0.3)",padding:"3px 12px",borderRadius:10,fontSize:10,color:"#888"}}>⏳ {(players.find(p=>p.id===gs.betting.actorId)||{}).name||"?"}</span>)}
          {showHands&&!isSD&&!isBetting&&<span style={{background:"rgba(100,180,255,0.1)",padding:"3px 12px",borderRadius:10,fontSize:10,color:"#64b4ff",fontWeight:700,border:"1px solid rgba(100,180,255,0.2)"}}>⚡ ALL-IN SHOWDOWN</span>}
        </div>}

        {/* Community cards - Top row */}
        <div style={{textAlign:"center",marginBottom:4}}>
          <div style={{fontSize:7,color:"rgba(100,180,255,0.4)",fontWeight:600,marginBottom:2,letterSpacing:1}}>COMMUNITY</div>
          <div style={{display:"flex",gap:3,justifyContent:"center"}}>{(gs.top||[]).map((c,i)=><span key={i}>{crd(c,{small:true})}</span>)}</div>
        </div>
        {/* Bottom row */}
        <div style={{textAlign:"center"}}>
          <div style={{fontSize:7,color:"rgba(255,80,80,0.4)",fontWeight:600,marginBottom:2,letterSpacing:1}}>DISCARD</div>
          <div style={{display:"flex",gap:3,justifyContent:"center"}}>{(gs.bot||[]).map((c,i)=><span key={i}>{crd(c,{small:true})}</span>)}</div>
        </div>

        {/* Dealer controls on table */}
        <div style={{display:"flex",gap:6,justifyContent:"center",marginTop:8}}>
          {canAdv&&gs.phase==="deal"&&<button onClick={onAdvance} style={{padding:"6px 20px",borderRadius:20,background:"linear-gradient(145deg,#d4af37,#b8962e)",color:"#0a0a0a",border:"none",fontWeight:800,fontSize:11,cursor:"pointer",fontFamily:"inherit",boxShadow:"0 2px 8px rgba(212,175,55,0.3)"}}>FLOP ▶</button>}
          {canAdv&&gs.phase==="flop"&&<button onClick={onAdvance} style={{padding:"6px 20px",borderRadius:20,background:"linear-gradient(145deg,#d4af37,#b8962e)",color:"#0a0a0a",border:"none",fontWeight:800,fontSize:11,cursor:"pointer",fontFamily:"inherit",boxShadow:"0 2px 8px rgba(212,175,55,0.3)"}}>TURN ▶</button>}
          {canAdv&&gs.phase==="turn"&&<button onClick={onAdvance} style={{padding:"6px 20px",borderRadius:20,background:"linear-gradient(145deg,#d4af37,#b8962e)",color:"#0a0a0a",border:"none",fontWeight:800,fontSize:11,cursor:"pointer",fontFamily:"inherit",boxShadow:"0 2px 8px rgba(212,175,55,0.3)"}}>RIVER ▶</button>}
          {isDlr&&!isSD&&!isBetting&&gs.phase==="river"&&<button onClick={onAdvance} style={{padding:"6px 20px",borderRadius:20,background:"linear-gradient(145deg,#d4af37,#b8962e)",color:"#0a0a0a",border:"none",fontWeight:800,fontSize:11,cursor:"pointer",fontFamily:"inherit",boxShadow:"0 2px 8px rgba(212,175,55,0.3)"}}>SHOWDOWN ▶</button>}
          {isDlr&&isSD&&<button onClick={onNext} style={{padding:"6px 20px",borderRadius:20,background:"linear-gradient(145deg,#d4af37,#b8962e)",color:"#0a0a0a",border:"none",fontWeight:800,fontSize:11,cursor:"pointer",fontFamily:"inherit",boxShadow:"0 2px 8px rgba(212,175,55,0.3)"}}>NEXT ROUND ▶</button>}
        </div>
      </div>

      {/* ═══════ MY SEAT ═══════ */}
      <div style={{background:myDn?"rgba(120,20,20,0.15)":myFold?"rgba(50,50,50,0.15)":"rgba(0,0,0,0.3)",borderRadius:14,padding:"8px 10px",border:isMyTurn?"2px solid rgba(255,215,0,0.5)":myDn?"1px solid rgba(120,20,20,0.3)":"1px solid rgba(255,255,255,0.05)",backdropFilter:"blur(4px)"}}>
        <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:4}}>
          <div style={{display:"flex",alignItems:"center",gap:6}}>
            <div style={{width:28,height:28,borderRadius:"50%",background:"linear-gradient(135deg,#d4af37,#b8962e)",display:"flex",alignItems:"center",justifyContent:"center",fontSize:12,fontWeight:900,color:"#0a0a0a",border:gs.btn===players.findIndex(p=>p.id===myId)?"2px solid #fff":"none"}}>{name[0]||"?"}</div>
            <div>
              <div style={{fontSize:11,fontWeight:700,color:"#d4af37"}}>{name} <span style={{fontSize:8,color:"#666"}}>({myH.length})</span>{myDn?<span style={{color:"#c04040",fontSize:9}}> 💀{gs.reason&&gs.reason[myId]}</span>:myFold?<span style={{color:"#555",fontSize:9}}> FOLD</span>:""}</div>
              {myH.length>0&&!myDn&&!myFold&&<div style={{fontSize:9,color:"#64b4ff"}}>Low: {myLow}pt{liveEval&&liveEval.rank>=0&&<span style={{marginLeft:6,color:"#aaa"}}>• {liveEval.name}</span>}</div>}
            </div>
          </div>
          {gs.btn===players.findIndex(p=>p.id===myId)&&<span style={{fontSize:8,background:"#d4af37",color:"#0a0a0a",padding:"1px 6px",borderRadius:4,fontWeight:800}}>BTN</span>}
        </div>
        <div style={{display:"flex",gap:3,justifyContent:"center",flexWrap:"wrap",minHeight:70}}>
          {myFold?<div style={{fontSize:12,color:"#444",padding:"20px 0"}}>FOLDED</div>
          :<>{myH.map((c,i)=><span key={i}>{crd(c,{glow:isSD&&!myDn})}</span>)}{myDisc.map((c,i)=><span key={"d"+i}>{crd(c,{discarded:true})}</span>)}</>}
        </div>
        {isSD&&gs.results&&!myDn&&!myFold&&<div style={{textAlign:"center",marginTop:4,padding:"4px 10px",borderRadius:8,background:((gs.results.w&&gs.results.w[myId])||0)>0?"rgba(255,215,0,0.1)":"rgba(255,255,255,0.02)",fontSize:11}}>
          🏆 <strong>{gs.results.hi&&gs.results.hi[myId]?gs.results.hi[myId].name:"?"}</strong> ・ {myLow}pt
          {((gs.results.w&&gs.results.w[myId])||0)>0&&<span style={{color:"#ffd700",fontWeight:700,marginLeft:6}}>+{(gs.results.w[myId]||0).toLocaleString()}</span>}
        </div>}
      </div>

      {/* Rebuy */}
      {needRebuy&&<div style={{textAlign:"center",padding:10,background:"rgba(200,40,40,0.08)",borderRadius:10,border:"1px solid rgba(200,40,40,0.2)"}}>
        <div style={{fontSize:12,color:"#c04040",fontWeight:700,marginBottom:6}}>💸 BUSTED</div>
        <button onClick={onRebuy} style={{padding:"8px 24px",borderRadius:8,background:"#c0392b",color:"#fff",border:"none",fontWeight:700,fontSize:13,cursor:"pointer",fontFamily:"inherit"}}>REBUY +{(room.stack||10000).toLocaleString()} 🔄</button>
      </div>}

      {/* ═══════ BETTING UI ═══════ */}
      {isMyTurn&&!myDn&&!myFold&&<div style={{background:"rgba(0,0,0,0.35)",borderRadius:12,padding:10,border:"1px solid rgba(255,215,0,0.15)"}}>
        {gs.betting.currentBet===0?<>
          <div style={{display:"flex",gap:6,marginBottom:8}}>
            <button onClick={()=>onBetAct("check")} style={{flex:1,padding:"10px",borderRadius:8,background:"linear-gradient(145deg,#2a7a42,#1a5a2e)",color:"#fff",border:"none",fontWeight:700,fontSize:14,cursor:"pointer",fontFamily:"inherit",boxShadow:"0 2px 8px rgba(42,122,66,0.3)"}}>CHECK ✓</button>
            <button onClick={()=>onBetAct("fold")} style={{padding:"10px 16px",borderRadius:8,background:"rgba(90,51,51,0.5)",color:"#aaa",border:"1px solid rgba(90,51,51,0.5)",fontWeight:700,fontSize:13,cursor:"pointer",fontFamily:"inherit"}}>FOLD</button>
          </div>
          <div style={{display:"flex",gap:3,marginBottom:6,flexWrap:"wrap",justifyContent:"center"}}>
            {[100,200,500,1000,2000].filter(v=>v<=myChips).map(v=><button key={v} onClick={()=>setBetAmt(v)} style={{padding:"4px 10px",borderRadius:6,fontSize:10,fontWeight:700,fontFamily:"inherit",background:betAmt===v?"#d4af37":"rgba(255,255,255,0.04)",color:betAmt===v?"#0a0a0a":"#888",border:"none",cursor:"pointer"}}>{v>=1000?(v/1000)+"K":v}</button>)}
            {gs.pot>0&&<button onClick={()=>setBetAmt(Math.max(Math.floor(gs.pot/2),100))} style={{padding:"4px 8px",borderRadius:6,fontSize:10,fontWeight:700,fontFamily:"inherit",background:"rgba(255,255,255,0.04)",color:"#888",border:"none",cursor:"pointer"}}>½P</button>}
            <button onClick={()=>setBetAmt(myChips)} style={{padding:"4px 8px",borderRadius:6,fontSize:10,fontWeight:700,fontFamily:"inherit",background:"rgba(200,50,50,0.2)",color:"#c04040",border:"none",cursor:"pointer"}}>ALL</button>
          </div>
          <div style={{display:"flex",gap:6}}>
            <input type="number" value={betAmt} onChange={e=>setBetAmt(Math.max(1,+e.target.value||0))} style={{flex:1,padding:"8px",borderRadius:6,border:"1px solid rgba(255,255,255,0.1)",background:"rgba(0,0,0,0.3)",color:"#e8e4d9",fontSize:15,fontFamily:"inherit",outline:"none",textAlign:"center"}}/>
            <button onClick={()=>onBetAct("bet",Math.min(betAmt,myChips))} style={{padding:"8px 22px",borderRadius:8,background:"linear-gradient(145deg,#d4af37,#b8962e)",color:"#0a0a0a",border:"none",fontWeight:800,fontSize:14,cursor:"pointer",fontFamily:"inherit"}}>BET</button>
          </div>
        </>:<>
          <div style={{display:"flex",gap:6,marginBottom:8}}>
            <button onClick={()=>onBetAct("call")} style={{flex:1,padding:"10px",borderRadius:8,background:"linear-gradient(145deg,#2a7a42,#1a5a2e)",color:"#fff",border:"none",fontWeight:700,fontSize:14,cursor:"pointer",fontFamily:"inherit",boxShadow:"0 2px 8px rgba(42,122,66,0.3)"}}>CALL {Math.min(toCall,myChips).toLocaleString()}</button>
            <button onClick={()=>onBetAct("fold")} style={{padding:"10px 16px",borderRadius:8,background:"rgba(90,51,51,0.5)",color:"#aaa",border:"1px solid rgba(90,51,51,0.5)",fontWeight:700,fontSize:13,cursor:"pointer",fontFamily:"inherit"}}>FOLD</button>
          </div>
          <div style={{display:"flex",gap:3,marginBottom:6,flexWrap:"wrap",justifyContent:"center"}}>
            <button onClick={()=>setBetAmt(minRaise)} style={{padding:"4px 8px",borderRadius:6,fontSize:10,fontWeight:700,fontFamily:"inherit",background:"rgba(255,255,255,0.04)",color:"#888",border:"none",cursor:"pointer"}}>MIN</button>
            {gs.pot>0&&<button onClick={()=>setBetAmt(Math.max(Math.floor(gs.pot/2),minRaise))} style={{padding:"4px 8px",borderRadius:6,fontSize:10,fontWeight:700,fontFamily:"inherit",background:"rgba(255,255,255,0.04)",color:"#888",border:"none",cursor:"pointer"}}>½P</button>}
            {gs.pot>0&&<button onClick={()=>setBetAmt(Math.max(gs.pot,minRaise))} style={{padding:"4px 8px",borderRadius:6,fontSize:10,fontWeight:700,fontFamily:"inherit",background:"rgba(255,255,255,0.04)",color:"#888",border:"none",cursor:"pointer"}}>POT</button>}
            <button onClick={()=>setBetAmt(maxBet)} style={{padding:"4px 8px",borderRadius:6,fontSize:10,fontWeight:700,fontFamily:"inherit",background:"rgba(200,50,50,0.2)",color:"#c04040",border:"none",cursor:"pointer"}}>ALL</button>
          </div>
          <div style={{display:"flex",gap:6}}>
            <input type="number" value={betAmt} onChange={e=>setBetAmt(Math.max(1,+e.target.value||0))} style={{flex:1,padding:"8px",borderRadius:6,border:"1px solid rgba(255,255,255,0.1)",background:"rgba(0,0,0,0.3)",color:"#e8e4d9",fontSize:15,fontFamily:"inherit",outline:"none",textAlign:"center"}}/>
            <button onClick={()=>onBetAct("raise",Math.min(Math.max(betAmt,minRaise),maxBet))} disabled={myChips<=toCall} style={{padding:"8px 22px",borderRadius:8,background:"linear-gradient(145deg,#d4af37,#b8962e)",color:"#0a0a0a",border:"none",fontWeight:800,fontSize:14,cursor:"pointer",fontFamily:"inherit",opacity:myChips<=toCall?0.3:1}}>RAISE</button>
          </div>
        </>}
      </div>}

      {/* Log */}
      <div ref={logR} style={{background:"rgba(0,0,0,0.3)",borderRadius:8,padding:5,maxHeight:80,overflowY:"auto",fontSize:8,lineHeight:1.6,color:"#4a6a4e"}}>
        {(gs.log||[]).map((l,i)=><div key={i} style={{color:l.includes("💀")?"#c04040":l.includes("🏆")?"#d4af37":l.startsWith("──")?"#8aaa8e":l.includes("🎲")?"#7aba7e":l.includes("⚡")?"#64b4ff":l.includes("💰")?"#b8962e":"#4a6a4e",fontWeight:l.includes("🏆")||l.includes("💀")?700:400}}>{l}</div>)}
      </div>
    </div>
    <div style={{textAlign:"center",padding:"6px 0"}}><button onClick={onLeave} style={{background:"none",border:"none",color:"#333",fontSize:9,cursor:"pointer"}}>EXIT</button></div>
  </div>;
}
