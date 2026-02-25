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

/* ═══════ HAND EVAL ═══════ */
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

/* ═══════ GAME LOGIC ═══════ */
function aliveIds(gs,ps){return ps.filter(p=>!gs.folded[p.id]&&!gs.down[p.id]).map(p=>p.id);}
function findFirstActor(ps,btnIdx,gs){const n=ps.length;for(let i=1;i<=n;i++){const p=ps[(btnIdx+i)%n];if(!gs.folded[p.id]&&!gs.down[p.id])return p.id;}return null;}
function findNextActor(ps,curId,gs){const ids=ps.map(p=>p.id);const ci=ids.indexOf(curId);const n=ids.length;for(let i=1;i<n;i++){const id=ids[(ci+i)%n];if(gs.folded[id]||gs.down[id])continue;if(!gs.betting.acted[id]||(gs.betting.bets[id]||0)<gs.betting.currentBet)return id;}return null;}
function allAliveAllIn(gs,ps,chips){const alive=aliveIds(gs,ps);if(alive.length<=1)return true;return alive.every(id=>(chips[id]||0)===0);}
function startBetting(gs,ps,chips){const alive=aliveIds(gs,ps);if(alive.length<=1)return null;if(allAliveAllIn(gs,ps,chips))return null;const fid=findFirstActor(ps,gs.btn,gs);if(!fid)return null;return{currentBet:0,bets:{},acted:{},actorId:fid,minRaise:10};}

function makeGame(ps,round,btn,chips){
  const deck=makeDeck();
  const hands={},disc={},down={},reason={},folded={};
  let pot=0;const log=[];
  ps.forEach(p=>{hands[p.id]=deck.splice(0,6);disc[p.id]=[];down[p.id]=false;reason[p.id]="";folded[p.id]=false;
    const ante=Math.min(ANTE,chips[p.id]||0);chips[p.id]=(chips[p.id]||0)-ante;pot+=ante;});
  log.push("R"+(round||1)+": ディール完了 — BTN: "+ps[btn||0].name);
  log.push("💰 ボムポット: 全員 "+ANTE+" アンティ → POT "+pot);
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
    s.log.push(p.name+": "+(toss.length?toss.map(c=>c.rank+c.suit).join(" ")+" 捨て":"捨てなし")+"（残"+kept.length+"枚）");}
  if(next==="river"){for(const p of ps){if(s.folded[p.id]||s.down[p.id])continue;const hl=(s.hands[p.id]||[]).length;
    if(hl===0){s.down[p.id]=true;s.reason[p.id]="0枚";s.log.push("💀 "+p.name+" バースト（0枚）");}
    else if(hl===6){s.down[p.id]=true;s.reason[p.id]="6枚";s.log.push("💀 "+p.name+" バースト（6枚）");}}}
  s.phase=next;return s;
}

function doAdvancePhase(gs,ps,chips){
  let s=openCards(gs,ps);const alive=aliveIds(s,ps);
  if(alive.length<=1)return doShowdown(s,ps);
  const bet=startBetting(s,ps,chips);
  if(bet){s.betting=bet;s.log.push("🎲 ベッティング開始 → "+((ps.find(p=>p.id===bet.actorId)||{}).name||"?"));return s;}
  if(s.phase==="river"){s.log.push("⚡ 全員オールイン → ショーダウン");return doShowdown(s,ps);}
  s.allInShow=true;s.log.push("⚡ 全員オールイン → ハンド公開");return s;
}

function doBetAction(gs,room,ps,pid,action,amount){
  const s=dc(gs),r=dc(room);const pn=(ps.find(p=>p.id===pid)||{}).name||"?";const chips=r.chips;
  if(action==="check"){s.betting.acted[pid]=true;s.log.push(pn+": チェック ✓");}
  else if(action==="fold"){s.folded[pid]=true;s.log.push(pn+": フォールド ✕");}
  else if(action==="bet"){const amt=Math.min(amount,chips[pid]||0);s.betting.bets[pid]=amt;s.betting.currentBet=amt;s.betting.minRaise=amt;aliveIds(s,ps).forEach(id=>{s.betting.acted[id]=false;});s.betting.acted[pid]=true;chips[pid]-=amt;s.pot+=amt;s.log.push(pn+": ベット "+amt+(chips[pid]===0?" (All-in)":""));}
  else if(action==="call"){const owed=Math.min(s.betting.currentBet-(s.betting.bets[pid]||0),chips[pid]||0);s.betting.bets[pid]=(s.betting.bets[pid]||0)+owed;s.betting.acted[pid]=true;chips[pid]-=owed;s.pot+=owed;s.log.push(pn+": コール "+owed+(chips[pid]===0?" (All-in)":""));}
  else if(action==="raise"){const already=s.betting.bets[pid]||0;const total=Math.min(amount,already+(chips[pid]||0));const pay=total-already;s.betting.minRaise=Math.max(total-s.betting.currentBet,s.betting.minRaise);s.betting.bets[pid]=total;s.betting.currentBet=total;aliveIds(s,ps).forEach(id=>{s.betting.acted[id]=false;});s.betting.acted[pid]=true;chips[pid]-=pay;s.pot+=pay;s.log.push(pn+": レイズ → "+total+(chips[pid]===0?" (All-in)":""));}
  const alive=aliveIds(s,ps);
  if(alive.length<=1){s.betting=null;return{gs:doShowdown(s,ps),room:r};}
  if(allAliveAllIn(s,ps,chips)){s.betting=null;s.allInShow=true;s.log.push("⚡ 全員オールイン → ハンド公開");return{gs:s,room:r};}
  const ni=findNextActor(ps,pid,s);
  if(ni){s.betting.actorId=ni;return{gs:s,room:r};}
  s.betting=null;s.log.push("ベッティング終了");
  if(s.phase==="river"){return{gs:doShowdown(s,ps),room:r};}
  const ng=doAdvancePhase(s,ps,chips);return{gs:ng,room:r};
}

function doShowdown(gs,ps){
  const s=dc(gs);s.phase="showdown";s.betting=null;s.log.push("── ショーダウン ──");
  const tc=(s.top||[]).filter(Boolean);const ids=ps.map(p=>p.id);const hi={},lw={};
  ids.forEach(id=>{if(s.folded[id]||s.down[id]){hi[id]={rank:-1,name:s.folded[id]?"フォールド":"バースト",score:-1};lw[id]=Infinity;}
    else{const h=s.hands[id]||[];hi[id]=evalHand([...h,...tc]);lw[id]=h.length?lowPts(h):Infinity;}});
  const act=ids.filter(id=>!s.folded[id]&&!s.down[id]);const w={};ids.forEach(id=>w[id]=0);
  if(!act.length){const busted=ids.filter(id=>s.down[id]&&!s.folded[id]);if(busted.length){const sh=Math.floor(s.pot/busted.length);busted.forEach(id=>w[id]=sh);s.log.push("全員バースト → バースト者で折半");}else{const sh=Math.floor(s.pot/ids.length);ids.forEach(id=>w[id]=sh);s.log.push("全員アウト → 返還");}}
  else if(act.length===1){w[act[0]]=s.pot;s.log.push("🏆 "+((ps.find(p=>p.id===act[0])||{}).name||"?")+" → "+s.pot+"チップ！");}
  else{const mH=Math.max(...act.map(id=>hi[id].score));const hW=act.find(id=>hi[id].score===mH);
    const mL=Math.min(...act.map(id=>lw[id]));const lW=mL===Infinity?hW:act.find(id=>lw[id]===mL);
    const half=Math.floor(s.pot/2),rem=s.pot-half*2;w[hW]+=half+rem;w[lW]+=half;
    s.log.push("🏆 ハイ: "+((ps.find(p=>p.id===hW)||{}).name||"?")+"（"+hi[hW].name+"）→ "+(half+rem));
    s.log.push("🏆 ロー: "+((ps.find(p=>p.id===lW)||{}).name||"?")+"（"+(mL===Infinity?"—":mL+"pt")+"）→ "+half);}
  s.results={hi,lw,w};return s;
}

/* ═══════ MAIN COMPONENT ═══════ */
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
  const unR=useRef(null);const logR=useRef(null);const matchRef=useRef(null);

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
  const upd=useCallback(async(c,d,s)=>{const cp=dc(d);setRS(cp);if(s)setScr(s);await setRoom(c,cp);},[]);

  /* ═══════ MATCHMAKING ═══════ */
  const onMatchSearch=async()=>{
    if(!name.trim()){setErr("名前を入力");return;}setErr("");
    const ok=await joinQueue(myId,name.trim());
    if(!ok){setErr("マッチング登録失敗");return;}
    setScr("matching");setSearchTime(0);
    // Poll for match every 2 seconds
    if(matchRef.current)clearInterval(matchRef.current);
    matchRef.current=setInterval(async()=>{
      setSearchTime(t=>t+2);
      const cnt=await getQueueCount();setQueueCount(cnt);
      const res=await tryMatch(myId);
      if(res.matched){
        clearInterval(matchRef.current);matchRef.current=null;
        const rc=res.roomCode;
        if(res.isCreator){
          // I found the match, create the room
          const d={code:rc,players:[{id:myId,name:name.trim()},res.opponent],dealerId:myId,
            chips:{[myId]:MATCH_STACK,[res.opponent.id]:MATCH_STACK},gameState:null,stack:MATCH_STACK};
          setCode(rc);saveSession(myId,name.trim(),rc);await upd(rc,d,"lobby");sub(rc);
        }else{
          // Other player created the room, just join
          // Wait a moment for room to be created
          let attempts=0;
          const joinInterval=setInterval(async()=>{
            attempts++;
            const d=await getRoom(rc);
            if(d&&d.players){
              clearInterval(joinInterval);
              if(!d.players.find(p=>p.id===myId)){
                d.players.push({id:myId,name:name.trim()});
                d.chips[myId]=MATCH_STACK;
                await setRoom(rc,d);
              }
              setCode(rc);saveSession(myId,name.trim(),rc);setRS(dc(d));setScr("lobby");sub(rc);
            }
            if(attempts>15)clearInterval(joinInterval);
          },1000);
        }
      }
    },2000);
  };

  const onCancelMatch=async()=>{
    if(matchRef.current){clearInterval(matchRef.current);matchRef.current=null;}
    await leaveQueue(myId);
    setScr("home");setSearchTime(0);
  };

  /* ═══════ ROOM ACTIONS ═══════ */
  const onCreate=async()=>{
    if(!name.trim()){setErr("名前を入力");return;}setErr("");
    const c=rcode();
    const d={code:c,players:[{id:myId,name:name.trim()}],dealerId:myId,chips:{[myId]:stack},gameState:null,stack};
    setCode(c);saveSession(myId,name.trim(),c);await upd(c,d,"lobby");sub(c);
  };
  const onJoin=async()=>{
    if(!name.trim()){setErr("名前を入力");return;}if(!ji.trim()){setErr("コードを入力");return;}setErr("");
    const c=ji.trim().toUpperCase();const d=await getRoom(c);
    if(!d||!d.players){setErr("ルーム見つかりません");return;}
    if(d.gameState&&d.gameState.phase!=="showdown"&&!d.players.find(p=>p.id===myId)){setErr("ゲーム進行中");return;}
    if(d.players.length>=6&&!d.players.find(p=>p.id===myId)){setErr("満員");return;}
    if(!d.players.find(p=>p.id===myId)){d.players.push({id:myId,name:name.trim()});d.chips[myId]=d.stack||10000;}
    setCode(c);setStack(d.stack||10000);saveSession(myId,name.trim(),c);await upd(c,d,"lobby");sub(c);
  };
  const onStart=async()=>{
    if(!room||room.players.length<2)return;
    const d=dc(room);d.gameState=makeGame(d.players,1,0,d.chips);await upd(code,d,"game");
  };
  const onAdvance=async()=>{
    if(!room||!gs||isBetting)return;
    const d=dc(room);const g=doAdvancePhase(gs,room.players,d.chips);d.gameState=g;await upd(code,d);
  };
  const onBetAct=async(action,amount)=>{
    if(!room||!gs||!isBetting||gs.betting.actorId!==myId)return;
    const{gs:ng,room:nr}=doBetAction(gs,room,room.players,myId,action,amount);nr.gameState=ng;await upd(code,nr);
  };
  const onNext=async()=>{
    if(!room||!gs||!gs.results)return;
    const d=dc(room);const w=d.gameState.results.w;
    d.players.forEach(p=>{d.chips[p.id]=(d.chips[p.id]||0)+((w&&w[p.id])||0);});
    const nb=((d.gameState.btn||0)+1)%d.players.length;
    d.gameState=makeGame(d.players,(d.gameState.round||1)+1,nb,d.chips);await upd(code,d);
  };
  const onRebuy=async()=>{if(!room)return;const d=dc(room);d.chips[myId]=(d.chips[myId]||0)+(d.stack||10000);await upd(code,d);};
  const onSetStack=async v=>{setStack(v);if(room&&isDlr){const d=dc(room);d.stack=v;d.players.forEach(p=>d.chips[p.id]=v);await upd(code,d);}};
  const onLeave=async()=>{
    try{if(unR.current){unR.current();unR.current=null;}
    if(room){const d=dc(room);d.players=d.players.filter(p=>p.id!==myId);if(!d.players.length)await deleteRoom(code);else{if(d.dealerId===myId&&d.players.length)d.dealerId=d.players[0].id;await setRoom(code,d);}}
    clearSession();}catch(e){}setScr("home");setRS(null);setCode("");setErr("");
  };

  /* ═══════ RENDER ═══════ */
  const crd=(card,o={})=>{
    const{faceDown,small,discarded,glow,dim}=o;
    const w=small?38:50,h=small?54:74,fs=small?9:13;
    if(faceDown)return<div style={{width:w,height:h,borderRadius:6,background:"linear-gradient(135deg,#1a5c2e,#0d3318)",border:"2px solid #2a7a42",display:"flex",alignItems:"center",justifyContent:"center",flexShrink:0}}><span style={{fontSize:12,opacity:0.3,color:"#4a9a62"}}>🂠</span></div>;
    if(!card)return<div style={{width:w,height:h,borderRadius:6,border:"2px dashed rgba(255,255,255,0.06)",flexShrink:0}}/>;
    const rd=isRed(card);
    return<div style={{width:w,height:h,borderRadius:6,background:discarded?"#181828":"#fffef8",border:glow?"2px solid #ffd700":discarded?"2px solid #c0392b":"2px solid #bbb",display:"flex",flexDirection:"column",justifyContent:"space-between",padding:small?"2px 3px":"3px 5px",color:discarded?"#555":rd?"#c0392b":"#1a1a2e",fontSize:fs,fontWeight:700,fontFamily:"Georgia,serif",position:"relative",flexShrink:0,opacity:discarded?0.4:dim?0.3:1,boxShadow:glow?"0 0 8px rgba(255,215,0,0.4)":"0 1px 3px rgba(0,0,0,0.2)"}}>
      <div>{card.rank}{card.suit}</div><div style={{textAlign:"right",transform:"rotate(180deg)"}}>{card.rank}{card.suit}</div>
      {discarded&&<div style={{position:"absolute",top:"50%",left:"50%",transform:"translate(-50%,-50%)",fontSize:small?12:18,color:"#c0392b"}}>✕</div>}
    </div>;
  };
  const abtn=(t,fn,bg,dk,dis,fl)=><button onClick={fn} disabled={dis} style={{padding:"10px 20px",borderRadius:8,width:fl?"100%":"auto",background:dis?"#333":bg||"#444",color:dk?"#111":"#fff",border:"none",cursor:dis?"default":"pointer",fontWeight:700,fontSize:14,opacity:dis?0.5:1,fontFamily:"inherit"}}>{t}</button>;
  const CS={minHeight:"100vh",background:"linear-gradient(160deg,#080c0a,#0d1f15,#080e0a)",color:"#e8e4d9",fontFamily:"'Segoe UI','Hiragino Sans','Noto Sans JP',sans-serif",padding:10};
  const TT={fontSize:24,fontWeight:900,textAlign:"center",background:"linear-gradient(90deg,#d4af37,#f5e07a,#d4af37)",WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent",letterSpacing:3,margin:"0 0 4px"};

  /* ═══════ HOME ═══════ */
  if(scr==="home")return<div style={CS}><div style={{maxWidth:400,margin:"0 auto",padding:"30px 16px"}}>
    <h1 style={TT}>♠ SCARNEY ♣</h1>
    <p style={{textAlign:"center",color:"#6a8a6e",fontSize:12,marginBottom:20}}>スカーニーポーカー</p>
    <div style={{fontSize:11,color:"#8aaa8e",marginBottom:3,fontWeight:600}}>あなたの名前</div>
    <input value={name} onChange={e=>{setName(e.target.value);setErr("");}} placeholder="名前" maxLength={10} style={{width:"100%",padding:"9px 11px",borderRadius:8,border:"1px solid rgba(255,255,255,0.1)",background:"rgba(255,255,255,0.05)",color:"#e8e4d9",fontSize:15,fontFamily:"inherit",boxSizing:"border-box",outline:"none"}}/>
    <div style={{height:12}}/>

    {/* MATCHMAKING BUTTON */}
    <button onClick={onMatchSearch} style={{width:"100%",padding:"14px 20px",borderRadius:10,background:"linear-gradient(135deg,#e74c3c,#c0392b)",color:"#fff",border:"none",fontWeight:900,fontSize:16,cursor:"pointer",fontFamily:"inherit",letterSpacing:1,boxShadow:"0 4px 15px rgba(231,76,60,0.3)"}}>
      🔍 マッチを探す
    </button>
    <div style={{textAlign:"center",fontSize:9,color:"#666",marginTop:4}}>スタック: {MATCH_STACK.toLocaleString()} 固定</div>

    <div style={{display:"flex",alignItems:"center",gap:10,margin:"16px 0"}}><div style={{flex:1,height:1,background:"rgba(255,255,255,0.08)"}}/><span style={{color:"#444",fontSize:11}}>フレンド対戦</span><div style={{flex:1,height:1,background:"rgba(255,255,255,0.08)"}}/></div>

    <div style={{fontSize:11,color:"#8aaa8e",marginBottom:3,fontWeight:600}}>スタック</div>
    <div style={{display:"flex",gap:5,flexWrap:"wrap",marginBottom:10}}>
      {STACKS.map(v=><button key={v} onClick={()=>setStack(v)} style={{padding:"5px 12px",borderRadius:6,fontSize:13,fontWeight:700,fontFamily:"inherit",background:stack===v?"#d4af37":"rgba(255,255,255,0.06)",color:stack===v?"#111":"#aaa",border:stack===v?"2px solid #d4af37":"2px solid rgba(255,255,255,0.1)",cursor:"pointer"}}>{v.toLocaleString()}</button>)}
    </div>
    {abtn("ルームを作成",onCreate,"#2a7a42",false,false,true)}
    <div style={{height:8}}/>
    <div style={{fontSize:11,color:"#8aaa8e",marginBottom:3,fontWeight:600}}>ルームコード</div>
    <input value={ji} onChange={e=>{setJi(e.target.value.toUpperCase());setErr("");}} placeholder="AB3X" maxLength={4} style={{width:"100%",padding:"9px 11px",borderRadius:8,border:"1px solid rgba(255,255,255,0.1)",background:"rgba(255,255,255,0.05)",color:"#e8e4d9",fontSize:22,fontWeight:900,fontFamily:"inherit",boxSizing:"border-box",outline:"none",textAlign:"center",letterSpacing:10}}/>
    <div style={{height:6}}/>
    {abtn("参加する",onJoin,"#4a6a8a",false,false,true)}
    {err&&<div style={{marginTop:10,padding:"7px 10px",borderRadius:6,background:"rgba(180,40,40,0.1)",border:"1px solid rgba(180,40,40,0.2)",color:"#e74c3c",fontSize:12,textAlign:"center"}}>{err}</div>}
    <div style={{marginTop:18,padding:10,borderRadius:8,background:"rgba(255,255,255,0.02)",border:"1px solid rgba(255,255,255,0.04)",fontSize:10,color:"#5a7a5e",lineHeight:1.8}}>
      <strong style={{color:"#7a9a7e"}}>📖 ルール</strong><br/>
      ボムポット: ディール時に全員{ANTE}アンティ。<br/>
      各ストリートで下段と同じ数字の手札を強制ディスカード。<br/>
      <span style={{color:"#e74c3c"}}>💀 リバー時点で手札 0枚 or 6枚 → バースト。</span><br/>
      フロップ/ターン/リバーでベッティング。ハイ＋ローでポット折半。
    </div>
  </div></div>;

  /* ═══════ MATCHING ═══════ */
  if(scr==="matching")return<div style={CS}><div style={{maxWidth:400,margin:"0 auto",padding:"60px 16px",textAlign:"center"}}>
    <h1 style={TT}>♠ SCARNEY ♣</h1>
    <div style={{marginTop:40,marginBottom:30}}>
      <div style={{fontSize:40,marginBottom:16,animation:"pulse 1.5s ease-in-out infinite"}}>🔍</div>
      <div style={{fontSize:18,fontWeight:700,color:"#d4af37",marginBottom:8}}>対戦相手を探しています…</div>
      <div style={{fontSize:13,color:"#999",marginBottom:4}}>{name} として検索中</div>
      <div style={{fontSize:22,fontWeight:900,color:"#e8e4d9",fontFamily:"monospace"}}>{Math.floor(searchTime/60)}:{String(searchTime%60).padStart(2,"0")}</div>
      <div style={{fontSize:11,color:"#666",marginTop:8}}>待機中のプレイヤー: {queueCount}人</div>
    </div>
    <button onClick={onCancelMatch} style={{padding:"12px 40px",borderRadius:8,background:"#5a3333",color:"#fff",border:"none",fontWeight:700,fontSize:14,cursor:"pointer",fontFamily:"inherit"}}>キャンセル</button>
    <style>{`@keyframes pulse{0%,100%{transform:scale(1)}50%{transform:scale(1.15)}}`}</style>
  </div></div>;

  /* ═══════ LOBBY ═══════ */
  if(scr==="lobby"){
    const ps=room?room.players||[]:[];const cs=room?room.stack||stack:stack;
    return<div style={CS}><div style={{maxWidth:400,margin:"0 auto",padding:"24px 16px"}}>
      <h1 style={TT}>♠ SCARNEY ♣</h1>
      <div style={{textAlign:"center",margin:"12px 0"}}>
        <div style={{fontSize:10,color:"#777"}}>ルームコード</div>
        <div style={{fontSize:36,fontWeight:900,letterSpacing:12,color:"#d4af37",fontFamily:"monospace"}}>{code}</div>
        <div style={{fontSize:10,color:"#555"}}>友達にシェア！</div>
      </div>
      <div style={{textAlign:"center",margin:"10px 0",padding:"8px 12px",borderRadius:8,background:"rgba(212,175,55,0.08)",border:"1px solid rgba(212,175,55,0.2)"}}>
        <div style={{fontSize:11,color:"#d4af37",fontWeight:600,marginBottom:5}}>🪙 スタック: {cs.toLocaleString()}</div>
        {isDlr&&!room.gameState&&<div style={{display:"flex",gap:4,justifyContent:"center",flexWrap:"wrap"}}>
          {STACKS.map(v=><button key={v} onClick={()=>onSetStack(v)} style={{padding:"3px 10px",borderRadius:5,fontSize:11,fontWeight:700,fontFamily:"inherit",background:cs===v?"#d4af37":"rgba(255,255,255,0.05)",color:cs===v?"#111":"#777",border:cs===v?"2px solid #d4af37":"2px solid rgba(255,255,255,0.06)",cursor:"pointer"}}>{v.toLocaleString()}</button>)}
        </div>}
      </div>
      <div style={{background:"rgba(255,255,255,0.03)",borderRadius:10,padding:12,border:"1px solid rgba(255,255,255,0.05)",marginBottom:12}}>
        <div style={{fontSize:12,color:"#aaa",marginBottom:6,fontWeight:600}}>👥 ({ps.length}/6)</div>
        {ps.map((p,i)=><div key={p.id} style={{display:"flex",alignItems:"center",gap:8,padding:"5px 0",borderBottom:i<ps.length-1?"1px solid rgba(255,255,255,0.04)":"none"}}>
          <span style={{fontSize:15}}>{p.id===room.dealerId?"👑":"🎮"}</span>
          <span style={{fontSize:13,fontWeight:p.id===myId?700:400,color:p.id===myId?"#d4af37":"#ccc"}}>{p.name}{p.id===myId?" (あなた)":""}</span>
        </div>)}
        {ps.length<2&&<div style={{fontSize:11,color:"#666",marginTop:6,textAlign:"center"}}>あと{2-ps.length}人で開始</div>}
      </div>
      {isDlr?abtn("ゲーム開始 ▶",onStart,"#d4af37",true,ps.length<2,true):<div style={{textAlign:"center",padding:10,color:"#777",fontSize:13}}>待機中…</div>}
      <div style={{height:8}}/>
      {abtn("退出",onLeave,"#5a3333",false,false,true)}
    </div></div>;
  }

  /* ═══════ GAME ═══════ */
  if(!gs||!room)return<div style={CS}><p style={{padding:40,textAlign:"center",color:"#888"}}>読み込み中...</p></div>;
  const players=room.players||[];const others=players.filter(p=>p.id!==myId);
  const myDisc=(gs.disc&&gs.disc[myId])||[];const myDn=(gs.down&&gs.down[myId])||false;const myFold=(gs.folded&&gs.folded[myId])||false;
  const canAdv=isDlr&&!isBetting&&!isSD;
  const actorName=isBetting?(players.find(p=>p.id===gs.betting.actorId)||{}).name||"?":"";
  const myBetIn=isBetting?(gs.betting.bets[myId]||0):0;
  const toCall=isBetting?Math.max(0,gs.betting.currentBet-myBetIn):0;
  const minRaise=isBetting?(gs.betting.currentBet===0?100:gs.betting.currentBet+(gs.betting.minRaise||100)):100;
  const maxBet=myChips+myBetIn;
  const needRebuy=myChips===0&&gs.phase==="deal";

  return<div style={CS}>
    <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:6}}>
      <div>
        <div style={{fontSize:14,fontWeight:900,background:"linear-gradient(90deg,#d4af37,#f5e07a,#d4af37)",WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent",letterSpacing:2}}>♠ SCARNEY ♣</div>
        <div style={{fontSize:9,color:"#6a8a6e"}}>R{gs.round} ・ {code} ・ BTN: {(players[gs.btn]||{}).name||"?"}</div>
      </div>
      <div style={{background:myChips===0?"linear-gradient(135deg,rgba(231,76,60,0.2),rgba(231,76,60,0.05))":"linear-gradient(135deg,rgba(144,238,144,0.15),rgba(144,238,144,0.05))",border:myChips===0?"1px solid rgba(231,76,60,0.4)":"1px solid rgba(144,238,144,0.3)",borderRadius:10,padding:"6px 14px",textAlign:"center"}}>
        <div style={{fontSize:8,color:myChips===0?"#e74c3c":"#6aaa6e",fontWeight:600,letterSpacing:1}}>MY STACK</div>
        <div style={{fontSize:22,fontWeight:900,color:myChips===0?"#e74c3c":"#90ee90",fontFamily:"Georgia,serif"}}>{myChips.toLocaleString()}</div>
      </div>
    </div>
    <div style={{textAlign:"center",padding:"6px 0",marginBottom:5,background:"radial-gradient(ellipse at center,rgba(212,175,55,0.1) 0%,transparent 70%)",borderRadius:10}}>
      <div style={{fontSize:9,color:"#b8962e",fontWeight:600,letterSpacing:1}}>POT</div>
      <div style={{fontSize:26,fontWeight:900,color:"#f0d060",fontFamily:"Georgia,serif",textShadow:"0 0 16px rgba(212,175,55,0.25)"}}>{gs.pot.toLocaleString()}</div>
    </div>
    <div style={{display:"flex",gap:2,marginBottom:6}}>
      {PH_LIST.map(p=>{const on=PH_LIST.indexOf(gs.phase)>=PH_LIST.indexOf(p);return<div key={p} style={{flex:1,textAlign:"center"}}>
        <div style={{height:3,borderRadius:2,marginBottom:1,background:on?"#d4af37":"rgba(255,255,255,0.04)"}}/>
        <div style={{fontSize:7,color:on?"#d4af37":"#333",fontWeight:600}}>{PH_JP[p]}</div>
      </div>;})}
    </div>
    {isBetting&&<div style={{textAlign:"center",padding:"5px 8px",marginBottom:5,borderRadius:8,background:isMyTurn?"rgba(255,215,0,0.1)":"rgba(255,255,255,0.03)",border:isMyTurn?"1px solid rgba(255,215,0,0.3)":"1px solid rgba(255,255,255,0.05)",fontSize:11}}>
      {isMyTurn?<span style={{color:"#ffd700",fontWeight:700}}>🎲 あなたのターン！</span>:<span style={{color:"#999"}}>⏳ {actorName} のアクション待ち…</span>}
      {gs.betting.currentBet>0&&<span style={{color:"#d4af37",marginLeft:8,fontSize:10}}>現在ベット: {gs.betting.currentBet.toLocaleString()}</span>}
    </div>}
    {showHands&&!isSD&&<div style={{textAlign:"center",padding:"5px 8px",marginBottom:5,borderRadius:8,background:"rgba(100,180,255,0.08)",border:"1px solid rgba(100,180,255,0.2)",fontSize:11,color:"#64b4ff",fontWeight:700}}>⚡ 全員オールイン — ハンド公開中</div>}

    {/* Others */}
    <div style={{display:"flex",gap:4,marginBottom:6,flexWrap:"wrap"}}>
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
        return<div key={p.id} style={{flex:1,minWidth:110,background:fd?"rgba(100,100,100,0.06)":dn?"rgba(180,40,40,0.06)":isActor?"rgba(255,215,0,0.05)":"rgba(255,255,255,0.02)",borderRadius:8,padding:"4px 5px",border:isActor?"1px solid rgba(255,215,0,0.3)":dn?"1px solid rgba(180,40,40,0.15)":"1px solid rgba(255,255,255,0.04)"}}>
          <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:2}}>
            <span style={{fontSize:9,fontWeight:700}}>{isBtn2?"🔘":""}{p.name}{dn?"💀":fd?"✕":""}</span>
            <span style={{fontSize:10,fontWeight:700,color:pChips===0?"#e74c3c":"#90ee90"}}>🪙{pChips.toLocaleString()}</span>
          </div>
          {pBet>0&&<div style={{fontSize:8,color:"#d4af37",marginBottom:2}}>ベット: {pBet.toLocaleString()}</div>}
          <div style={{display:"flex",gap:2,flexWrap:"wrap"}}>
            {fd?<div style={{fontSize:9,color:"#666",padding:"8px 0"}}>フォールド</div>
            :canSee?hd.map((c,i)=><span key={i}>{crd(c,{small:true,dim:dn})}</span>)
            :Array(hd.length).fill(null).map((_,i)=><span key={i}>{crd(null,{faceDown:true,small:true,dim:dn})}</span>)}
            {canSee&&!fd&&dsc.map((c,i)=><span key={"d"+i}>{crd(c,{discarded:true,small:true})}</span>)}
          </div>
          {canSee&&!fd&&!dn&&pEval&&pEval.rank>=0&&<div style={{marginTop:2,fontSize:8,color:"#bbb"}}>{pEval.name} ・ <span style={{color:"#64b4ff"}}>{pLow}pt</span>{wn>0&&<strong style={{color:"#ffd700",marginLeft:3}}>+{wn.toLocaleString()}</strong>}</div>}
          {canSee&&!fd&&!dn&&(!pEval||pEval.rank<0)&&hd.length>0&&<div style={{marginTop:2,fontSize:8,color:"#bbb"}}><span style={{color:"#64b4ff"}}>{pLow}pt</span>{wn>0&&<strong style={{color:"#ffd700",marginLeft:3}}>+{wn.toLocaleString()}</strong>}</div>}
          {dn&&<div style={{fontSize:8,color:"#e74c3c",marginTop:1}}>💀{(gs.reason&&gs.reason[p.id])||""}</div>}
        </div>;
      })}
    </div>

    {/* Board */}
    <div style={{background:"linear-gradient(135deg,#1a4a2e,#0f3520,#1a4a2e)",borderRadius:12,padding:8,marginBottom:6,border:"2px solid #2a6a42",boxShadow:"inset 0 2px 12px rgba(0,0,0,0.4)"}}>
      <div style={{fontSize:9,color:"rgba(100,180,255,0.6)",fontWeight:600,marginBottom:2}}>⬆ 上段（役に使用）</div>
      <div style={{display:"flex",gap:3,flexWrap:"wrap",marginBottom:5}}>{(gs.top||[]).map((c,i)=><span key={i}>{crd(c)}</span>)}</div>
      <div style={{height:1,background:"rgba(255,255,255,0.06)",marginBottom:5}}/>
      <div style={{fontSize:9,color:"rgba(255,80,80,0.6)",fontWeight:600,marginBottom:2}}>⬇ 下段（ディスカード判定）</div>
      <div style={{display:"flex",gap:3,flexWrap:"wrap"}}>{(gs.bot||[]).map((c,i)=><span key={i}>{crd(c)}</span>)}</div>
    </div>

    {/* My hand */}
    <div style={{background:myDn?"rgba(180,40,40,0.06)":myFold?"rgba(100,100,100,0.06)":"rgba(255,255,255,0.03)",borderRadius:10,padding:8,marginBottom:6,border:myDn?"1px solid rgba(180,40,40,0.2)":isMyTurn?"2px solid rgba(255,215,0,0.4)":"1px solid rgba(212,175,55,0.18)"}}>
      <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:3}}>
        <span style={{fontSize:11,fontWeight:700}}>🃏 あなた（{myH.length}枚）{gs.btn===players.findIndex(p=>p.id===myId)?" 🔘BTN":""}{myDn?<span style={{color:"#e74c3c",fontSize:10,marginLeft:3}}>💀{(gs.reason&&gs.reason[myId])||""}</span>:myFold?<span style={{color:"#666",fontSize:10,marginLeft:3}}>フォールド</span>:""}</span>
        {myH.length>0&&!myDn&&!myFold&&<span style={{fontSize:10,color:"#64b4ff",fontWeight:700}}>Low: {myLow}pt</span>}
      </div>
      {isBetting&&(gs.betting.bets[myId]||0)>0&&<div style={{fontSize:9,color:"#d4af37",marginBottom:3}}>ベット中: {(gs.betting.bets[myId]||0).toLocaleString()}</div>}
      <div style={{display:"flex",gap:3,flexWrap:"wrap"}}>
        {myFold?<div style={{fontSize:11,color:"#666",padding:"10px 0"}}>フォールド済み</div>
        :<>{myH.map((c,i)=><span key={i}>{crd(c,{glow:isSD&&!myDn})}</span>)}{myDisc.map((c,i)=><span key={"d"+i}>{crd(c,{discarded:true})}</span>)}</>}
      </div>
      {liveEval&&liveEval.rank>=0&&!myDn&&!myFold&&<div style={{marginTop:5,padding:"4px 10px",borderRadius:8,background:"linear-gradient(90deg,rgba(100,180,255,0.08),rgba(100,180,255,0.02))",border:"1px solid rgba(100,180,255,0.15)",fontSize:11}}>
        🃏 現在の役: <strong style={{color:"#64b4ff"}}>{liveEval.name}</strong>
      </div>}
      {isSD&&gs.results&&!myDn&&!myFold&&<div style={{marginTop:4,padding:"3px 8px",borderRadius:6,fontSize:11,background:((gs.results.w&&gs.results.w[myId])||0)>0?"rgba(255,215,0,0.1)":"rgba(255,255,255,0.02)"}}>
        🏆 <strong>{gs.results.hi&&gs.results.hi[myId]?gs.results.hi[myId].name:"?"}</strong> ・ Low: <strong>{myLow}pt</strong>
        {((gs.results.w&&gs.results.w[myId])||0)>0&&<span style={{color:"#ffd700",marginLeft:6,fontWeight:700}}>+{(gs.results.w[myId]||0).toLocaleString()}!</span>}
      </div>}
    </div>

    {/* Betting UI */}
    {isMyTurn&&!myDn&&!myFold&&<div style={{background:"rgba(255,215,0,0.05)",border:"1px solid rgba(255,215,0,0.2)",borderRadius:10,padding:10,marginBottom:6}}>
      {gs.betting.currentBet===0?<>
        <div style={{display:"flex",gap:6,marginBottom:8}}>
          <button onClick={()=>onBetAct("check")} style={{flex:1,padding:"10px",borderRadius:8,background:"#2a7a42",color:"#fff",border:"none",fontWeight:700,fontSize:14,cursor:"pointer",fontFamily:"inherit"}}>チェック ✓</button>
          <button onClick={()=>onBetAct("fold")} style={{padding:"10px 16px",borderRadius:8,background:"#5a3333",color:"#fff",border:"none",fontWeight:700,fontSize:13,cursor:"pointer",fontFamily:"inherit"}}>フォールド</button>
        </div>
        <div style={{fontSize:10,color:"#aaa",marginBottom:4}}>ベット額:</div>
        <div style={{display:"flex",gap:4,marginBottom:6,flexWrap:"wrap"}}>
          {[100,200,500,1000,2000].filter(v=>v<=myChips).map(v=><button key={v} onClick={()=>setBetAmt(v)} style={{padding:"4px 10px",borderRadius:6,fontSize:11,fontWeight:700,fontFamily:"inherit",background:betAmt===v?"#d4af37":"rgba(255,255,255,0.06)",color:betAmt===v?"#111":"#aaa",border:"1px solid rgba(255,255,255,0.1)",cursor:"pointer"}}>{v.toLocaleString()}</button>)}
          {gs.pot>0&&<button onClick={()=>setBetAmt(Math.max(Math.floor(gs.pot/2),100))} style={{padding:"4px 10px",borderRadius:6,fontSize:11,fontWeight:700,fontFamily:"inherit",background:"rgba(255,255,255,0.06)",color:"#aaa",border:"1px solid rgba(255,255,255,0.1)",cursor:"pointer"}}>½Pot</button>}
          <button onClick={()=>setBetAmt(myChips)} style={{padding:"4px 10px",borderRadius:6,fontSize:11,fontWeight:700,fontFamily:"inherit",background:"rgba(200,50,50,0.2)",color:"#e74c3c",border:"1px solid rgba(200,50,50,0.3)",cursor:"pointer"}}>All-in</button>
        </div>
        <div style={{display:"flex",gap:6}}>
          <input type="number" value={betAmt} onChange={e=>setBetAmt(Math.max(1,+e.target.value||0))} style={{flex:1,padding:"8px",borderRadius:6,border:"1px solid rgba(255,255,255,0.15)",background:"rgba(255,255,255,0.05)",color:"#e8e4d9",fontSize:15,fontFamily:"inherit",outline:"none",textAlign:"center"}}/>
          <button onClick={()=>onBetAct("bet",Math.min(betAmt,myChips))} disabled={betAmt<=0} style={{padding:"8px 20px",borderRadius:8,background:"#d4af37",color:"#111",border:"none",fontWeight:700,fontSize:14,cursor:"pointer",fontFamily:"inherit"}}>ベット</button>
        </div>
      </>:<>
        <div style={{display:"flex",gap:6,marginBottom:8}}>
          <button onClick={()=>onBetAct("call")} style={{flex:1,padding:"10px",borderRadius:8,background:"#2a7a42",color:"#fff",border:"none",fontWeight:700,fontSize:14,cursor:"pointer",fontFamily:"inherit"}}>コール ({Math.min(toCall,myChips).toLocaleString()})</button>
          <button onClick={()=>onBetAct("fold")} style={{padding:"10px 16px",borderRadius:8,background:"#5a3333",color:"#fff",border:"none",fontWeight:700,fontSize:13,cursor:"pointer",fontFamily:"inherit"}}>フォールド</button>
        </div>
        <div style={{fontSize:10,color:"#aaa",marginBottom:4}}>レイズ額（トータル）:</div>
        <div style={{display:"flex",gap:4,marginBottom:6,flexWrap:"wrap"}}>
          <button onClick={()=>setBetAmt(minRaise)} style={{padding:"4px 10px",borderRadius:6,fontSize:11,fontWeight:700,fontFamily:"inherit",background:"rgba(255,255,255,0.06)",color:"#aaa",border:"1px solid rgba(255,255,255,0.1)",cursor:"pointer"}}>Min({minRaise.toLocaleString()})</button>
          {gs.pot>0&&<button onClick={()=>setBetAmt(Math.max(Math.floor(gs.pot/2),minRaise))} style={{padding:"4px 10px",borderRadius:6,fontSize:11,fontWeight:700,fontFamily:"inherit",background:"rgba(255,255,255,0.06)",color:"#aaa",border:"1px solid rgba(255,255,255,0.1)",cursor:"pointer"}}>½Pot</button>}
          {gs.pot>0&&<button onClick={()=>setBetAmt(Math.max(gs.pot,minRaise))} style={{padding:"4px 10px",borderRadius:6,fontSize:11,fontWeight:700,fontFamily:"inherit",background:"rgba(255,255,255,0.06)",color:"#aaa",border:"1px solid rgba(255,255,255,0.1)",cursor:"pointer"}}>Pot</button>}
          <button onClick={()=>setBetAmt(maxBet)} style={{padding:"4px 10px",borderRadius:6,fontSize:11,fontWeight:700,fontFamily:"inherit",background:"rgba(200,50,50,0.2)",color:"#e74c3c",border:"1px solid rgba(200,50,50,0.3)",cursor:"pointer"}}>All-in</button>
        </div>
        <div style={{display:"flex",gap:6}}>
          <input type="number" value={betAmt} onChange={e=>setBetAmt(Math.max(1,+e.target.value||0))} style={{flex:1,padding:"8px",borderRadius:6,border:"1px solid rgba(255,255,255,0.15)",background:"rgba(255,255,255,0.05)",color:"#e8e4d9",fontSize:15,fontFamily:"inherit",outline:"none",textAlign:"center"}}/>
          <button onClick={()=>onBetAct("raise",Math.min(Math.max(betAmt,minRaise),maxBet))} disabled={myChips<=toCall} style={{padding:"8px 20px",borderRadius:8,background:"#d4af37",color:"#111",border:"none",fontWeight:700,fontSize:14,cursor:"pointer",fontFamily:"inherit",opacity:myChips<=toCall?0.4:1}}>レイズ</button>
        </div>
      </>}
    </div>}

    {needRebuy&&<div style={{background:"rgba(231,76,60,0.08)",border:"1px solid rgba(231,76,60,0.25)",borderRadius:10,padding:12,marginBottom:6,textAlign:"center"}}>
      <div style={{fontSize:13,color:"#e74c3c",fontWeight:700,marginBottom:6}}>💸 スタックがなくなりました</div>
      <button onClick={onRebuy} style={{padding:"10px 30px",borderRadius:8,background:"#e74c3c",color:"#fff",border:"none",fontWeight:700,fontSize:14,cursor:"pointer",fontFamily:"inherit"}}>リバイ (+{(room.stack||10000).toLocaleString()}) 🔄</button>
    </div>}

    <div style={{display:"flex",gap:8,justifyContent:"center",marginBottom:6,flexWrap:"wrap"}}>
      {canAdv&&gs.phase==="deal"&&abtn("フロップ ▶",onAdvance,"#d4af37",true)}
      {canAdv&&gs.phase==="flop"&&abtn("ターン ▶",onAdvance,"#d4af37",true)}
      {canAdv&&gs.phase==="turn"&&abtn("リバー ▶",onAdvance,"#d4af37",true)}
      {isDlr&&isSD&&abtn("次のラウンド ▶",onNext,"#d4af37",true)}
      {!isDlr&&!isBetting&&!isSD&&gs.phase==="deal"&&<div style={{padding:6,color:"#777",fontSize:11}}>👑 ディーラーがフロップへ…</div>}
      {!isDlr&&!isBetting&&!isSD&&gs.phase!=="deal"&&gs.phase!=="showdown"&&<div style={{padding:6,color:"#777",fontSize:11}}>👑 ディーラーが次のストリートへ…</div>}
      {!isDlr&&isSD&&<div style={{padding:6,color:"#777",fontSize:11}}>次のラウンド待ち…</div>}
    </div>

    <div ref={logR} style={{background:"rgba(0,0,0,0.25)",borderRadius:8,padding:6,maxHeight:120,overflowY:"auto",fontSize:9,lineHeight:1.7,border:"1px solid rgba(255,255,255,0.03)",color:"#7a9a7e",marginBottom:5}}>
      {(gs.log||[]).map((l,i)=><div key={i} style={{color:l.includes("💀")?"#e74c3c":l.includes("🏆")?"#ffd700":l.startsWith("──")?"#d4af37":l.includes("🎲")?"#90ee90":l.includes("⚡")?"#64b4ff":l.includes("💰")?"#d4af37":l.includes("フォールド")?"#888":"#7a9a7e",fontWeight:l.startsWith("──")||l.includes("🏆")||l.includes("💀")||l.includes("🎲")||l.includes("⚡")||l.includes("💰")?700:400}}>{l}</div>)}
    </div>
    <div style={{textAlign:"center"}}><button onClick={onLeave} style={{background:"none",border:"none",color:"#553",fontSize:10,cursor:"pointer",textDecoration:"underline"}}>退出</button></div>
  </div>;
}
