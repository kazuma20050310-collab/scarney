import { useState, useCallback, useEffect, useRef } from "react";
import {
  getRoom, setRoom, deleteRoom,
  subscribeRoom,
  getSession, saveSession, clearSession,
} from "./supabase";

/* ═══════════════════════════════════════════
   CONSTANTS
   ═══════════════════════════════════════════ */
const SUITS = ["♠", "♥", "♦", "♣"];
const RANKS = ["2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A"];
const RV = { 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, J: 11, Q: 12, K: 13, A: 14 };
const LP = { 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, J: 10, Q: 10, K: 10, A: 1 };
const HN = ["ハイカード", "ワンペア", "ツーペア", "スリーカード", "ストレート", "フラッシュ", "フルハウス", "フォーカード", "ストレートフラッシュ", "ロイヤルフラッシュ"];
const BETS = [10, 25, 50, 100, 200, 500];
const PH_LIST = ["deal", "flop", "turn", "river", "showdown"];
const PH_JP = { deal: "ディール", flop: "フロップ", turn: "ターン", river: "リバー", showdown: "ショーダウン" };

function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
function makeDeck() {
  const d = [];
  for (const s of SUITS) for (const r of RANKS) d.push({ rank: r, suit: s });
  return shuffle(d);
}
function isRed(c) { return c.suit === "♥" || c.suit === "♦"; }
function lowPts(h) { return h.reduce((s, c) => s + LP[c.rank], 0); }
function uid() { return Math.random().toString(36).slice(2, 10); }
function rcode() {
  const ch = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
  let r = "";
  for (let i = 0; i < 4; i++) r += ch[Math.floor(Math.random() * ch.length)];
  return r;
}
function deepCopy(obj) { return JSON.parse(JSON.stringify(obj)); }

/* ═══════════════════════════════════════════
   HAND EVAL
   ═══════════════════════════════════════════ */
function combos(arr, k) {
  if (k === 0) return [[]];
  if (arr.length < k) return [];
  const [first, ...rest] = arr;
  return [...combos(rest, k - 1).map(c => [first, ...c]), ...combos(rest, k)];
}

function eval5(cards) {
  const v = cards.map(c => RV[c.rank]).sort((a, b) => a - b);
  const fl = cards.every(c => c.suit === cards[0].suit);
  const u = [...new Set(v)].sort((a, b) => a - b);
  const isSt = u.length === 5 && (u[4] - u[0] === 4 || u.join(",") === "2,3,4,5,14");
  const isLow = u.join(",") === "2,3,4,5,14";
  const cn = {};
  v.forEach(x => (cn[x] = (cn[x] || 0) + 1));
  const g = Object.entries(cn).map(([x, c]) => ({ v: +x, c })).sort((a, b) => b.c - a.c || b.v - a.v);

  if (fl && isSt) {
    if (v.join(",") === "10,11,12,13,14") return { rank: 9, name: HN[9], score: 9e12 };
    return { rank: 8, name: HN[8], score: 8e12 + (isLow ? 5 : v[4]) };
  }
  if (g[0].c === 4) return { rank: 7, name: HN[7], score: 7e12 + g[0].v * 1e6 + (g[1] ? g[1].v : 0) };
  if (g[0].c === 3 && g.length > 1 && g[1].c === 2) return { rank: 6, name: HN[6], score: 6e12 + g[0].v * 1e6 + g[1].v };
  if (fl) return { rank: 5, name: HN[5], score: 5e12 + v[4] * 1e8 + v[3] * 1e6 + v[2] * 1e4 + v[1] * 100 + v[0] };
  if (isSt) return { rank: 4, name: HN[4], score: 4e12 + (isLow ? 5 : v[4]) };
  if (g[0].c === 3) return { rank: 3, name: HN[3], score: 3e12 + g[0].v * 1e6 };
  if (g[0].c === 2 && g.length > 1 && g[1].c === 2) {
    const hi = Math.max(g[0].v, g[1].v), lo2 = Math.min(g[0].v, g[1].v);
    return { rank: 2, name: HN[2], score: 2e12 + hi * 1e6 + lo2 * 1e4 + (g[2] ? g[2].v : 0) };
  }
  if (g[0].c === 2) return { rank: 1, name: HN[1], score: 1e12 + g[0].v * 1e6 };
  return { rank: 0, name: HN[0], score: v[4] * 1e8 + v[3] * 1e6 + v[2] * 1e4 + v[1] * 100 + v[0] };
}

function evalHand(cards) {
  if (!cards || cards.length < 5) return { rank: -1, name: "不成立", score: -1 };
  let best = null;
  for (const c of combos(cards, 5)) {
    const e = eval5(c);
    if (!best || e.score > best.score) best = e;
  }
  return best;
}

/* ═══════════════════════════════════════════
   GAME LOGIC
   ═══════════════════════════════════════════ */
function makeGame(players, ante, round) {
  const deck = makeDeck();
  const hands = {}, disc = {}, down = {}, reason = {};
  players.forEach(p => {
    hands[p.id] = deck.splice(0, 6);
    disc[p.id] = [];
    down[p.id] = false;
    reason[p.id] = "";
  });
  return {
    deck, hands, disc, down, reason,
    top: [null, null, null, null, null, null],
    bot: [null, null, null, null, null, null],
    phase: "deal", pot: ante * players.length, ante,
    round: round || 1, results: null,
    log: ["R" + (round || 1) + ": 全員" + ante + "チップ投入！"]
  };
}

function doAdvancePhase(gs, players) {
  const s = deepCopy(gs);
  const n = s.phase === "deal" ? 3 : s.phase === "flop" ? 2 : s.phase === "turn" ? 1 : 0;
  if (n === 0) return s;

  const tI = s.top.filter(Boolean).length;
  const bI = s.bot.filter(Boolean).length;
  const newRanks = new Set();

  for (let i = 0; i < n; i++) { if (s.deck.length > 0) s.top[tI + i] = s.deck.shift(); }
  for (let i = 0; i < n; i++) {
    if (s.deck.length > 0) { const c = s.deck.shift(); s.bot[bI + i] = c; newRanks.add(c.rank); }
  }

  const next = s.phase === "deal" ? "flop" : s.phase === "flop" ? "turn" : "river";
  s.log.push("── " + PH_JP[next] + " ──");
  const isRiver = next === "river";

  for (const p of players) {
    if (s.down[p.id]) continue;
    const kept = [], toss = [];
    for (const c of (s.hands[p.id] || [])) {
      if (newRanks.has(c.rank)) toss.push(c); else kept.push(c);
    }
    s.hands[p.id] = kept;
    s.disc[p.id] = [...(s.disc[p.id] || []), ...toss];

    if (toss.length > 0) s.log.push(p.name + ": " + toss.map(c => c.rank + c.suit).join(" ") + " 捨て（残" + kept.length + "枚）");
    else s.log.push(p.name + ": 捨てなし（残" + kept.length + "枚）");

    if (isRiver) {
      if (kept.length === 0) { s.down[p.id] = true; s.reason[p.id] = "ハンド0枚"; s.log.push("💀 " + p.name + " バースト（ハンド0枚）"); }
      else if (toss.length === 0) { s.down[p.id] = true; s.reason[p.id] = "捨て0枚"; s.log.push("💀 " + p.name + " バースト（捨て0枚）"); }
    }
  }
  s.phase = next;
  return s;
}

function doShowdown(gs, players) {
  const s = deepCopy(gs);
  s.phase = "showdown";
  s.log.push("── ショーダウン ──");
  const topCards = (s.top || []).filter(Boolean);
  const ids = players.map(p => p.id);
  const hi = {}, lw = {};

  ids.forEach(id => {
    if (s.down[id]) { hi[id] = { rank: -1, name: "バースト", score: -1 }; lw[id] = Infinity; }
    else {
      const hand = s.hands[id] || [];
      hi[id] = evalHand([...hand, ...topCards]);
      lw[id] = hand.length === 0 ? Infinity : lowPts(hand);
    }
  });

  const active = ids.filter(id => !s.down[id]);
  const w = {};
  ids.forEach(id => (w[id] = 0));

  if (active.length === 0) {
    const share = Math.floor(s.pot / ids.length);
    ids.forEach(id => (w[id] = share));
    s.log.push("全員バースト → 返還");
  } else if (active.length === 1) {
    w[active[0]] = s.pot;
    const nm = players.find(p => p.id === active[0]);
    s.log.push("🏆 " + (nm ? nm.name : "?") + " 生存 → " + s.pot + "チップ！");
  } else {
    const maxH = Math.max(...active.map(id => hi[id].score));
    const hW = active.find(id => hi[id].score === maxH);
    const minL = Math.min(...active.map(id => lw[id]));
    const lW = minL === Infinity ? hW : active.find(id => lw[id] === minL);
    const half = Math.floor(s.pot / 2), rem = s.pot - half * 2;
    w[hW] += half + rem;
    w[lW] += half;
    const hn = players.find(p => p.id === hW);
    const ln = players.find(p => p.id === lW);
    s.log.push("🏆 ハイ: " + (hn ? hn.name : "?") + "（" + hi[hW].name + "）→ " + (half + rem));
    s.log.push("🏆 ロー: " + (ln ? ln.name : "?") + "（" + (minL === Infinity ? "—" : minL + "pt") + "）→ " + half);
  }
  s.results = { hi, lw, w };
  return s;
}

/* ═══════════════════════════════════════════
   MAIN COMPONENT
   ═══════════════════════════════════════════ */
export default function Scarney() {
  const [myId] = useState(() => {
    const sess = getSession();
    return sess ? sess.id : uid();
  });
  const [screen, setScreen] = useState("home");
  const [name, setName] = useState(() => {
    const sess = getSession();
    return sess ? sess.name || "" : "";
  });
  const [code, setCode] = useState("");
  const [joinInput, setJoinInput] = useState("");
  const [room, setRoomState] = useState(null);
  const [err, setErr] = useState("");
  const [ante, setAnte] = useState(50);
  const unsubRef = useRef(null);
  const logRef = useRef(null);

  const isDealer = room ? room.dealerId === myId : false;
  const gs = room ? room.gameState : null;
  const isSD = gs ? gs.phase === "showdown" : false;

  useEffect(() => {
    if (logRef.current) logRef.current.scrollTop = 999999;
  });

  useEffect(() => {
    if (room && room.gameState && screen === "lobby") setScreen("game");
  }, [room, screen]);

  useEffect(() => {
    return () => { if (unsubRef.current) unsubRef.current(); };
  }, []);

  const subscribe = useCallback((roomCode) => {
    if (unsubRef.current) unsubRef.current();
    unsubRef.current = subscribeRoom(roomCode, (data) => {
      setRoomState(deepCopy(data));
    });
  }, []);

  // Restore session
  useEffect(() => {
    let cancelled = false;
    (async () => {
      const sess = getSession();
      if (!sess) return;
      const d = await getRoom(sess.room);
      if (cancelled) return;
      if (d && d.players && d.players.find(p => p.id === sess.id)) {
        setCode(sess.room);
        setRoomState(deepCopy(d));
        setScreen(d.gameState ? "game" : "lobby");
        subscribe(sess.room);
      }
    })();
    return () => { cancelled = true; };
  }, [subscribe]);

  // ─── Helper: update local + remote ───
  const updateRoom = useCallback(async (roomCode, newData, newScreen) => {
    const copy = deepCopy(newData);
    setRoomState(copy);
    if (newScreen) setScreen(newScreen);
    await setRoom(roomCode, copy);
  }, []);

  // ─── ACTIONS ───
  const onCreate = async () => {
    if (!name.trim()) { setErr("名前を入力"); return; }
    setErr("");
    const c = rcode();
    const d = { code: c, players: [{ id: myId, name: name.trim() }], dealerId: myId, chips: { [myId]: 1000 }, gameState: null, ante };
    setCode(c);
    saveSession(myId, name.trim(), c);
    await updateRoom(c, d, "lobby");
    subscribe(c);
  };

  const onJoin = async () => {
    if (!name.trim()) { setErr("名前を入力"); return; }
    if (!joinInput.trim()) { setErr("コードを入力"); return; }
    setErr("");
    const c = joinInput.trim().toUpperCase();
    const d = await getRoom(c);
    if (!d || !d.players) { setErr("ルーム見つかりません"); return; }
    if (d.gameState && d.gameState.phase !== "showdown" && !d.players.find(p => p.id === myId)) { setErr("ゲーム進行中"); return; }
    if (d.players.length >= 6 && !d.players.find(p => p.id === myId)) { setErr("満員"); return; }
    if (!d.players.find(p => p.id === myId)) {
      d.players.push({ id: myId, name: name.trim() });
      d.chips[myId] = 1000;
    }
    setCode(c);
    setAnte(d.ante || 50);
    saveSession(myId, name.trim(), c);
    await updateRoom(c, d, "lobby");
    subscribe(c);
  };

  const onStart = async () => {
    if (!room || room.players.length < 2) return;
    const d = deepCopy(room);
    const a = d.ante || ante; d.ante = a;
    d.players.forEach(p => { d.chips[p.id] = (d.chips[p.id] || 1000) - a; });
    d.gameState = makeGame(d.players, a, 1);
    await updateRoom(code, d, "game");
  };

  const onAdvance = async () => {
    if (!room || !gs) return;
    let g = doAdvancePhase(gs, room.players);
    if (g.phase === "river") {
      const act = room.players.filter(p => !g.down[p.id]);
      if (act.length <= 1) g = doShowdown(g, room.players);
    }
    const d = deepCopy(room);
    d.gameState = g;
    await updateRoom(code, d);
  };

  const onShowdownBtn = async () => {
    if (!room || !gs) return;
    const g = doShowdown(gs, room.players);
    const d = deepCopy(room);
    d.gameState = g;
    await updateRoom(code, d);
  };

  const onNextRound = async () => {
    if (!room || !gs || !gs.results) return;
    const d = deepCopy(room);
    const w = d.gameState.results.w;
    const a = d.ante || ante;
    d.players.forEach(p => { d.chips[p.id] = (d.chips[p.id] || 0) + ((w && w[p.id]) || 0) - a; });
    d.gameState = makeGame(d.players, a, (d.gameState.round || 1) + 1);
    await updateRoom(code, d);
  };

  const onSetAnte = async (v) => {
    setAnte(v);
    if (room && isDealer) {
      const d = deepCopy(room);
      d.ante = v;
      await updateRoom(code, d);
    }
  };

  const onLeave = async () => {
    try {
      if (unsubRef.current) { unsubRef.current(); unsubRef.current = null; }
      if (room) {
        const d = deepCopy(room);
        d.players = d.players.filter(p => p.id !== myId);
        if (d.players.length === 0) await deleteRoom(code);
        else {
          if (d.dealerId === myId && d.players.length > 0) d.dealerId = d.players[0].id;
          await setRoom(code, d);
        }
      }
      clearSession();
    } catch (e) {}
    setScreen("home"); setRoomState(null); setCode(""); setErr("");
  };

  /* ═══════════ RENDER HELPERS ═══════════ */
  const renderCard = (card, opts = {}) => {
    const { faceDown, small, discarded, glow, dim } = opts;
    const w = small ? 40 : 52, h = small ? 56 : 76, fs = small ? 9 : 13;

    if (faceDown) return (
      <div style={{ width: w, height: h, borderRadius: 6, background: "linear-gradient(135deg,#1a5c2e,#0d3318)", border: "2px solid #2a7a42", display: "flex", alignItems: "center", justifyContent: "center", flexShrink: 0 }}>
        <span style={{ fontSize: 14, opacity: 0.3, color: "#4a9a62" }}>🂠</span>
      </div>
    );
    if (!card) return <div style={{ width: w, height: h, borderRadius: 6, border: "2px dashed rgba(255,255,255,0.06)", flexShrink: 0 }} />;
    const rd = isRed(card);
    return (
      <div style={{
        width: w, height: h, borderRadius: 6,
        background: discarded ? "#181828" : "#fffef8",
        border: glow ? "2px solid #ffd700" : discarded ? "2px solid #c0392b" : "2px solid #bbb",
        display: "flex", flexDirection: "column", justifyContent: "space-between",
        padding: small ? "2px 3px" : "3px 5px",
        color: discarded ? "#555" : rd ? "#c0392b" : "#1a1a2e",
        fontSize: fs, fontWeight: 700, fontFamily: "Georgia,serif",
        position: "relative", flexShrink: 0,
        opacity: discarded ? 0.4 : dim ? 0.3 : 1,
        boxShadow: glow ? "0 0 8px rgba(255,215,0,0.4)" : "0 1px 3px rgba(0,0,0,0.2)"
      }}>
        <div>{card.rank}{card.suit}</div>
        <div style={{ textAlign: "right", transform: "rotate(180deg)" }}>{card.rank}{card.suit}</div>
        {discarded && <div style={{ position: "absolute", top: "50%", left: "50%", transform: "translate(-50%,-50%)", fontSize: small ? 14 : 20, color: "#c0392b" }}>✕</div>}
      </div>
    );
  };

  const btn = (text, onClick, color, dark, disabled, full) => (
    <button onClick={onClick} disabled={disabled} style={{
      padding: "10px 22px", borderRadius: 8, width: full ? "100%" : "auto",
      background: disabled ? "#333" : (color || "#444"), color: dark ? "#111" : "#fff",
      border: "none", cursor: disabled ? "default" : "pointer",
      fontWeight: 700, fontSize: 14, opacity: disabled ? 0.5 : 1,
      fontFamily: "inherit", letterSpacing: 0.5,
      transition: "all 0.15s",
    }}>{text}</button>
  );

  const ctrStyle = {
    minHeight: "100vh",
    background: "linear-gradient(160deg,#080c0a 0%,#0d1f15 40%,#080e0a 100%)",
    color: "#e8e4d9",
    fontFamily: "'Segoe UI','Hiragino Sans','Noto Sans JP',sans-serif",
    padding: 10
  };

  /* ═══════════ HOME ═══════════ */
  if (screen === "home") return (
    <div style={ctrStyle}>
      <div style={{ maxWidth: 400, margin: "0 auto", padding: "30px 16px" }}>
        <h1 style={{ fontSize: 24, fontWeight: 900, textAlign: "center", background: "linear-gradient(90deg,#d4af37,#f5e07a,#d4af37)", WebkitBackgroundClip: "text", WebkitTextFillColor: "transparent", letterSpacing: 3, margin: "0 0 4px" }}>♠ SCARNEY ♣</h1>
        <p style={{ textAlign: "center", color: "#6a8a6e", fontSize: 12, marginBottom: 20 }}>ボムポット・スカーニー</p>

        <div style={{ fontSize: 11, color: "#8aaa8e", marginBottom: 3, fontWeight: 600 }}>あなたの名前</div>
        <input value={name} onChange={e => { setName(e.target.value); setErr(""); }} placeholder="名前" maxLength={10}
          style={{ width: "100%", padding: "9px 11px", borderRadius: 8, border: "1px solid rgba(255,255,255,0.1)", background: "rgba(255,255,255,0.05)", color: "#e8e4d9", fontSize: 15, fontFamily: "inherit", boxSizing: "border-box", outline: "none" }} />
        <div style={{ height: 10 }} />

        <div style={{ fontSize: 11, color: "#8aaa8e", marginBottom: 3, fontWeight: 600 }}>ベット額</div>
        <div style={{ display: "flex", gap: 5, flexWrap: "wrap", marginBottom: 14 }}>
          {BETS.map(v => (
            <button key={v} onClick={() => setAnte(v)} style={{
              padding: "5px 12px", borderRadius: 6, fontSize: 13, fontWeight: 700, fontFamily: "inherit",
              background: ante === v ? "#d4af37" : "rgba(255,255,255,0.06)",
              color: ante === v ? "#111" : "#aaa",
              border: ante === v ? "2px solid #d4af37" : "2px solid rgba(255,255,255,0.1)",
              cursor: "pointer"
            }}>{v}</button>
          ))}
        </div>

        {btn("ルームを作成", onCreate, "#2a7a42", false, false, true)}
        <div style={{ display: "flex", alignItems: "center", gap: 10, margin: "14px 0" }}>
          <div style={{ flex: 1, height: 1, background: "rgba(255,255,255,0.08)" }} />
          <span style={{ color: "#444", fontSize: 11 }}>or</span>
          <div style={{ flex: 1, height: 1, background: "rgba(255,255,255,0.08)" }} />
        </div>

        <div style={{ fontSize: 11, color: "#8aaa8e", marginBottom: 3, fontWeight: 600 }}>ルームコード</div>
        <input value={joinInput} onChange={e => { setJoinInput(e.target.value.toUpperCase()); setErr(""); }} placeholder="AB3X" maxLength={4}
          style={{ width: "100%", padding: "9px 11px", borderRadius: 8, border: "1px solid rgba(255,255,255,0.1)", background: "rgba(255,255,255,0.05)", color: "#e8e4d9", fontSize: 22, fontWeight: 900, fontFamily: "inherit", boxSizing: "border-box", outline: "none", textAlign: "center", letterSpacing: 10 }} />
        <div style={{ height: 8 }} />
        {btn("参加する", onJoin, "#4a6a8a", false, false, true)}

        {err && <div style={{ marginTop: 10, padding: "7px 10px", borderRadius: 6, background: "rgba(180,40,40,0.1)", border: "1px solid rgba(180,40,40,0.2)", color: "#e74c3c", fontSize: 12, textAlign: "center" }}>{err}</div>}

        <div style={{ marginTop: 18, padding: 10, borderRadius: 8, background: "rgba(255,255,255,0.02)", border: "1px solid rgba(255,255,255,0.04)", fontSize: 10, color: "#5a7a5e", lineHeight: 1.8 }}>
          <strong style={{ color: "#7a9a7e" }}>📖 ルール</strong><br />
          全員同額ベット → フロップ/ターン/リバーを進行。下段と同じ数字の手札は強制ディスカード。<br />
          <span style={{ color: "#e74c3c" }}>💀 リバーで1枚も捨てない or 手札0枚 → バースト。</span><br />
          手札＋上段で最強役=ハイ、手札の点数合計最小=ロー。ポット折半。
        </div>
      </div>
    </div>
  );

  /* ═══════════ LOBBY ═══════════ */
  if (screen === "lobby") {
    const ps = room ? (room.players || []) : [];
    const ca = room ? (room.ante || ante) : ante;
    return (
      <div style={ctrStyle}>
        <div style={{ maxWidth: 400, margin: "0 auto", padding: "24px 16px" }}>
          <h1 style={{ fontSize: 24, fontWeight: 900, textAlign: "center", background: "linear-gradient(90deg,#d4af37,#f5e07a,#d4af37)", WebkitBackgroundClip: "text", WebkitTextFillColor: "transparent", letterSpacing: 3, margin: "0 0 4px" }}>♠ SCARNEY ♣</h1>

          <div style={{ textAlign: "center", margin: "12px 0" }}>
            <div style={{ fontSize: 10, color: "#777" }}>ルームコード</div>
            <div style={{ fontSize: 36, fontWeight: 900, letterSpacing: 12, color: "#d4af37", fontFamily: "monospace" }}>{code}</div>
            <div style={{ fontSize: 10, color: "#555" }}>友達にシェア！</div>
          </div>

          <div style={{ textAlign: "center", margin: "10px 0", padding: "8px 12px", borderRadius: 8, background: "rgba(212,175,55,0.08)", border: "1px solid rgba(212,175,55,0.2)" }}>
            <div style={{ fontSize: 11, color: "#d4af37", fontWeight: 600, marginBottom: 5 }}>💰 ベット: {ca}</div>
            {isDealer && <div style={{ display: "flex", gap: 4, justifyContent: "center", flexWrap: "wrap" }}>
              {BETS.map(v => (
                <button key={v} onClick={() => onSetAnte(v)} style={{
                  padding: "3px 10px", borderRadius: 5, fontSize: 11, fontWeight: 700, fontFamily: "inherit",
                  background: ca === v ? "#d4af37" : "rgba(255,255,255,0.05)",
                  color: ca === v ? "#111" : "#777",
                  border: ca === v ? "2px solid #d4af37" : "2px solid rgba(255,255,255,0.06)",
                  cursor: "pointer"
                }}>{v}</button>
              ))}
            </div>}
          </div>

          <div style={{ background: "rgba(255,255,255,0.03)", borderRadius: 10, padding: 12, border: "1px solid rgba(255,255,255,0.05)", marginBottom: 12 }}>
            <div style={{ fontSize: 12, color: "#aaa", marginBottom: 6, fontWeight: 600 }}>👥 ({ps.length}/6)</div>
            {ps.map((p, i) => (
              <div key={p.id} style={{ display: "flex", alignItems: "center", gap: 8, padding: "5px 0", borderBottom: i < ps.length - 1 ? "1px solid rgba(255,255,255,0.04)" : "none" }}>
                <span style={{ fontSize: 15 }}>{p.id === room.dealerId ? "👑" : "🎮"}</span>
                <span style={{ fontSize: 13, fontWeight: p.id === myId ? 700 : 400, color: p.id === myId ? "#d4af37" : "#ccc" }}>{p.name}{p.id === myId ? " (あなた)" : ""}</span>
              </div>
            ))}
            {ps.length < 2 && <div style={{ fontSize: 11, color: "#666", marginTop: 6, textAlign: "center" }}>あと{2 - ps.length}人で開始</div>}
          </div>

          {isDealer ? btn("ゲーム開始 ▶", onStart, "#d4af37", true, ps.length < 2, true)
            : <div style={{ textAlign: "center", padding: 10, color: "#777", fontSize: 13 }}>待機中…</div>}
          <div style={{ height: 8 }} />
          {btn("退出", onLeave, "#5a3333", false, false, true)}
        </div>
      </div>
    );
  }

  /* ═══════════ GAME ═══════════ */
  if (!gs || !room) return <div style={ctrStyle}><p style={{ padding: 40, textAlign: "center", color: "#888" }}>読み込み中...</p></div>;

  const players = room.players || [];
  const others = players.filter(p => p.id !== myId);
  const myHand = (gs.hands && gs.hands[myId]) || [];
  const myDisc = (gs.disc && gs.disc[myId]) || [];
  const myDown = (gs.down && gs.down[myId]) || false;

  return (
    <div style={ctrStyle}>
      {/* Header */}
      <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 6 }}>
        <div>
          <div style={{ fontSize: 15, fontWeight: 900, background: "linear-gradient(90deg,#d4af37,#f5e07a,#d4af37)", WebkitBackgroundClip: "text", WebkitTextFillColor: "transparent", letterSpacing: 2 }}>♠ SCARNEY ♣</div>
          <div style={{ fontSize: 9, color: "#6a8a6e" }}>R{gs.round} ・ {code} ・ ベット{gs.ante || ante}</div>
        </div>
        <div style={{ fontSize: 11, color: "#90ee90" }}>🪙 {((room.chips && room.chips[myId]) || 0) + ((gs.results && gs.results.w && gs.results.w[myId]) || 0)}</div>
      </div>

      {/* POT */}
      <div style={{ textAlign: "center", padding: "8px 0", marginBottom: 6, background: "radial-gradient(ellipse at center, rgba(212,175,55,0.1) 0%, transparent 70%)", borderRadius: 10 }}>
        <div style={{ fontSize: 9, color: "#b8962e", fontWeight: 600, letterSpacing: 1 }}>POT</div>
        <div style={{ fontSize: 28, fontWeight: 900, color: "#f0d060", fontFamily: "Georgia,serif", textShadow: "0 0 16px rgba(212,175,55,0.25)" }}>{gs.pot}</div>
      </div>

      {/* Phase bar */}
      <div style={{ display: "flex", gap: 2, marginBottom: 7 }}>
        {PH_LIST.map(p => {
          const on = PH_LIST.indexOf(gs.phase) >= PH_LIST.indexOf(p);
          return <div key={p} style={{ flex: 1, textAlign: "center" }}>
            <div style={{ height: 3, borderRadius: 2, marginBottom: 1, background: on ? "#d4af37" : "rgba(255,255,255,0.04)" }} />
            <div style={{ fontSize: 7, color: on ? "#d4af37" : "#333", fontWeight: 600 }}>{PH_JP[p]}</div>
          </div>;
        })}
      </div>

      {/* Other players */}
      <div style={{ display: "flex", gap: 5, marginBottom: 7, flexWrap: "wrap" }}>
        {others.map(p => {
          const dn = gs.down && gs.down[p.id];
          const hd = (gs.hands && gs.hands[p.id]) || [];
          const dc = (gs.disc && gs.disc[p.id]) || [];
          const wn = (gs.results && gs.results.w && gs.results.w[p.id]) || 0;
          const hiR = gs.results && gs.results.hi && gs.results.hi[p.id];
          return (
            <div key={p.id} style={{ flex: 1, minWidth: 120, background: dn ? "rgba(180,40,40,0.06)" : "rgba(255,255,255,0.02)", borderRadius: 8, padding: "5px 6px", border: dn ? "1px solid rgba(180,40,40,0.15)" : "1px solid rgba(255,255,255,0.04)" }}>
              <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 3 }}>
                <span style={{ fontSize: 10, fontWeight: 700 }}>{p.id === room.dealerId ? "👑" : "🎮"}{p.name}{dn ? "💀" : ""}</span>
                <span style={{ fontSize: 8, color: "#90ee90" }}>🪙{(room.chips && room.chips[p.id]) || 0}</span>
              </div>
              <div style={{ display: "flex", gap: 2, flexWrap: "wrap" }}>
                {isSD ? hd.map((c, i) => <span key={i}>{renderCard(c, { small: true, dim: dn })}</span>) : Array(hd.length).fill(null).map((_, i) => <span key={i}>{renderCard(null, { faceDown: true, small: true, dim: dn })}</span>)}
                {isSD && dc.map((c, i) => <span key={"d" + i}>{renderCard(c, { discarded: true, small: true })}</span>)}
              </div>
              {isSD && hiR && !dn && <div style={{ marginTop: 2, fontSize: 8, color: "#bbb" }}>{hiR.name}{wn > 0 && <strong style={{ color: "#ffd700", marginLeft: 3 }}>+{wn}</strong>}</div>}
              {dn && <div style={{ fontSize: 8, color: "#e74c3c", marginTop: 2 }}>💀{(gs.reason && gs.reason[p.id]) || ""}</div>}
            </div>
          );
        })}
      </div>

      {/* Board */}
      <div style={{ background: "linear-gradient(135deg,#1a4a2e,#0f3520,#1a4a2e)", borderRadius: 12, padding: 10, marginBottom: 7, border: "2px solid #2a6a42", boxShadow: "inset 0 2px 12px rgba(0,0,0,0.4)" }}>
        <div style={{ fontSize: 9, color: "rgba(100,180,255,0.6)", fontWeight: 600, marginBottom: 3 }}>⬆ 上段（役に使用）</div>
        <div style={{ display: "flex", gap: 3, flexWrap: "wrap", marginBottom: 6 }}>
          {(gs.top || []).map((c, i) => <span key={"t" + i}>{renderCard(c)}</span>)}
        </div>
        <div style={{ height: 1, background: "rgba(255,255,255,0.06)", marginBottom: 6 }} />
        <div style={{ fontSize: 9, color: "rgba(255,80,80,0.6)", fontWeight: 600, marginBottom: 3 }}>⬇ 下段（ディスカード判定）</div>
        <div style={{ display: "flex", gap: 3, flexWrap: "wrap" }}>
          {(gs.bot || []).map((c, i) => <span key={"b" + i}>{renderCard(c)}</span>)}
        </div>
      </div>

      {/* My hand */}
      <div style={{ background: myDown ? "rgba(180,40,40,0.06)" : "rgba(255,255,255,0.03)", borderRadius: 10, padding: 10, marginBottom: 7, border: myDown ? "1px solid rgba(180,40,40,0.2)" : "1px solid rgba(212,175,55,0.18)" }}>
        <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 4 }}>
          <span style={{ fontSize: 12, fontWeight: 700 }}>🃏 あなた（{myHand.length}枚）{myDown && <span style={{ color: "#e74c3c", fontSize: 10, marginLeft: 3 }}>💀{(gs.reason && gs.reason[myId]) || ""}</span>}</span>
          {myHand.length > 0 && !myDown && <span style={{ fontSize: 10, color: "#999" }}>Low: {lowPts(myHand)}pt</span>}
        </div>
        <div style={{ display: "flex", gap: 4, flexWrap: "wrap" }}>
          {myHand.map((c, i) => <span key={i}>{renderCard(c, { glow: isSD && !myDown })}</span>)}
          {myDisc.map((c, i) => <span key={"d" + i}>{renderCard(c, { discarded: true })}</span>)}
        </div>
        {isSD && gs.results && !myDown && (
          <div style={{ marginTop: 6, padding: "4px 8px", borderRadius: 6, fontSize: 11, background: ((gs.results.w && gs.results.w[myId]) || 0) > 0 ? "rgba(255,215,0,0.1)" : "rgba(255,255,255,0.02)" }}>
            🏆 <strong>{gs.results.hi && gs.results.hi[myId] ? gs.results.hi[myId].name : "?"}</strong> ・ Low: <strong>{gs.results.lw && gs.results.lw[myId] === Infinity ? "—" : ((gs.results.lw && gs.results.lw[myId]) || "?") + "pt"}</strong>
            {((gs.results.w && gs.results.w[myId]) || 0) > 0 && <span style={{ color: "#ffd700", marginLeft: 6, fontWeight: 700 }}>+{gs.results.w[myId]}!</span>}
          </div>
        )}
      </div>

      {/* Actions */}
      <div style={{ display: "flex", gap: 8, justifyContent: "center", marginBottom: 8, flexWrap: "wrap" }}>
        {isDealer && !isSD && gs.phase === "deal" && btn("フロップ ▶", onAdvance, "#d4af37", true)}
        {isDealer && !isSD && gs.phase === "flop" && btn("ターン ▶", onAdvance, "#d4af37", true)}
        {isDealer && !isSD && gs.phase === "turn" && btn("リバー ▶", onAdvance, "#d4af37", true)}
        {isDealer && !isSD && gs.phase === "river" && btn("ショーダウン ▶", onShowdownBtn, "#c0392b")}
        {isDealer && isSD && btn("次のラウンド ▶", onNextRound, "#d4af37", true)}
        {!isDealer && !isSD && <div style={{ padding: 8, color: "#777", fontSize: 12 }}>👑 {(players.find(p => p.id === (room.dealerId || "")) || {}).name || "?"} を待っています…</div>}
        {!isDealer && isSD && <div style={{ padding: 8, color: "#777", fontSize: 12 }}>次のラウンド待ち…</div>}
      </div>

      {/* Log */}
      <div ref={logRef} style={{ background: "rgba(0,0,0,0.25)", borderRadius: 8, padding: 7, maxHeight: 130, overflowY: "auto", fontSize: 9, lineHeight: 1.7, border: "1px solid rgba(255,255,255,0.03)", color: "#7a9a7e", marginBottom: 6 }}>
        {(gs.log || []).map((l, i) => (
          <div key={i} style={{ color: l.includes("💀") ? "#e74c3c" : l.includes("🏆") ? "#ffd700" : l.startsWith("──") ? "#d4af37" : "#7a9a7e", fontWeight: (l.startsWith("──") || l.includes("🏆") || l.includes("💀")) ? 700 : 400 }}>{l}</div>
        ))}
      </div>

      <div style={{ textAlign: "center" }}>
        <button onClick={onLeave} style={{ background: "none", border: "none", color: "#553", fontSize: 10, cursor: "pointer", textDecoration: "underline" }}>退出</button>
      </div>
    </div>
  );
}
