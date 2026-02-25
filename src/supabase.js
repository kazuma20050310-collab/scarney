import { createClient } from '@supabase/supabase-js'

const url = import.meta.env.VITE_SUPABASE_URL || ''
const key = import.meta.env.VITE_SUPABASE_ANON_KEY || ''

export const supabase = createClient(url, key)

/* ═══════ ROOMS ═══════ */
export async function getRoom(code) {
  try {
    const { data, error } = await supabase.from('rooms').select('data').eq('code', code).single()
    if (error || !data) return null
    return data.data
  } catch (e) { return null }
}

export async function setRoom(code, roomData) {
  try {
    const { error } = await supabase.from('rooms').upsert({ code, data: roomData }, { onConflict: 'code' })
    return !error
  } catch (e) { return false }
}

export async function deleteRoom(code) {
  try { await supabase.from('rooms').delete().eq('code', code) } catch (e) {}
}

export function subscribeRoom(code, callback) {
  const interval = setInterval(async () => {
    const data = await getRoom(code)
    if (data) callback(data)
  }, 1500)
  let channel = null
  try {
    channel = supabase.channel('room-' + code)
      .on('postgres_changes', { event: '*', schema: 'public', table: 'rooms', filter: 'code=eq.' + code },
        (payload) => { if (payload.new && payload.new.data) callback(payload.new.data) })
      .subscribe()
  } catch (e) {}
  return () => { clearInterval(interval); if (channel) try { supabase.removeChannel(channel) } catch (e) {} }
}

/* ═══════ MATCHMAKING ═══════ */

// Clean up old entries (older than 5 minutes)
async function cleanQueue() {
  try {
    const cutoff = new Date(Date.now() - 5 * 60 * 1000).toISOString()
    await supabase.from('matchmaking_queue').delete().lt('created_at', cutoff)
  } catch (e) {}
}

// Join the matchmaking queue
export async function joinQueue(playerId, playerName) {
  await cleanQueue()
  // Remove any existing entries for this player
  await supabase.from('matchmaking_queue').delete().eq('player_id', playerId)
  // Insert new entry
  const { error } = await supabase.from('matchmaking_queue').insert({
    player_id: playerId,
    player_name: playerName,
    room_code: null
  })
  return !error
}

// Check for a waiting opponent and match
export async function tryMatch(myId) {
  // First check if I've been matched by someone else
  const { data: myEntry } = await supabase
    .from('matchmaking_queue')
    .select('*')
    .eq('player_id', myId)
    .single()

  if (myEntry && myEntry.room_code) {
    // I've been matched! Return the room code
    return { matched: true, roomCode: myEntry.room_code, isCreator: false }
  }

  // Look for another waiting player
  const { data: waiting } = await supabase
    .from('matchmaking_queue')
    .select('*')
    .is('room_code', null)
    .neq('player_id', myId)
    .order('created_at', { ascending: true })
    .limit(1)

  if (waiting && waiting.length > 0) {
    const opponent = waiting[0]
    // Generate room code
    const ch = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    let rc = ""
    for (let i = 0; i < 4; i++) rc += ch[0 | Math.random() * ch.length]

    // Update both entries with room code
    await supabase.from('matchmaking_queue').update({ room_code: rc }).eq('player_id', myId)
    await supabase.from('matchmaking_queue').update({ room_code: rc }).eq('player_id', opponent.player_id)

    return {
      matched: true,
      roomCode: rc,
      isCreator: true,
      opponent: { id: opponent.player_id, name: opponent.player_name }
    }
  }

  return { matched: false }
}

// Leave the queue
export async function leaveQueue(playerId) {
  try {
    await supabase.from('matchmaking_queue').delete().eq('player_id', playerId)
  } catch (e) {}
}

// Get queue count
export async function getQueueCount() {
  try {
    const { count } = await supabase
      .from('matchmaking_queue')
      .select('*', { count: 'exact', head: true })
      .is('room_code', null)
    return count || 0
  } catch (e) { return 0 }
}

/* ═══════ SESSION ═══════ */
export function getSession() { try { const r = localStorage.getItem('scarney-session'); return r ? JSON.parse(r) : null } catch (e) { return null } }
export function saveSession(id, name, room) { try { localStorage.setItem('scarney-session', JSON.stringify({ id, name, room })) } catch (e) {} }
export function clearSession() { try { localStorage.removeItem('scarney-session') } catch (e) {} }
