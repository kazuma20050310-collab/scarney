import { createClient } from '@supabase/supabase-js'

const url = import.meta.env.VITE_SUPABASE_URL || ''
const key = import.meta.env.VITE_SUPABASE_ANON_KEY || ''

export const supabase = createClient(url, key)

// ─── Room CRUD ───

export async function getRoom(code) {
  try {
    const { data, error } = await supabase
      .from('rooms')
      .select('data')
      .eq('code', code)
      .single()
    if (error || !data) return null
    return data.data
  } catch (e) {
    console.error('getRoom error:', e)
    return null
  }
}

export async function setRoom(code, roomData) {
  try {
    const { error } = await supabase
      .from('rooms')
      .upsert({ code, data: roomData }, { onConflict: 'code' })
    if (error) console.error('setRoom error:', error)
    return !error
  } catch (e) {
    console.error('setRoom exception:', e)
    return false
  }
}

export async function deleteRoom(code) {
  try {
    await supabase.from('rooms').delete().eq('code', code)
  } catch (e) {}
}

// ─── Realtime subscription + Polling fallback ───

export function subscribeRoom(code, callback) {
  // Polling fallback (every 1.5s)
  const interval = setInterval(async () => {
    const data = await getRoom(code)
    if (data) callback(data)
  }, 1500)

  // Also try Realtime
  let channel = null
  try {
    channel = supabase
      .channel('room-' + code)
      .on(
        'postgres_changes',
        {
          event: '*',
          schema: 'public',
          table: 'rooms',
          filter: 'code=eq.' + code,
        },
        (payload) => {
          if (payload.new && payload.new.data) {
            callback(payload.new.data)
          }
        }
      )
      .subscribe()
  } catch (e) {
    console.error('Realtime subscribe error:', e)
  }

  // Return cleanup function
  return () => {
    clearInterval(interval)
    if (channel) {
      try { supabase.removeChannel(channel) } catch (e) {}
    }
  }
}

// ─── Session (localStorage) ───

export function getSession() {
  try {
    const raw = localStorage.getItem('scarney-session')
    return raw ? JSON.parse(raw) : null
  } catch (e) { return null }
}

export function saveSession(id, name, room) {
  try {
    localStorage.setItem('scarney-session', JSON.stringify({ id, name, room }))
  } catch (e) {}
}

export function clearSession() {
  try { localStorage.removeItem('scarney-session') } catch (e) {}
}
