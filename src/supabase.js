import { createClient } from '@supabase/supabase-js'

const url = import.meta.env.VITE_SUPABASE_URL || ''
const key = import.meta.env.VITE_SUPABASE_ANON_KEY || ''

export const supabase = createClient(url, key)

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

export function getSession() { try { const r = localStorage.getItem('scarney-session'); return r ? JSON.parse(r) : null } catch (e) { return null } }
export function saveSession(id, name, room) { try { localStorage.setItem('scarney-session', JSON.stringify({ id, name, room })) } catch (e) {} }
export function clearSession() { try { localStorage.removeItem('scarney-session') } catch (e) {} }
