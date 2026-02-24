-- ============================================
-- Supabase SQL Editor でこのSQLを実行してください
-- ============================================

-- 1. rooms テーブル作成
create table if not exists rooms (
  code text primary key,
  data jsonb not null default '{}',
  updated_at timestamptz not null default now()
);

-- 2. updated_at を自動更新するトリガー
create or replace function update_updated_at()
returns trigger as $$
begin
  new.updated_at = now();
  return new;
end;
$$ language plpgsql;

drop trigger if exists rooms_updated_at on rooms;
create trigger rooms_updated_at
  before update on rooms
  for each row execute function update_updated_at();

-- 3. Realtime を有効化
alter publication supabase_realtime add table rooms;

-- 4. RLS（Row Level Security）を有効化
-- 匿名ユーザーが読み書きできるようにする（ゲーム用）
alter table rooms enable row level security;

create policy "Anyone can read rooms"
  on rooms for select
  using (true);

create policy "Anyone can insert rooms"
  on rooms for insert
  with check (true);

create policy "Anyone can update rooms"
  on rooms for update
  using (true);

create policy "Anyone can delete rooms"
  on rooms for delete
  using (true);

-- 5. 古いルームを自動削除（24時間経過）- オプション
-- Supabase の pg_cron extension が必要
-- select cron.schedule('cleanup-old-rooms', '0 * * * *',
--   $$delete from rooms where updated_at < now() - interval '24 hours'$$
-- );
