# ♠ SCARNEY ♣ — ボムポット・スカーニー

友達とオンラインで遊べるスカーニーポーカー。

## セットアップ手順

### 1. Supabase プロジェクト作成（無料）

1. [supabase.com](https://supabase.com) でアカウント作成
2. 「New Project」→ プロジェクト名とパスワードを設定
3. リージョンは `Northeast Asia (Tokyo)` を選択
4. プロジェクト作成後、**SQL Editor** を開く
5. `sql/setup.sql` の内容を貼り付けて **Run** を実行

### 2. Supabase の API キーを取得

1. Supabase ダッシュボード → **Settings** → **API**
2. 以下の2つをコピー:
   - **Project URL** → `https://xxxxx.supabase.co`
   - **anon (public) key** → `eyJxxxxx...`

### 3. Supabase Realtime を有効化

1. Supabase ダッシュボード → **Database** → **Replication**
2. `rooms` テーブルの Realtime が有効になっていることを確認
   （SQL で `alter publication supabase_realtime add table rooms;` を実行済みなら OK）

### 4. ローカルで動かす

```bash
# クローン or ダウンロード後
cd scarney

# 依存関係インストール
npm install

# 環境変数を設定
cp .env.example .env
# .env を編集して Supabase の URL と Key を入力

# 開発サーバー起動
npm run dev
```

`http://localhost:5173` でゲームが開く。

### 5. Vercel にデプロイ

```bash
# Vercel CLI がなければインストール
npm i -g vercel

# デプロイ
vercel
```

**または** GitHub にプッシュして Vercel ダッシュボードから連携：

1. [vercel.com](https://vercel.com) → 「Import Project」→ GitHub リポジトリを選択
2. **Environment Variables** に以下を追加:
   - `VITE_SUPABASE_URL` → Supabase の Project URL
   - `VITE_SUPABASE_ANON_KEY` → Supabase の anon key
3. Deploy！

### 6. 遊び方

1. デプロイしたURL（`https://your-app.vercel.app`）を開く
2. 名前を入力 → 「ルームを作成」
3. 表示された **4文字のルームコード** を友達に送る
4. 友達が同じURLを開いてコードを入力して参加
5. ディーラー（👑）が「ゲーム開始」を押す

---

## ルール

- 全員同額ベット → ベッティングなしでフロップ/ターン/リバーを進行
- 各ストリートで上段・下段にカードがオープン
- **下段と同じ数字の手札は強制ディスカード**
- 💀 **リバーで** 1枚も捨てない or ハンドが0枚 → バースト
- 残った手札 + 上段ボードで最強5枚 = **ハイ**
- 手札の点数合計最小 = **ロー** (A=1, 数字=額面, J/Q/K=10)
- ポットをハイ/ローで折半

## 技術スタック

- **Vite + React** — フロントエンド
- **Supabase** — リアルタイムDB（PostgreSQL + Realtime）
- **Vercel** — ホスティング
