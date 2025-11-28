# ChordThinker 🎵

音楽理論とAI (Google Gemini) を組み合わせた、直感的なコード進行作成支援ツールです。
コードブロックを並べるだけでMIDIを出力でき、行き詰まったらAIが「王道」と「スパイス」な進行を提案してくれます。

## ✨ 主な機能

* **ハイブリッド提案:** 音楽理論に基づく瞬時の提案 + Gemini AIによる文脈を読んだ提案。
* **ピアノロール編集:** 転回形やボイシングを視覚的に編集可能。
* **直感的な操作:** ブロックのドラッグ移動、ダブルクリックでの長さ変更。
* **プロジェクト管理:** `.ctp` 形式での保存・読み込みに対応。
* **MIDIエクスポート:** DAWにそのままドラッグ＆ドロップできるMIDIファイルを出力。

## 📦 インストールと実行

### 必要要件
* Python 3.10+
* Google AI Studio API Key (無料枠あり)

### ライブラリのインストール
```bash
pip install mido pygame google-generativeai

pyinstaller --noconsole --onedir --clean --noconfirm --collect-all google.generativeai --hidden-import=mido --hidden-import=pygame --name ChordThinker chordthinker.py

