import tkinter as tk
from tkinter import messagebox, filedialog, ttk, simpledialog
import mido
from mido import Message, MidiFile, MidiTrack, MetaMessage
import pygame
import threading
import time
import google.generativeai as genai
import os
import re
import tempfile
import json
import shutil

# --- Configuration ---
C_BG_MAIN = "#1e1e1e"
C_BG_PANEL = "#252526"
C_TEXT_MAIN = "#ffffff"
C_SELECTION = "#ffffff"

C_SUGGEST_BG = "#ffff00" 
C_SUGGEST_FG = "#000000"
C_SPICE_BG = "#00ffcc"
C_SPICE_FG = "#000000"
C_BTN_DEFAULT_BG = "#2a2a2a"

# Piano Roll Colors
C_PR_BG = "#111111"
C_PR_GRID = "#333333"
C_PR_NOTE = "#ff5555"
C_PR_NOTE_SEL = "#ffaaaa"
C_PR_KEY_WHITE = "#dddddd"
C_PR_KEY_BLACK = "#444444"

FONT_FAMILY = "Segoe UI"
FONT_SIZE_UI = 10
FONT_SIZE_BTN = 10

CONFIG_FILE = "config.json"

TYPE_COLORS = {
    'Maj':  "#007acc", 'Maj7': "#005a9e",
    'Min':  "#d16d9e", 'm7':   "#b14d7e", 'mM7':  "#c239b3",
    '7':    "#e0aa00",
    'dim':  "#888888", 'dim7': "#666666",
    'm7-5': "#777777",
    'aug':  "#ff4444",
    'sus4': "#4ec9b0", 'sus2': "#2c9c85",
    'add9': "#9cdcfe",
    'Rest': "#444444"
}

CHORD_DEFS = {
    'Maj': [0, 4, 7], 'Min': [0, 3, 7], '7': [0, 4, 7, 10], 'Maj7': [0, 4, 7, 11],
    'm7': [0, 3, 7, 10], 'mM7': [0, 3, 7, 11], 'm7-5': [0, 3, 6, 10],
    'dim': [0, 3, 6], 'dim7': [0, 3, 6, 9],
    'aug': [0, 4, 8], 'sus4': [0, 5, 7], 'sus2': [0, 2, 7], 'add9': [0, 4, 7, 14],
    'Rest': []
}
ROOTS = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
NOTE_MAP = {note: i for i, note in enumerate(ROOTS)}

ENHARMONIC_MAP = {
    'Db': 'C#', 'Eb': 'D#', 'Gb': 'F#', 'Ab': 'G#', 'Bb': 'A#',
    'DB': 'C#', 'EB': 'D#', 'GB': 'F#', 'AB': 'G#', 'BB': 'A#'
}

DURATION_OPTIONS = {
    "8分音符": 0.125, "4分音符": 0.25, "2分音符": 0.5,
    "全音符": 1.0, "2小節": 2.0, "4小節": 4.0
}

INSTRUMENT_MAP = {
    "Grand Piano": 0, "Bright Piano": 1, "Electric Piano": 4, "Harpsichord": 6,
    "Celesta": 8, "Music Box": 10, "Vibraphone": 11, "Drawbar Organ": 16,
    "Rock Organ": 18, "Accordion": 21, "Nylon Guitar": 24, "Steel Guitar": 25,
    "Jazz Guitar": 26, "Clean Guitar": 27, "Overdrive Gtr": 29, "Distortion Gtr": 30,
    "Acoustic Bass": 32, "Finger Bass": 33, "Pick Bass": 34, "Fretless Bass": 35,
    "Slap Bass": 36, "Synth Bass 1": 38, "Violin": 40, "Cello": 42,
    "Tremolo Str": 44, "Harp": 46, "Strings Ens": 48, "Slow Strings": 49,
    "Synth Strings": 50, "Voice Oohs": 53, "Trumpet": 56, "Saxophone": 65,
    "Oboe": 68, "Flute": 73, "Square Lead": 80, "Sawtooth Lead": 81,
    "Calliope": 82, "New Age Pad": 88, "Warm Pad": 89, "Polysynth": 90,
    "Halo Pad": 94, "Sci-Fi": 103, "Sitar": 104,
}

PRESET_PROGRESSIONS = {
    "王道進行 (Major)": ["F_Maj", "G_Maj", "E_Min", "A_Min"],
    "カノン進行 (Major)": ["C_Maj", "G_Maj", "A_Min", "E_Min", "F_Maj", "C_Maj", "F_Maj", "G_Maj"],
    "小室進行 (Minor)": ["A_Min", "F_Maj", "G_Maj", "C_Maj"],
    "Just The Two Of Us": ["F_Maj7", "E_7", "A_m7", "G_m7", "C_7"],
    "パッシングdim (例)": ["C_Maj", "C#_dim7", "D_m7", "G_7"],
    "J-Popバラード": ["A_Min", "E_Min", "F_Maj", "G_Maj"],
}

class ChordThinkerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        
        self.project_name = "Untitled"
        self.current_file_path = None
        self.is_modified = False
        
        self.update_title()
        self.geometry("1300x950")
        self.configure(bg=C_BG_MAIN)
        
        # Audio Init
        pygame.init()
        pygame.mixer.init()
        self.cleanup_temp_files(force=True)

        self.config = self.load_config()

        self.progression = []
        self.selection = set()
        self.clipboard = []
        self.chord_buttons = {}   
        self.is_playing = False
        self.block_coords = []
        self.current_temp_file = None
        
        self.drag_item_index = None
        self.drag_start_x = 0
        
        # Piano Roll
        self.show_piano_roll = False
        self.pr_note_drag_index = None
        self.pr_start_y = 0
        self.pr_start_pitch = 0
        self.pr_height = 250
        self.pr_key_height = 14
        self.pr_min_note = 24   # C1
        self.pr_max_note = 96   # C7
        
        # API Key
        self.api_key = self.config.get("api_key", "").strip()
        self.is_thinking = False
        self.cached_model_name = None

        if self.api_key:
            try: genai.configure(api_key=self.api_key)
            except: pass

        self.setup_ui()
        self.bind_keys()
        self.update_suggestions_logic(None)
        
        self.protocol("WM_DELETE_WINDOW", self.on_closing)

    def on_closing(self):
        self.cleanup_temp_files(force=True)
        self.destroy()

    def update_title(self):
        name = self.project_name
        mark = "*" if self.is_modified else ""
        self.title(f"CHORD THINKER - {name}{mark}")

    def load_config(self):
        default_config = {
            "api_key": "",
            "default_bpm": "120",
            "default_instrument": "Grand Piano",
            "default_duration": "全音符"
        }
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                    return {**default_config, **json.load(f)}
            except: return default_config
        else: return default_config

    def save_config_file(self):
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(self.config, f, indent=4)
        except Exception as e:
            messagebox.showerror("Error", f"設定の保存に失敗: {e}")

    # --- ECO SYSTEM ---
    def get_temp_dir(self):
        base = os.getcwd()
        temp_dir = os.path.join(base, "temp")
        if not os.path.exists(temp_dir): os.makedirs(temp_dir)
        return temp_dir

    def cleanup_temp_files(self, force=False):
        temp_dir = self.get_temp_dir()
        if force:
            try:
                pygame.mixer.music.stop()
                pygame.mixer.music.unload()
            except: pass
            
        for f in os.listdir(temp_dir):
            if f.endswith(".mid"):
                try: os.remove(os.path.join(temp_dir, f))
                except: pass
    
    def manual_cleanup(self):
        self.cleanup_temp_files(force=True)
        messagebox.showinfo("完了", "一時ファイルを削除しました。")

    # --- Settings ---
    def open_settings(self):
        win = tk.Toplevel(self)
        win.title("環境設定")
        win.geometry("450x350")
        win.configure(bg=C_BG_PANEL)
        x = self.winfo_rootx() + self.winfo_width()//2 - 225
        y = self.winfo_rooty() + self.winfo_height()//2 - 175
        win.geometry(f"+{x}+{y}")

        lbl_font = (FONT_FAMILY, 10)
        tk.Label(win, text="Google Gemini API Key:", bg=C_BG_PANEL, fg="white", font=lbl_font).pack(anchor="w", padx=20, pady=(20, 5))
        entry_key = tk.Entry(win, width=50, font=lbl_font)
        entry_key.insert(0, self.config.get("api_key", ""))
        entry_key.pack(padx=20)
        tk.Label(win, text="※設定すると次回から自動で読み込まれます", bg=C_BG_PANEL, fg="#888888", font=(FONT_FAMILY, 8)).pack(anchor="w", padx=20)

        tk.Label(win, text="デフォルトBPM:", bg=C_BG_PANEL, fg="white", font=lbl_font).pack(anchor="w", padx=20, pady=(15, 5))
        entry_bpm = tk.Entry(win, width=10, font=lbl_font)
        entry_bpm.insert(0, self.config.get("default_bpm", "120"))
        entry_bpm.pack(anchor="w", padx=20)

        tk.Label(win, text="デフォルト楽器:", bg=C_BG_PANEL, fg="white", font=lbl_font).pack(anchor="w", padx=20, pady=(15, 5))
        combo_inst = ttk.Combobox(win, values=list(INSTRUMENT_MAP.keys()), state="readonly", width=30)
        combo_inst.set(self.config.get("default_instrument", "Grand Piano"))
        combo_inst.pack(anchor="w", padx=20)

        def save_and_close():
            new_key = entry_key.get().strip()
            self.config["api_key"] = new_key
            self.config["default_bpm"] = entry_bpm.get()
            self.config["default_instrument"] = combo_inst.get()
            self.save_config_file()
            self.api_key = new_key
            self.cached_model_name = None 
            msg = "設定保存: APIキー有効" if self.api_key else "設定保存: APIキーなし"
            self.advice_label.config(text=msg)
            messagebox.showinfo("保存", "設定を保存しました。")
            win.destroy()

        tk.Button(win, text="保存して閉じる", command=save_and_close, bg=TYPE_COLORS['sus4'], fg="black", relief=tk.FLAT, font=(FONT_FAMILY, 10, "bold")).pack(pady=30)


    # --- UI ---
    def setup_ui(self):
        header = tk.Frame(self, bg=C_BG_MAIN, pady=10)
        header.pack(fill=tk.X, padx=20)
        tk.Label(header, text="CHORD THINKER", bg=C_BG_MAIN, fg="#aaaaaa", font=(FONT_FAMILY, 14, "bold")).pack(side=tk.LEFT)
        
        right_frame = tk.Frame(header, bg=C_BG_MAIN)
        right_frame.pack(side=tk.RIGHT)
        
        tk.Button(right_frame, text="🗑️", command=self.manual_cleanup, width=3, bg="#444444", fg="white", relief=tk.FLAT).pack(side=tk.RIGHT, padx=2)
        tk.Button(right_frame, text="？", command=self.show_help, width=3, bg="#444444", fg="white", relief=tk.FLAT).pack(side=tk.RIGHT, padx=2)
        tk.Button(right_frame, text="⚙ 設定", command=self.open_settings, bg="#007acc", fg="white", relief=tk.FLAT).pack(side=tk.RIGHT, padx=2)
        tk.Label(right_frame, text=" | ", bg=C_BG_MAIN, fg="#555555").pack(side=tk.RIGHT, padx=2)
        
        self.save_btn = tk.Menubutton(right_frame, text="💾 保存 ▼", bg="#555555", fg="white", relief=tk.FLAT, direction='below')
        self.save_menu = tk.Menu(self.save_btn, tearoff=0)
        self.save_menu.add_command(label="上書き保存 (Ctrl+S)", command=self.save_project_overwrite)
        self.save_menu.add_command(label="名前を付けて保存...", command=self.save_project_as)
        self.save_menu.add_separator()
        self.save_menu.add_command(label="コピーを保存...", command=self.save_project_copy)
        self.save_btn.config(menu=self.save_menu)
        self.save_btn.pack(side=tk.RIGHT, padx=2)

        tk.Button(right_frame, text="📂 開く", command=self.load_project, bg="#555555", fg="white", relief=tk.FLAT).pack(side=tk.RIGHT, padx=2)
        tk.Button(right_frame, text="📄 新規", command=self.new_project, bg="#555555", fg="white", relief=tk.FLAT).pack(side=tk.RIGHT, padx=2)
        
        tk.Label(right_frame, text=" | ", bg=C_BG_MAIN, fg="#555555").pack(side=tk.RIGHT, padx=2)
        
        tk.Button(right_frame, text="追加", command=self.load_preset, bg="#444444", fg="white", relief=tk.FLAT).pack(side=tk.RIGHT, padx=2)
        self.preset_var = tk.StringVar()
        self.preset_combo = ttk.Combobox(right_frame, textvariable=self.preset_var, values=list(PRESET_PROGRESSIONS.keys()), state="readonly", width=18)
        self.preset_combo.current(0)
        self.preset_combo.pack(side=tk.RIGHT, padx=2)

        # Container for Canvas and Piano Roll
        self.middle_container = tk.Frame(self, bg=C_BG_MAIN)
        self.middle_container.pack(fill=tk.X, padx=20, pady=5)

        self.canvas = tk.Canvas(self.middle_container, height=160, bg="#111111", highlightthickness=0)
        self.canvas.pack(fill=tk.X, side=tk.TOP)
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.canvas.bind("<Double-Button-1>", self.on_canvas_double_click)
        
        toggle_frame = tk.Frame(self, bg=C_BG_MAIN)
        toggle_frame.pack(fill=tk.X, padx=20)
        self.pr_toggle_btn = tk.Button(toggle_frame, text="🎹 ピアノロール (開く)", command=self.toggle_piano_roll,
                                       bg="#333333", fg="white", relief=tk.FLAT, font=(FONT_FAMILY, 9))
        self.pr_toggle_btn.pack(side=tk.LEFT)

        self.pr_frame = tk.Frame(self.middle_container, bg=C_PR_BG, height=250)
        self.pr_scrollbar = tk.Scrollbar(self.pr_frame, orient="vertical")
        self.pr_canvas = tk.Canvas(self.pr_frame, bg=C_PR_BG, highlightthickness=0, 
                                   height=250, yscrollcommand=self.pr_scrollbar.set)
        self.pr_scrollbar.config(command=self.pr_canvas.yview)
        
        self.pr_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.pr_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.pr_canvas.bind("<Button-1>", self.on_pr_click)
        self.pr_canvas.bind("<B1-Motion>", self.on_pr_drag)
        self.pr_canvas.bind("<ButtonRelease-1>", self.on_pr_release)

        ctrl = tk.Frame(self, bg=C_BG_PANEL, pady=12, padx=15)
        ctrl.pack(fill=tk.X, padx=20, pady=10)

        self.make_label(ctrl, "楽器:")
        self.inst_var = tk.StringVar(value=self.config.get("default_instrument", "Grand Piano"))
        self.inst_combo = ttk.Combobox(ctrl, textvariable=self.inst_var, values=list(INSTRUMENT_MAP.keys()), width=15, state="readonly", font=(FONT_FAMILY, 10))
        self.inst_combo.pack(side=tk.LEFT, padx=5)

        self.make_label(ctrl, "BPM:")
        self.bpm_var = tk.StringVar(value=self.config.get("default_bpm", "120"))
        tk.Entry(ctrl, textvariable=self.bpm_var, width=5, bg="#333333", fg="white", relief=tk.FLAT, font=(FONT_FAMILY, 11)).pack(side=tk.LEFT, padx=5)

        self.make_label(ctrl, "音符:")
        self.dur_var = tk.StringVar(value="全音符")
        self.dur_combo = ttk.Combobox(ctrl, textvariable=self.dur_var, values=list(DURATION_OPTIONS.keys()), width=10, state="readonly", font=(FONT_FAMILY, 10))
        self.dur_combo.pack(side=tk.LEFT, padx=5)

        self.make_label(ctrl, "Key:")
        self.key_root_var = tk.StringVar(value="C")
        self.key_root_combo = ttk.Combobox(ctrl, textvariable=self.key_root_var, values=ROOTS, width=3, state="readonly", font=(FONT_FAMILY, 11))
        self.key_root_combo.pack(side=tk.LEFT, padx=5)
        self.key_scale_var = tk.StringVar(value="Major")
        self.key_scale_combo = ttk.Combobox(ctrl, textvariable=self.key_scale_var, values=["Major", "Minor"], width=6, state="readonly", font=(FONT_FAMILY, 11))
        self.key_scale_combo.pack(side=tk.LEFT, padx=5)
        
        self.key_root_combo.bind("<<ComboboxSelected>>", lambda e: self.update_suggestions_logic(self.get_last_selected_chord_name()))
        self.key_scale_combo.bind("<<ComboboxSelected>>", lambda e: self.update_suggestions_logic(self.get_last_selected_chord_name()))

        self.make_btn(ctrl, "▶ 再生", self.play_preview, bg=TYPE_COLORS['sus4'], fg="black")
        self.make_btn(ctrl, "■ 停止", self.stop_preview, bg=TYPE_COLORS['aug'])
        
        self.make_btn(ctrl, "１つ削除", self.delete_selection, bg="#555555", side=tk.RIGHT)
        self.make_btn(ctrl, "全消去", self.reset_progression, bg="#333333", side=tk.RIGHT)
        self.make_btn(ctrl, "MIDI出力", self.export_midi, bg=TYPE_COLORS['Maj'], fg="black", side=tk.RIGHT)

        advice_frame = tk.Frame(self, bg="#222222", bd=1, relief=tk.SUNKEN, height=60)
        advice_frame.pack(fill=tk.X, padx=20, pady=5)
        advice_frame.pack_propagate(False)
        self.ai_btn = tk.Button(advice_frame, text="🤖 AIに聞く", command=self.ask_gemini, bg="#720e9e", fg="white", font=(FONT_FAMILY, 10, "bold"), relief=tk.RAISED)
        self.ai_btn.pack(side=tk.LEFT, padx=10, pady=10)
        initial_msg = "APIキー設定済み" if self.api_key else "設定ボタンからAPIキーを設定してください"
        self.advice_label = tk.Label(advice_frame, text=f"理論モード: {initial_msg}", bg="#222222", fg="white", font=(FONT_FAMILY, 10), anchor="w", justify="left", wraplength=900)
        self.advice_label.pack(side=tk.LEFT, padx=10, fill=tk.BOTH, expand=True)

        container_frame = tk.Frame(self, bg=C_BG_MAIN)
        container_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=5)
        legend_row = tk.Frame(container_frame, bg=C_BG_MAIN)
        legend_row.pack(anchor=tk.W, fill=tk.X)
        tk.Button(legend_row, text="休 (Rest)", bg="#333333", fg="white", bd=0, relief=tk.FLAT, width=8, command=lambda: self.add_chord("Rest_Rest")).pack(side=tk.LEFT, pady=5)
        tk.Label(legend_row, text="  推奨:", bg=C_BG_MAIN, fg="#888888").pack(side=tk.LEFT)
        tk.Label(legend_row, text=" ■ 王道 ", bg=C_SUGGEST_BG, fg="black", font=(FONT_FAMILY, 9)).pack(side=tk.LEFT, padx=2)
        tk.Label(legend_row, text=" ■ スパイス ", bg=C_SPICE_BG, fg="black", font=(FONT_FAMILY, 9)).pack(side=tk.LEFT, padx=2)

        canvas_scroll = tk.Canvas(container_frame, bg=C_BG_MAIN, highlightthickness=0)
        scrollbar = ttk.Scrollbar(container_frame, orient="vertical", command=canvas_scroll.yview)
        scrollable_frame = tk.Frame(canvas_scroll, bg=C_BG_MAIN)
        scrollable_frame.bind("<Configure>", lambda e: canvas_scroll.configure(scrollregion=canvas_scroll.bbox("all")))
        canvas_scroll.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas_scroll.configure(yscrollcommand=scrollbar.set)
        canvas_scroll.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        for col, root in enumerate(ROOTS):
            tk.Label(scrollable_frame, text=root, bg=C_BG_MAIN, fg="#aaaaaa", font=(FONT_FAMILY, 11, "bold"), width=6).grid(row=0, column=col+1, pady=(0,5))
        display_types = [k for k in CHORD_DEFS.keys() if k != 'Rest']
        for row, type_key in enumerate(display_types):
            color = TYPE_COLORS.get(type_key, "#ffffff")
            tk.Label(scrollable_frame, text=type_key, bg=C_BG_MAIN, fg=color, font=(FONT_FAMILY, 11, "bold"), anchor=tk.E, width=6).grid(row=row+1, column=0, padx=(0,10), pady=2)
            for col, root in enumerate(ROOTS):
                chord_name = f"{root}_{type_key}"
                btn = tk.Button(scrollable_frame, text="▪", bg=C_BTN_DEFAULT_BG, fg=color, activebackground=color, activeforeground="white", bd=0, relief=tk.FLAT, width=5, height=2, font=(FONT_FAMILY, 10), command=lambda c=chord_name: self.add_chord(c))
                btn.grid(row=row+1, column=col+1, padx=2, pady=2)
                self.chord_buttons[chord_name] = btn

    def make_label(self, parent, text):
        lbl = tk.Label(parent, text=text, bg=C_BG_PANEL, fg=C_TEXT_MAIN, font=(FONT_FAMILY, 10))
        lbl.pack(side=tk.LEFT, padx=(15,2))
        return lbl

    def make_btn(self, parent, text, cmd, bg="#555555", fg="white", side=tk.LEFT):
        btn = tk.Button(parent, text=text, command=cmd, bg=bg, fg=fg, relief=tk.FLAT, font=(FONT_FAMILY, 10, "bold"), padx=15, pady=2)
        btn.pack(side=side, padx=5)
        return btn

    def show_help(self):
        messagebox.showinfo("ガイド", "・ブロック移動：ドラッグで並べ替え\n・ダブルクリック：長さ変更\n・AIボタン：Geminiに相談\n・プロジェクト保存：作業を保存\n・ゴミ箱：キャッシュ削除")

    def bind_keys(self):
        self.bind("<Control-c>", self.copy_selection)
        self.bind("<Control-v>", self.paste_selection)
        self.bind("<Delete>", self.delete_selection)
        self.bind("<BackSpace>", self.delete_selection)
        self.bind("<Control-a>", self.select_all)
        self.bind("<Control-s>", lambda e: self.save_project_overwrite())

    # --- Project Management ---
    def get_project_dir(self):
        base = os.getcwd()
        proj_dir = os.path.join(base, "project")
        if not os.path.exists(proj_dir): os.makedirs(proj_dir)
        return proj_dir

    def get_project_data(self):
        return {
            "progression": self.progression,
            "bpm": self.bpm_var.get(),
            "instrument": self.inst_var.get(),
            "key_root": self.key_root_var.get(),
            "key_scale": self.key_scale_var.get()
        }

    def new_project(self):
        if self.progression:
            if not messagebox.askyesno("確認", "現在の作業内容は消えますが、新規作成しますか？"):
                return
        self.progression = []
        self.current_file_path = None
        self.project_name = "Untitled"
        self.is_modified = False
        self.draw_progression()
        self.update_title()
        self.update_suggestions_logic(None)

    def save_project_overwrite(self, event=None):
        if not self.progression: return
        if self.current_file_path:
            try:
                with open(self.current_file_path, "w", encoding="utf-8") as f:
                    json.dump(self.get_project_data(), f, indent=4)
                self.is_modified = False
                self.update_title()
            except Exception as e:
                messagebox.showerror("Error", f"保存失敗: {e}")
        else:
            self.save_project_as()

    def save_project_as(self):
        if not self.progression:
            messagebox.showwarning("Info", "保存するデータがありません。")
            return
        file_path = filedialog.asksaveasfilename(
            initialdir=self.get_project_dir(),
            defaultextension=".ctp",
            filetypes=[("Chord Thinker Project", "*.ctp"), ("All Files", "*.*")],
            title="名前を付けて保存"
        )
        if file_path:
            try:
                with open(file_path, "w", encoding="utf-8") as f:
                    json.dump(self.get_project_data(), f, indent=4)
                self.current_file_path = file_path
                self.project_name = os.path.basename(file_path)
                self.is_modified = False
                self.update_title()
                messagebox.showinfo("保存", "保存しました。")
            except Exception as e:
                messagebox.showerror("Error", f"保存失敗: {e}")

    def save_project_copy(self):
        if not self.progression: return
        file_path = filedialog.asksaveasfilename(
            initialdir=self.get_project_dir(),
            defaultextension=".ctp",
            filetypes=[("Chord Thinker Project", "*.ctp"), ("All Files", "*.*")],
            title="コピーを保存"
        )
        if file_path:
            try:
                with open(file_path, "w", encoding="utf-8") as f:
                    json.dump(self.get_project_data(), f, indent=4)
                messagebox.showinfo("保存", "コピーを保存しました。")
            except Exception as e:
                messagebox.showerror("Error", f"保存失敗: {e}")

    def load_project(self):
        file_path = filedialog.askopenfilename(
            initialdir=self.get_project_dir(),
            filetypes=[("Chord Thinker Project", "*.ctp"), ("All Files", "*.*")],
            title="プロジェクトを開く"
        )
        if file_path:
            try:
                with open(file_path, "r", encoding="utf-8") as f: data = json.load(f)
                self.progression = data.get("progression", [])
                self.bpm_var.set(data.get("bpm", "120"))
                self.inst_var.set(data.get("instrument", "Grand Piano"))
                self.key_root_var.set(data.get("key_root", "C"))
                self.key_scale_var.set(data.get("key_scale", "Major"))
                self.current_file_path = file_path
                self.project_name = os.path.basename(file_path)
                self.is_modified = False
                self.update_title()
                self.draw_progression()
                self.update_suggestions_logic(self.get_last_selected_chord_name())
                messagebox.showinfo("Success", "読み込みました。")
            except Exception as e: messagebox.showerror("Error", f"読み込み失敗: {e}")

    # --- Canvas Actions ---
    def on_canvas_click(self, event):
        clicked_x = event.x
        clicked_index = -1
        for idx, (x1, x2) in enumerate(self.block_coords):
            if x1 <= clicked_x <= x2: clicked_index = idx; break
        
        if clicked_index != -1:
            self.drag_item_index = clicked_index
            self.drag_start_x = clicked_x
            if clicked_index in self.selection: self.selection.remove(clicked_index)
            else: 
                self.selection.clear()
                self.selection.add(clicked_index)
            self.update_suggestions_logic(self.progression[clicked_index]['name'])
        else:
            self.selection.clear()
            self.update_suggestions_logic(None)
        self.draw_progression()
        self.draw_piano_roll()

    def on_canvas_drag(self, event):
        if self.drag_item_index is not None:
            dx = event.x - self.drag_start_x
            self.canvas.move(f"group_{self.drag_item_index}", dx, 0)
            self.drag_start_x = event.x

    def on_canvas_release(self, event):
        if self.drag_item_index is not None:
            drop_x = event.x
            new_index = 0
            for i, (x1, x2) in enumerate(self.block_coords):
                center = (x1 + x2) / 2
                if drop_x > center: new_index = i + 1
                else: break
            if new_index > len(self.progression): new_index = len(self.progression)
            
            if new_index != self.drag_item_index and new_index != self.drag_item_index + 1:
                item = self.progression.pop(self.drag_item_index)
                if new_index > self.drag_item_index: new_index -= 1
                self.progression.insert(new_index, item)
                if self.drag_item_index in self.selection:
                    self.selection.remove(self.drag_item_index)
                    self.selection.add(new_index)
                self.mark_modified()
            self.drag_item_index = None
            self.draw_progression()
            self.draw_piano_roll()

    def mark_modified(self):
        if not self.is_modified:
            self.is_modified = True
            self.update_title()

    def on_canvas_double_click(self, event):
        clicked_x = event.x
        clicked_index = -1
        for idx, (x1, x2) in enumerate(self.block_coords):
            if x1 <= clicked_x <= x2: clicked_index = idx; break
        if clicked_index != -1: self.open_duration_editor(clicked_index)

    def open_duration_editor(self, index):
        current_data = self.progression[index]
        current_dur_val = current_data['duration']
        current_label = "全音符"
        for k, v in DURATION_OPTIONS.items():
            if v == current_dur_val: current_label = k; break

        edit_win = tk.Toplevel(self)
        edit_win.title("長さ変更")
        edit_win.geometry("250x150")
        edit_win.configure(bg=C_BG_PANEL)
        x = self.winfo_rootx() + self.winfo_width()//2 - 125
        y = self.winfo_rooty() + self.winfo_height()//2 - 75
        edit_win.geometry(f"+{x}+{y}")

        tk.Label(edit_win, text=f"Change: {current_data['name'].replace('_', '')}", 
                 bg=C_BG_PANEL, fg="white", font=(FONT_FAMILY, 10)).pack(pady=10)
        combo = ttk.Combobox(edit_win, values=list(DURATION_OPTIONS.keys()), state="readonly")
        combo.set(current_label)
        combo.pack(pady=5)

        def apply_change():
            new_label = combo.get()
            if new_label in DURATION_OPTIONS:
                self.progression[index]['duration'] = DURATION_OPTIONS[new_label]
                self.draw_progression()
                self.mark_modified()
                edit_win.destroy()
        tk.Button(edit_win, text="変更", command=apply_change, bg=TYPE_COLORS['sus4'], fg="black", relief=tk.FLAT).pack(pady=15)

    # --- Piano Roll ---
    def toggle_piano_roll(self):
        if self.show_piano_roll:
            self.pr_frame.pack_forget()
            self.pr_toggle_btn.config(text="🎹 ピアノロール (開く)")
            self.show_piano_roll = False
        else:
            self.pr_frame.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)
            self.pr_toggle_btn.config(text="🎹 ピアノロール (閉じる)")
            self.show_piano_roll = True
            self.draw_piano_roll()

    def draw_piano_roll(self):
        self.pr_canvas.delete("all")
        if not self.show_piano_roll: return
        total_height = (self.pr_max_note - self.pr_min_note + 1) * self.pr_key_height
        self.pr_canvas.configure(scrollregion=(0, 0, 1000, total_height))
        
        for note_num in range(self.pr_max_note, self.pr_min_note - 1, -1):
            y = (self.pr_max_note - note_num) * self.pr_key_height
            is_black = (note_num % 12) in [1, 3, 6, 8, 10]
            color = C_PR_KEY_BLACK if is_black else C_PR_KEY_WHITE
            self.pr_canvas.create_rectangle(0, y, 40, y + self.pr_key_height, fill=color, outline="#888888")
            if note_num % 12 == 0: self.pr_canvas.create_text(20, y + self.pr_key_height/2, text=f"C{note_num//12 - 1}", font=("Arial", 8))
            line_col = "#222222" if is_black else "#2a2a2a"
            self.pr_canvas.create_rectangle(40, y, 2000, y + self.pr_key_height, fill=line_col, outline="")
            self.pr_canvas.create_line(40, y, 2000, y, fill="#333333")
        sel_idx = self.get_selected_index()
        if sel_idx is not None:
            chord = self.progression[sel_idx]
            notes = chord.get('voicing', self.get_default_notes(chord['name']))
            for i, note_num in enumerate(notes):
                if self.pr_min_note <= note_num <= self.pr_max_note:
                    y = (self.pr_max_note - note_num) * self.pr_key_height
                    tag = f"note_{i}"
                    self.pr_canvas.create_rectangle(60, y + 2, 200, y + self.pr_key_height - 2, fill=C_PR_NOTE, outline="white", tags=tag)

    def on_pr_click(self, event):
        self.pr_note_drag_index = None
        sel_idx = self.get_selected_index()
        if sel_idx is None: return
        # Adjust y with scroll
        canvas_y = self.pr_canvas.canvasy(event.y)
        item = self.pr_canvas.find_closest(event.x, canvas_y)
        tags = self.pr_canvas.gettags(item)
        for tag in tags:
            if tag.startswith("note_"):
                self.pr_note_drag_index = int(tag.split("_")[1])
                self.pr_start_y = canvas_y
                chord = self.progression[sel_idx]
                notes = chord.get('voicing', self.get_default_notes(chord['name']))
                self.pr_start_pitch = notes[self.pr_note_drag_index]
                break

    def on_pr_drag(self, event):
        if self.pr_note_drag_index is not None:
            canvas_y = self.pr_canvas.canvasy(event.y)
            dy = canvas_y - self.pr_start_y
            semitones = -int(dy / self.pr_key_height)
            sel_idx = self.get_selected_index()
            chord = self.progression[sel_idx]
            current_notes = list(chord.get('voicing', self.get_default_notes(chord['name'])))
            new_pitch = self.pr_start_pitch + semitones
            if new_pitch < 0: new_pitch = 0
            if new_pitch > 127: new_pitch = 127
            current_notes[self.pr_note_drag_index] = new_pitch
            chord['voicing'] = current_notes
            self.draw_piano_roll()
            self.mark_modified()

    def on_pr_release(self, event):
        if self.pr_note_drag_index is not None:
            self.play_single_chord_preview()
            self.pr_note_drag_index = None

    def play_single_chord_preview(self):
        self.cleanup_temp_files()
        sel_idx = self.get_selected_index()
        if sel_idx is None: return
        temp_dir = self.get_temp_dir()
        fd, temp_path = tempfile.mkstemp(suffix=".mid", dir=temp_dir)
        os.close(fd)
        mid = MidiFile()
        track = MidiTrack()
        mid.tracks.append(track)
        inst_name = self.inst_var.get()
        prog_num = INSTRUMENT_MAP.get(inst_name, 0)
        track.append(Message('program_change', program=prog_num, time=0))
        chord = self.progression[sel_idx]
        notes = chord.get('voicing', self.get_default_notes(chord['name']))
        for n in notes: track.append(Message('note_on', note=n, velocity=90, time=0))
        track.append(Message('note_off', note=notes[0], velocity=90, time=480))
        for n in notes[1:]: track.append(Message('note_off', note=n, velocity=90, time=0))
        mid.save(temp_path)
        try: pygame.mixer.music.load(temp_path); pygame.mixer.music.play()
        except: pass

    def get_selected_index(self):
        if self.selection: return list(self.selection)[0]
        return None

    def get_default_notes(self, chord_name):
        if chord_name == "Rest_Rest": return []
        try:
            root_str, type_str = chord_name.split('_')
            root_base = NOTE_MAP[root_str] + 48 
            intervals = CHORD_DEFS[type_str]
            return [root_base + interval for interval in intervals]
        except: return []

    def get_notes(self, chord_data):
        if 'voicing' in chord_data: return chord_data['voicing']
        return self.get_default_notes(chord_data['name'])

    # --- Logic & AI ---
    def get_key_offset(self):
        return NOTE_MAP.get(self.key_root_var.get(), 0)

    def update_suggestions_logic(self, last_chord):
        for c_name, btn in self.chord_buttons.items():
            type_key = c_name.split('_')[1]
            orig_color = TYPE_COLORS.get(type_key, "#ffffff")
            btn.configure(bg=C_BTN_DEFAULT_BG, fg=orig_color, font=(FONT_FAMILY, 10))

        key_offset = self.get_key_offset()
        scale_mode = self.key_scale_var.get()
        sug_main = set()
        sug_spice = set()
        advice_text = "理論ロジック: "

        if not last_chord or last_chord == "Rest_Rest":
            if scale_mode == "Major":
                for d, t in [(0, 'Maj'), (5, 'Maj'), (7, 'Maj'), (9, 'Min')]: sug_main.add(f"{ROOTS[(key_offset+d)%12]}_{t}")
                advice_text += "キーの主要コードから開始。"
            else:
                for d, t in [(0, 'Min'), (5, 'Min'), (7, 'Maj'), (8, 'Maj')]: sug_main.add(f"{ROOTS[(key_offset+d)%12]}_{t}")
                advice_text += "キーの主要コードから開始。"
        else:
            try:
                root_str, type_str = last_chord.split('_')
                if root_str not in NOTE_MAP: raise ValueError
                root_idx = NOTE_MAP[root_str]
                degree = (root_idx - key_offset) % 12

                if scale_mode == "Major":
                    if degree == 0:
                        sug_main.update([f"{ROOTS[(key_offset+d)%12]}_{t}" for d,t in [(7,'Maj'),(5,'Maj'),(9,'Min')]])
                        sug_spice.add(f"{ROOTS[(key_offset+1)%12]}_dim7")
                        advice_text += "I度。展開へ。"
                    elif degree == 2:
                        sug_main.add(f"{ROOTS[(key_offset+7)%12]}_Maj")
                        sug_spice.add(f"{ROOTS[(key_offset+7)%12]}_7")
                        advice_text += "ii度。V度へ。"
                    elif degree == 4:
                        sug_main.add(f"{ROOTS[(key_offset+9)%12]}_Min")
                        sug_main.add(f"{ROOTS[(key_offset+5)%12]}_Maj")
                        advice_text += "iii度。vi度へ。"
                    elif degree == 5:
                        sug_main.update([f"{ROOTS[(key_offset+d)%12]}_{t}" for d,t in [(7,'Maj'),(0,'Maj'),(2,'Min')]])
                        sug_spice.add(f"{ROOTS[(key_offset+6)%12]}_dim7")
                        sug_spice.add(f"{ROOTS[(key_offset+5)%12]}_Min")
                        advice_text += "IV度。展開。"
                    elif degree == 7:
                        sug_main.update([f"{ROOTS[(key_offset+d)%12]}_{t}" for d,t in [(0,'Maj'),(9,'Min')]])
                        sug_spice.add(f"{root_str}_aug")
                        sug_spice.add(f"{root_str}_sus4")
                        advice_text += "V度。解決か偽終止。"
                    elif degree == 9:
                        sug_main.update([f"{ROOTS[(key_offset+d)%12]}_{t}" for d,t in [(5,'Maj'),(2,'Min'),(4,'Min')]])
                        advice_text += "vi度。IVやiiへ。"
                else: 
                    if degree == 0:
                        sug_main.update([f"{ROOTS[(key_offset+d)%12]}_{t}" for d,t in [(5,'Min'),(8,'Maj'),(10,'Maj')]])
                        advice_text += "i度。展開へ。"
                    elif degree == 7:
                        sug_main.add(f"{ROOTS[(key_offset+0)%12]}_Min")
                        sug_spice.add(f"{root_str}_aug")
                        advice_text += "V度。i度へ解決。"
                    else:
                        sug_main.add(f"{ROOTS[(key_offset+7)%12]}_Maj")
                        advice_text += "ドミナントを目指して。"

                if type_str in ['7', 'aug', 'sus4']:
                    target_root = ROOTS[(root_idx + 5) % 12]
                    sug_main.add(f"{target_root}_{'Min' if scale_mode=='Minor' else 'Maj'}")
                if type_str in ['dim', 'dim7']:
                    target_root = ROOTS[(root_idx + 1) % 12]
                    sug_main.add(f"{target_root}_{'Min' if scale_mode=='Major' else 'Maj'}")
            except:
                advice_text = "特殊なコードです。"

        for s in sug_main:
            if s in self.chord_buttons: self.chord_buttons[s].configure(bg=C_SUGGEST_BG, fg=C_SUGGEST_FG, font=(FONT_FAMILY, 10, "bold"))
        for s in sug_spice:
            if s in self.chord_buttons: self.chord_buttons[s].configure(bg=C_SPICE_BG, fg=C_SPICE_FG, font=(FONT_FAMILY, 10, "bold"))
        self.advice_label.config(text=advice_text, fg="white")

    def ask_gemini(self):
        if not self.api_key:
            messagebox.showwarning("API Error", "APIキーが設定されていません。")
            return
        if self.is_thinking: return 
        self.is_thinking = True
        self.advice_label.config(text="Geminiが思考中... 🧠", fg=TYPE_COLORS['sus4'])

        current_chords = [item['name'].replace('_', '') for item in self.progression]
        if not current_chords: current_chords = ["(None)"]
        key_info = f"{self.key_root_var.get()} {self.key_scale_var.get()}"
        
        prompt = f"""
        Music Composition Task. Key: {key_info}.
        Chords: {', '.join(current_chords)}
        Task: Suggest 2 next chords.
        1. Main (Standard) 2. Spice (dim7/aug/sus4/modal)
        Format:
        Main: G_7
        Spice: C#_dim7
        Reason: (Reason in Japanese)
        """

        def run_api():
            try:
                model_to_use = self.cached_model_name
                if not model_to_use:
                    available = [m.name for m in genai.list_models() if 'generateContent' in m.supported_generation_methods]
                    for m in available:
                        if 'gemini-1.5-flash' in m: model_to_use = m; break
                    if not model_to_use:
                        for m in available:
                            if 'gemini-pro' in m: model_to_use = m; break
                    if not model_to_use and available: model_to_use = available[0]
                    
                    if not model_to_use: raise Exception("No valid models")
                    self.cached_model_name = model_to_use

                model = genai.GenerativeModel(model_to_use)
                response = model.generate_content(prompt)
                
                if response and response.text:
                    self.after(0, self.parse_gemini_response, response.text)
                else: raise Exception("Empty Response")
            except Exception as e:
                self.after(0, lambda: self.show_api_error(str(e)))
        threading.Thread(target=run_api, daemon=True).start()

    def show_api_error(self, error_msg):
        self.is_thinking = False
        self.advice_label.config(text=f"AI Error: {error_msg[:30]}", fg="red")

    def parse_gemini_response(self, text):
        self.is_thinking = False
        main_raw, spice_raw, reason = None, None, ""
        try:
            lines = text.strip().split('\n')
            for line in lines:
                if "Main:" in line: main_raw = line.split(':')[1].strip()
                if "Spice:" in line: spice_raw = line.split(':')[1].strip()
                if "Reason:" in line: reason = line.split(':')[1].strip()
            
            main_chord = self.normalize_chord_name(main_raw)
            spice_chord = self.normalize_chord_name(spice_raw)
            self.highlight_ai_buttons(main_chord, spice_chord)
            
            d_main = main_chord.replace('_', '') if main_chord else f"({main_raw}?)"
            d_spice = spice_chord.replace('_', '') if spice_chord else f"({spice_raw}?)"
            self.advice_label.config(text=f"🤖 AI: {reason}\n王道:{d_main}  攻め:{d_spice}", fg="#ffccff")
        except Exception:
            self.advice_label.config(text="解析エラー", fg="red")

    def normalize_chord_name(self, chord_str):
        if not chord_str: return None
        s = chord_str.strip().replace(" ", "")
        for flat, sharp in ENHARMONIC_MAP.items():
            if s.startswith(flat): s = s.replace(flat, sharp, 1); break
        
        if "_" not in s:
            if len(s) > 1 and s[1] == '#': root = s[:2]; type_part = s[2:]
            else: root = s[:1]; type_part = s[1:]
            
            if type_part.lower() == "dim7": type_part = "dim7"
            elif type_part.lower() == "dim": type_part = "dim"
            elif type_part.lower() in ["maj", "major"]: type_part = "Maj"
            elif type_part.lower() in ["min", "minor", "m"]: type_part = "Min"
            elif type_part == "7": type_part = "7"
            elif type_part.lower() == "aug": type_part = "aug"
            s = f"{root}_{type_part}"
        if s in self.chord_buttons: return s
        return None

    def highlight_ai_buttons(self, main, spice):
        for c_name, btn in self.chord_buttons.items():
            type_key = c_name.split('_')[1]
            orig_color = TYPE_COLORS.get(type_key, "#ffffff")
            btn.configure(bg=C_BTN_DEFAULT_BG, fg=orig_color, font=(FONT_FAMILY, 10))
        if main and main in self.chord_buttons:
            self.chord_buttons[main].configure(bg=C_SUGGEST_BG, fg=C_SUGGEST_FG, font=(FONT_FAMILY, 10, "bold"))
        if spice and spice in self.chord_buttons:
            self.chord_buttons[spice].configure(bg=C_SPICE_BG, fg=C_SPICE_FG, font=(FONT_FAMILY, 10, "bold"))

    def get_last_selected_chord_name(self):
        if self.selection:
            idx = sorted(list(self.selection))[-1]
            return self.progression[idx]['name']
        if self.progression: return self.progression[-1]['name']
        return None

    def add_chord(self, chord_name):
        label = self.dur_var.get()
        duration = DURATION_OPTIONS.get(label, 1.0)
        self.progression.append({'name': chord_name, 'duration': duration})
        new_index = len(self.progression) - 1
        self.selection.clear() 
        self.selection.add(new_index)
        self.draw_progression()
        self.mark_modified()
        self.update_suggestions_logic(chord_name)

    def load_preset(self):
        preset_name = self.preset_var.get()
        chords = PRESET_PROGRESSIONS.get(preset_name, [])
        label = self.dur_var.get()
        duration = DURATION_OPTIONS.get(label, 1.0)
        for c in chords:
            if c in self.chord_buttons or c == "Rest_Rest":
                self.progression.append({'name': c, 'duration': duration})
            else:
                print(f"Skipped: {c}")
        self.draw_progression()
        self.mark_modified()
        self.update_suggestions_logic(chords[-1] if chords else None)

    def copy_selection(self, event=None):
        if not self.selection: return
        self.clipboard = []
        for i in sorted(list(self.selection)):
            item = self.progression[i]
            data = {'name': item['name'], 'duration': item['duration']}
            if 'voicing' in item: data['voicing'] = list(item['voicing'])
            self.clipboard.append(data)

    def paste_selection(self, event=None):
        if not self.clipboard: return
        for item in self.clipboard: 
            new_item = {'name': item['name'], 'duration': item['duration']}
            if 'voicing' in item: new_item['voicing'] = list(item['voicing'])
            self.progression.append(new_item)
        self.selection.clear()
        start_idx = len(self.progression) - len(self.clipboard)
        for i in range(len(self.clipboard)): self.selection.add(start_idx + i)
        self.draw_progression()
        self.mark_modified()
        if self.progression: self.update_suggestions_logic(self.progression[-1]['name'])

    def delete_selection(self, event=None):
        focused = self.focus_get()
        if isinstance(focused, tk.Entry) or isinstance(focused, ttk.Combobox): return
        if not self.selection: 
            if self.progression:
                self.progression.pop()
                self.draw_progression()
                if self.progression: self.update_suggestions_logic(self.progression[-1]['name'])
                else: self.update_suggestions_logic(None)
                self.mark_modified()
            return
        for i in sorted(list(self.selection), reverse=True): del self.progression[i]
        self.selection.clear()
        self.draw_progression()
        self.mark_modified()
        if self.progression: self.update_suggestions_logic(self.progression[-1]['name'])
        else: self.update_suggestions_logic(None)

    def select_all(self, event=None):
        self.selection = set(range(len(self.progression)))
        self.draw_progression()

    def generate_midi(self, filename):
        mid = MidiFile()
        track = MidiTrack()
        mid.tracks.append(track)
        inst_name = self.inst_var.get()
        prog_num = INSTRUMENT_MAP.get(inst_name, 0)
        track.append(Message('program_change', program=prog_num, time=0))
        try: bpm = float(self.bpm_var.get())
        except: bpm = 120.0
        track.append(MetaMessage('set_tempo', tempo=mido.bpm2tempo(bpm)))
        ticks_per_bar = mid.ticks_per_beat * 4
        
        for item in self.progression:
            notes = self.get_notes(item)
            dur = item['duration']
            vel = 90
            if not notes: 
                wait_ticks = int(ticks_per_bar * dur)
                track.append(Message('note_off', note=0, velocity=0, time=wait_ticks))
                continue
            for n in notes: track.append(Message('note_on', note=n, velocity=vel, time=0))
            wait_ticks = int(ticks_per_bar * dur)
            track.append(Message('note_off', note=notes[0], velocity=vel, time=wait_ticks))
            for n in notes[1:]: track.append(Message('note_off', note=n, velocity=vel, time=0))
        mid.save(filename)
        return filename, bpm

    def play_preview(self):
        if not self.progression or self.is_playing: return
        
        local_temp_dir = os.path.join(os.getcwd(), "temp")
        if not os.path.exists(local_temp_dir): os.makedirs(local_temp_dir)
        
        self.cleanup_temp_files() # Clean old files
        fd, temp_path = tempfile.mkstemp(suffix=".mid", dir=local_temp_dir)
        os.close(fd)
        self.current_temp_file = temp_path
        
        _, bpm = self.generate_midi(temp_path)
        
        try:
            pygame.mixer.music.load(temp_path)
            pygame.mixer.music.play()
            self.is_playing = True
            threading.Thread(target=self.animate, args=(bpm,), daemon=True).start()
        except Exception as e: messagebox.showerror("Error", str(e))

    def animate(self, bpm):
        beat_sec = 60 / bpm
        bar_sec = beat_sec * 4
        for i, item in enumerate(self.progression):
            if not self.is_playing: break
            wait = bar_sec * item['duration']
            self.after(0, self.draw_progression, i)
            time.sleep(wait)
        self.is_playing = False
        self.after(0, self.draw_progression, -1)
        pygame.mixer.music.stop()
        try:
            if self.current_temp_file: pass
        except: pass

    def stop_preview(self):
        self.is_playing = False
        pygame.mixer.music.stop()
        self.draw_progression(-1)

    def reset_progression(self):
        self.new_project()

    def export_midi(self):
        if not self.progression: return
        path = filedialog.asksaveasfilename(defaultextension=".mid", filetypes=[("MIDI", "*.mid")])
        if path:
            self.generate_midi(path)
            messagebox.showinfo("Saved", path)

    def draw_progression(self, active_index=-1):
        self.canvas.delete("all")
        self.block_coords = []
        start_x = 20; y = 40; height = 100; base_px = 80; gap = 2
        current_x = start_x
        for i, item in enumerate(self.progression):
            name = item['name']
            dur = item['duration']
            
            if name == "Rest_Rest":
                root, ctype = "Rest", "Rest"
                base_color = TYPE_COLORS['Rest']
                disp_name = "休"
                text_col = "#888888"
            else:
                parts = name.split('_')
                if len(parts) == 2: root, ctype = parts
                else: root, ctype = "?", "?"
                base_color = TYPE_COLORS.get(ctype, "#555555")
                disp_name = name.replace('_', '\n')
                if dur < 0.25: disp_name = root
                text_col = "white" if ctype not in ['add9', 'sus4'] else "black"

            width = max(20, base_px * dur)
            outline = C_SELECTION if i in self.selection else base_color
            line_width = 3 if i in self.selection else 0
            if i == active_index: fill = "#ffffff"; text_col = "#000000"
            else: fill = base_color
            
            tag_group = f"group_{i}"
            self.canvas.create_rectangle(current_x, y, current_x + width, y + height, fill=fill, outline=outline, width=line_width, tags=tag_group)
            self.canvas.create_text(current_x + width/2, y + height/2, text=disp_name, fill=text_col, font=(FONT_FAMILY, 9, "bold"), justify=tk.CENTER, tags=tag_group)
            self.block_coords.append((current_x, current_x + width))
            current_x += width + gap
        
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

if __name__ == "__main__":
    app = ChordThinkerApp()
    app.mainloop()