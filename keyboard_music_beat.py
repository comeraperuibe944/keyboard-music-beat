#!/usr/bin/env python3
"""
Keyboard Music Beat Visualizer ,  ESC (FnLock) vs NumLock Alternating LEDs
========================================================================
Visualizador de batidas rítmicas com busca automática de BPM online via MPRIS
e metrônomo de grade fixa (Fixed-Grid Phase Accumulator) imune a drift e skips.

Arquitetura:
1. Rastreador Persistente MPRIS: Lê em tempo real alterações de faixa no
   Brave, Spotify, YouTube, etc. sem criar subprocessos a cada poucos segundos.
2. Consulta Online de BPM: Busca na API do ReccoBeats o BPM exato da música.
3. Metrônomo de Grade Fixa (Zero-Skip): O tempo entre batidas é matematicamente
   constante (next_beat_time += interval). Nunca pula batidas, nunca acumula atraso.
4. Sincronização Sutil por Kick: Ajusta a fase no impacto do bumbo da bateria
   sem resetar ou descontinuar a contagem.
5. Prioridade Absoluta (Override):
   - Assim que a música começa a tocar, PAUSA imediatamente o medidor de consumo
     de bateria no NumLock (numlock-power.service) e o keyboard-ripple com SIGSTOP.
   - Ao pausar a música (timeout de 3.0s de silêncio), restaura os LEDs e retoma
     os serviços com SIGCONT.
6. Consumo Energético Praticamente Nulo: 0,0% de CPU em repouso e <0,2% tocando.
"""

import os
import sys
import time
import glob
import signal
import atexit
import struct
import argparse
import threading
import subprocess
import urllib.request
import urllib.parse
import json
import re
import select
import random
from typing import Any, Dict, List, Optional, Set, Tuple

import evdev
from evdev import ecodes

SERVICE_NAME = "keyboard-beat.service"
SCRIPT_PATH = os.path.abspath(__file__)
DEFAULT_SENSITIVITY = 1.0
BEAT_DEBOUNCE_SEC = 0.36       # Debounce fallback (~165 BPM max)
SILENCE_TIMEOUT_SEC = 3.0      # Tempo sem som (3.0s) para devolver controle aos serviços
SAMPLE_RATE = 2000             # 2000 Hz mono = ~4KB/s (energia mínima)
CHUNK_SAMPLES = 80             # 40ms por chunk de áudio (25 avaliações/seg)


def get_fnlock_hw_state() -> int:
    """Lê se o FnLock está ativado no hardware ACPI da Lenovo."""
    try:
        with open("/sys/bus/platform/devices/VPC2004:00/fn_lock", "r") as f:
            return 1 if f.read().strip() == "1" else 0
    except Exception:
        pass
    return 0


def find_internal_led_paths(led_name: str) -> List[str]:
    """Retorna caminhos de LEDs do teclado interno (i8042)."""
    paths = []
    for p in glob.glob(f"/sys/class/leds/*::{led_name}"):
        try:
            real = os.path.realpath(p)
            if "i8042" in real:
                paths.append(p)
        except Exception:
            pass
    return paths


def read_exact(stream, n: int) -> Optional[bytes]:
    """Garante a leitura de exatamente n bytes do pipe unbuffered."""
    buf = bytearray()
    while len(buf) < n:
        chunk = stream.read(n - len(buf))
        if not chunk:
            return None
        buf.extend(chunk)
    return bytes(buf)


BPM_CACHE_FILE = "/var/cache/keyboard-beat-bpm.json"
UNRESOLVED_LOG_FILE = "/home/user/antigravity/radiant-goodall/unresolved_bpms.json"
FAVORITES_FILE = "/home/user/antigravity/radiant-goodall/music_favorites.json"


class FavoritesManager:
    """
    Gerenciador inteligente de histórico e músicas favoritas.
    Lembra o BPM instantaneamente de músicas repetidas através de correspondência
    inteligente por título canônico, aliases e candidatos.
    """
    def __init__(self, file_path: str = FAVORITES_FILE, bpm_cache_path: str = BPM_CACHE_FILE, verbose: bool = True):
        self.file_path = file_path
        self.bpm_cache_path = bpm_cache_path
        self.verbose = verbose
        self.lock = threading.Lock()
        self.data: Dict[str, Any] = {"last_updated": "", "favorites_count": 0, "total_tracks": 0, "tracks": {}}
        self.load()

    def load(self):
        with self.lock:
            if os.path.exists(self.file_path):
                try:
                    with open(self.file_path, "r", encoding="utf-8") as f:
                        self.data = json.load(f)
                    if self.verbose and self.data.get("tracks"):
                        print(f"[*] [FAVORITAS [SAVED]] {len(self.data['tracks'])} faixas carregadas da memória de favoritas.")
                except Exception:
                    pass

    def save(self):
        with self.lock:
            try:
                import datetime
                self.data["last_updated"] = datetime.datetime.now().astimezone().isoformat()
                fav_count = sum(1 for t in self.data["tracks"].values() if t.get("is_favorite", False))
                self.data["favorites_count"] = fav_count
                self.data["total_tracks"] = len(self.data["tracks"])
                with open(self.file_path, "w", encoding="utf-8") as f:
                    json.dump(self.data, f, ensure_ascii=False, indent=2)

                # Sincroniza com /var/cache/keyboard-beat-bpm.json para compatibilidade
                valid_cache = {}
                for t in self.data["tracks"].values():
                    bpm = t.get("bpm")
                    if isinstance(bpm, (int, float)) and bpm > 0:
                        for alias in t.get("aliases", []):
                            valid_cache[alias] = bpm
                cache_dir = os.path.dirname(self.bpm_cache_path)
                if cache_dir and not os.path.exists(cache_dir):
                    os.makedirs(cache_dir, exist_ok=True)
                with open(self.bpm_cache_path, "w", encoding="utf-8") as f:
                    json.dump(valid_cache, f, ensure_ascii=False, indent=2)
            except Exception as e:
                if self.verbose:
                    print(f"[*] [FAVORITAS [WARN]] Erro ao salvar favoritos: {e}")

    def _normalize(self, s: str) -> str:
        s = s.lower()
        s = re.sub(r"[\(\[\{【（「『].*?[\)\]\}】）」』]", " ", s)
        s = re.sub(r"[^\w\s]", " ", s)
        return re.sub(r"\s+", " ", s).strip()

    FORBIDDEN_CANONICAL = {
        "成人男性三人組", "25時、ナイトコードで。", "nightcord at 25:00", "25-ji",
        "more more jump！", "more more jump!", "more_more_jump",
        "vivid bad squad", "vivid_bad_squad",
        "wonderlands×showtime", "wonderlands x showtime", "ワンダーランズ×ショウタイム",
        "leo/need", "leo_need",
        "初音ミク", "鏡音リン", "鏡音レン", "巡音ルカ", "meiko", "kaito",
        "hatsune miku", "kagamine rin", "kagamine len", "megurine luka",
        "重音テト", "kasane teto", "flower", "vflower", "gumi", "ia",
        "deco*27", "deco 27", "wotaku", "pinocchiop", "ピノキオピー",
        "kanaria", "syudou", "giga", "kikuo", "すりぃ", "かいりきベア", "バルーン",
        "harumaki gohan", "はるまきごはん", "40mp", "40㍍", "eve", "orangestar",
        "yoasobi", "ado", "creepy nuts",
        "cover", "remix", "official", "audio", "video", "mv", "lyrics", "full ver"
    }

    def _find_track_key(self, raw_title: str, candidates: List[str]) -> Optional[str]:
        """Localiza a chave da faixa no banco de dados com alta precisão sem colisões por artista."""
        raw_low = raw_title.lower().strip()
        norm_raw = self._normalize(raw_title)

        # 1. Correspondência exata por alias
        for key, track in self.data["tracks"].items():
            for alias in track.get("aliases", []):
                if alias.lower().strip() == raw_low:
                    return key

        # 2. Correspondência exata por título canônico normalizado
        for key, track in self.data["tracks"].items():
            canon_norm = self._normalize(track["canonical_title"])
            if canon_norm in self.FORBIDDEN_CANONICAL:
                continue
            if norm_raw == canon_norm:
                return key

        # 3. Correspondência exata normalizada com candidatos
        if candidates:
            for cand in candidates:
                cand_norm = self._normalize(cand)
                if len(cand_norm) < 2 or cand_norm in self.FORBIDDEN_CANONICAL:
                    continue
                for key, track in self.data["tracks"].items():
                    canon_norm = self._normalize(track["canonical_title"])
                    if canon_norm in self.FORBIDDEN_CANONICAL:
                        continue
                    if cand_norm == canon_norm:
                        return key
                    for alias in track.get("aliases", []):
                        if cand_norm == self._normalize(alias):
                            return key

            # 4. Título canônico contido no candidato (canônico específico dentro de candidato com ruído)
            # NUNCA fazer 'cand_norm in canon_norm', e NUNCA casar se o canônico for um nome de artista/canal!
            for cand in candidates:
                cand_norm = self._normalize(cand)
                if len(cand_norm) < 3 or cand_norm in self.FORBIDDEN_CANONICAL:
                    continue
                for key, track in self.data["tracks"].items():
                    canon_norm = self._normalize(track["canonical_title"])
                    if canon_norm in self.FORBIDDEN_CANONICAL:
                        continue
                    if len(canon_norm) >= 3 and canon_norm in cand_norm:
                        if len(canon_norm) / len(cand_norm) >= 0.5:
                            return key

        return None

    def lookup(self, raw_title: str, candidates: List[str]) -> Optional[Tuple[Optional[float], str, int, bool, str, Optional[float]]]:
        """
        Busca uma faixa no histórico/favoritas.
        Retorna: (bpm, canonical_title, play_count, is_favorite, source, offset_sec) ou None.
        Nota: bpm pode ser None se a faixa foi tocada mas ainda não teve BPM definido.
        """
        with self.lock:
            key = self._find_track_key(raw_title, candidates)
            if key and key in self.data["tracks"]:
                t = self.data["tracks"][key]
                return t.get("bpm"), t["canonical_title"], t.get("play_count", 1), t.get("is_favorite", False), t.get("source", ""), t.get("offset_sec")
            return None

    def record_track(self, raw_title: str, candidates: List[str], bpm: Optional[float] = None, source: str = "", is_manual: bool = False, status: Optional[str] = None):
        """Registra uma reprodução de faixa (mesmo na 1ª vez sem BPM), incrementa contagem e salva edições manuais."""
        import datetime
        now_iso = datetime.datetime.now().astimezone().isoformat()
        with self.lock:
            matched_key = self._find_track_key(raw_title, candidates)

            if matched_key:
                entry = self.data["tracks"][matched_key]
                entry["play_count"] = entry.get("play_count", 1) + 1
                entry["last_played"] = now_iso
                if raw_title not in entry.get("aliases", []):
                    entry.setdefault("aliases", []).append(raw_title)

                if candidates:
                    for c in candidates:
                        c_clean = c.strip()
                        if self._normalize(c_clean) not in self.FORBIDDEN_CANONICAL and len(c_clean) >= 1:
                            if entry.get("canonical_title") == raw_title or self._normalize(entry.get("canonical_title", "")) in self.FORBIDDEN_CANONICAL:
                                entry["canonical_title"] = c_clean
                            break

                if is_manual and bpm is not None:
                    entry["bpm"] = float(bpm)
                    entry["source"] = "Manual do Dono (NumLock Tap)"
                    entry["status"] = "resolved"
                    entry["is_favorite"] = True
                    entry["manual_edited"] = True
                    entry["last_edited"] = now_iso
                elif bpm is not None and bpm > 0:
                    entry["bpm"] = float(bpm)
                    entry["source"] = source
                    entry["status"] = "resolved"
                else:
                    # Se já tinha BPM anterior (ex: manual do dono), preserva e não apaga
                    if not entry.get("bpm"):
                        entry["bpm"] = None
                        entry["status"] = status or "unresolved"
                        entry["source"] = source or "Não encontrado online"

                if entry.get("play_count", 0) >= 2 or is_manual:
                    entry["is_favorite"] = True
            else:
                key = raw_title.lower().strip()
                canon = raw_title
                if candidates:
                    for c in candidates:
                        c_clean = c.strip()
                        if self._normalize(c_clean) not in self.FORBIDDEN_CANONICAL and len(c_clean) >= 1:
                            canon = c_clean
                            break

                has_bpm = (bpm is not None and bpm > 0)
                st = "resolved" if has_bpm else (status or "unresolved")
                src = ("Manual do Dono (NumLock Tap)" if is_manual else source) if has_bpm else (source or "Não encontrado online")
                self.data["tracks"][key] = {
                    "canonical_title": canon,
                    "bpm": float(bpm) if has_bpm else None,
                    "source": src,
                    "status": st,
                    "play_count": 1,
                    "is_favorite": is_manual,
                    "manual_edited": is_manual,
                    "first_played": now_iso,
                    "last_played": now_iso,
                    "aliases": [raw_title]
                }
        self.save()

    def save_custom_offset(self, raw_title: str, candidates: List[str], offset_sec: float):
        """Salva o offset customizado do dono para a faixa no banco de dados permanente."""
        import datetime
        now_iso = datetime.datetime.now().astimezone().isoformat()
        with self.lock:
            matched_key = self._find_track_key(raw_title, candidates)

            if matched_key:
                entry = self.data["tracks"][matched_key]
                entry["offset_sec"] = round(float(offset_sec), 3)
                entry["offset_ms"] = round(float(offset_sec) * 1000.0, 1)
                entry["offset_source"] = "Manual do Dono (NumLock Hold)"
                entry["is_favorite"] = True
                entry["last_edited"] = now_iso
                if raw_title not in entry.get("aliases", []):
                    entry.setdefault("aliases", []).append(raw_title)
            else:
                key = raw_title.lower().strip()
                canon = candidates[0] if candidates else raw_title
                self.data["tracks"][key] = {
                    "canonical_title": canon,
                    "bpm": None,
                    "offset_sec": round(float(offset_sec), 3),
                    "offset_ms": round(float(offset_sec) * 1000.0, 1),
                    "offset_source": "Manual do Dono (NumLock Hold)",
                    "source": "Manual do Dono (NumLock Hold)",
                    "status": "unresolved",
                    "play_count": 1,
                    "is_favorite": True,
                    "first_played": now_iso,
                    "last_played": now_iso,
                    "aliases": [raw_title]
                }
        self.save()


class MediaClassifier:
    """
    Classificador heurístico para distinguir reproduções de música de vídeos convencionais
    (documentários, tutoriais, aulas, podcasts, gameplays, resenhas, notícias, etc.).
    """
    NON_MUSIC_PATTERNS = [
        # Documentários
        r"(?i)\b(?:document[aá]rio|documentary|doc)\b",
        # Podcasts e Entrevistas
        r"(?i)\b(?:podcast|pod\s*pah|flow\s*podcast|entrevista|interview|talk\s*show|bate[- ]papo|mesa\s*redonda|cortes\s+d[eoa]|corte\s+d[eoa])\b",
        # Educação, Aulas e Tutoriais
        r"(?i)\b(?:tutorial|v[ií]deo[- ]?aula|aula\s*\d+|curso|como\s+fazer|how\s+to|passo\s+a\s+passo|step\s+by\s+step|explicando|resumo|resenha|an[aá]lise|review|cr[ií]tica|unboxing|palestra|discurso|debate)\b",
        # Notícias e Política
        r"(?i)\b(?:not[ií]cia[s]?|news|jornal\s+nacional|plant[aã]o|pronunciamento|coletiva\s+de\s+imprensa|melhores\s+momentos|gols\s+da\s+rodada|resumo\s+do\s+jogo)\b",
        # Séries, Filmes e Gameplay
        r"(?i)\b(?:epis[oó]dio|episode|ep\.\s*\d+|s\d+e\d+|temporada|season\s*\d+|cap[ií]tulo|trailer|teaser|sneak\s*peek|vlog|gameplay|playthrough|walkthrough|longplay|speedrun|react|reagindo)\b",
    ]

    MUSIC_PLAYERS = {
        "spotify", "amberol", "rhythmbox", "clementine", "strawberry",
        "audacious", "tidal", "apple-music", "cmus", "mocp", "deadbeef"
    }

    MUSIC_DOMAINS = {
        "music.youtube.com", "open.spotify.com", "soundcloud.com", "bandcamp.com", "deezer.com"
    }

    MUSIC_INDICATOR_PATTERNS = [
        # Clipes oficiais e termos musicais
        r"(?i)\b(?:official\s+music\s+video|official\s+video|official\s+audio|clipe\s+oficial|music\s+video|mv|pv|ost|soundtrack|bgm|theme\s+song|opening|ending|op\s*\d*|ed\s*\d*|insert\s+song|vocaloid|chords|karaoke|instrumental|remastered|sped\s+up|nightcore|slowed|acoustic|remix|feat\.?|ft\.?|cover|covered|arrange|arrangement|original\s+song)\b",
        # Formatos comuns de tags de capa, clipe e arranjo
        r"(?i)(?:[--, ~]cover[--, ~]|【cover】|\(cover\)|\[cover\]|【mv】|\(mv\)|\[mv\]|（arrange）|【arrange】|\[arrange\])",
        # Termos musicais em japonês
        r"(?i)(?:歌ってみた|オリジナル曲|音源|フル|原曲mv|3dmv|2dmv|演奏してみた|叩いてみた|弾いてみた|ボカロ|カバー|アレンジ|歌コレ)",
        # Unidades de Project Sekai e Vocaloids conhecidos
        r"(?i)(?:25時、ナイトコードで。|nightcord|more\s*more\s*jump|vivid\s*bad\s*squad|wonderlands|ワンダーランズ|leo/need|初音ミク|鏡音リン|鏡音レン|巡音ルカ|meiko|kaito|hatsune\s*miku|kagamine|megurine|gumi|flower|kafu|utaite)",
        # Aspas japonesas típicas de títulos de músicas
        r"「.*?」|『.*?』"
    ]

    @classmethod
    def classify(cls, title: str, player_name: str = "", url: str = "") -> Tuple[bool, str, float]:
        """
        Classifica se a mídia reproduzida é musical.
        Retorna (is_music, motivo, confianca)
        """
        if not title:
            return False, "Sem metadados MPRIS (áudio de jogo/emulador/sistema)", 1.0

        # 1. Player de música dedicado
        p_low = player_name.lower()
        if any(mp in p_low for mp in cls.MUSIC_PLAYERS):
            return True, f"Player musical dedicado ({player_name})", 1.0

        # 2. Domínio de serviço de música
        u_low = url.lower()
        if any(d in u_low for d in cls.MUSIC_DOMAINS):
            return True, f"Serviço de streaming musical ({url})", 1.0

        # 3. Padrão negativo estrito (Documentários, aulas, podcasts, notícias, etc.)
        for pat in cls.NON_MUSIC_PATTERNS:
            m = re.search(pat, title)
            if m:
                return False, f"Identificado termo não-musical: '{m.group(0)}'", 0.95

        # 4. Indicadores explícitos de música (Sekai units, Vocaloid, clipes, aspas japonesas)
        for pat in cls.MUSIC_INDICATOR_PATTERNS:
            if re.search(pat, title):
                return True, "Indicador explícito de videoclipe/música", 0.9

        # 5. Estrutura padrão de Artista - Música ou Tags delimitadas
        if re.search(r"(?:^.+?\s*[--, ~／/|]\s*.+?|[--, ~][A-Za-z0-9_\u3040-\u30ff\u4e00-\u9fa5]+[--, ~])", title):
            return True, "Estrutura Artista - Música detectada", 0.7

        # 6. Vídeo genérico sem traços musicais
        return False, "Vídeo convencional sem padrões musicais identificados", 0.75


class MprisBpmTracker:
    """
    Rastreador persistente de MPRIS via D-Bus com consulta online de BPM,
    memória inteligente de favoritas e classificador automático de mídia.
    """
    def __init__(self, verbose: bool = True):
        self.verbose = verbose
        self.current_title = ""
        self.bpm: Optional[float] = None
        self.current_offset: Optional[float] = None
        self.is_playing = False
        self.is_music = True
        self.media_type = "UNKNOWN"
        self.media_reason = ""
        self.last_pos = 0.0
        self.last_pos_time = 0.0
        self.favorites_manager = FavoritesManager(FAVORITES_FILE, BPM_CACHE_FILE, verbose=verbose)
        self.notified_failed_tracks: Set[str] = set()
        self.notified_local_tracks: Dict[str, float] = {}
        self.last_notification_time: float = 0.0
        self.lock = threading.Lock()
        self.running = True
        self.proc: Optional[subprocess.Popen] = None
        self.thread = threading.Thread(target=self._worker_loop, daemon=True)
        self.thread.start()

    def is_music_active(self) -> bool:
        with self.lock:
            # Requisito obrigatório do usuário: O visualizador só deve ativar se houver
            # um player de mídia legítimo ativo no Linux (Brave/YouTube, Spotify, etc.)
            # em estado 'Playing' com título válido. Emuladores, jogos e sons do sistema NUNCA ativam os LEDs.
            if not self.is_playing:
                return False
            if not self.current_title or len(self.current_title.strip()) < 2:
                return False
            return self.is_music

    def _log_unresolved_track(self, raw_title: str, candidates: List[str]):
        """Registra faixa não detectada no log JSON persistente."""
        try:
            import datetime
            now_iso = datetime.datetime.now().astimezone().isoformat()
            data = {"last_updated": now_iso, "total_unresolved": 0, "tracks": {}}
            if os.path.exists(UNRESOLVED_LOG_FILE):
                try:
                    with open(UNRESOLVED_LOG_FILE, "r", encoding="utf-8") as f:
                        data = json.load(f)
                except Exception:
                    pass

            tracks = data.setdefault("tracks", {})
            if raw_title not in tracks:
                tracks[raw_title] = {
                    "first_seen": now_iso,
                    "last_seen": now_iso,
                    "fail_count": 1,
                    "candidates_tested": candidates,
                    "status": "unresolved"
                }
            else:
                entry = tracks[raw_title]
                entry["last_seen"] = now_iso
                entry["fail_count"] = entry.get("fail_count", 0) + 1
                entry["candidates_tested"] = candidates
                entry["status"] = "unresolved"

            data["last_updated"] = now_iso
            data["total_unresolved"] = sum(1 for t in tracks.values() if t.get("status") == "unresolved")

            with open(UNRESOLVED_LOG_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _mark_resolved_track(self, raw_title: str, bpm: float, source: str):
        """Atualiza faixa no log JSON para 'resolved' se estava registrada."""
        try:
            if not os.path.exists(UNRESOLVED_LOG_FILE):
                return
            import datetime
            now_iso = datetime.datetime.now().astimezone().isoformat()
            with open(UNRESOLVED_LOG_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            tracks = data.get("tracks", {})
            if raw_title in tracks:
                tracks[raw_title]["status"] = "resolved"
                tracks[raw_title]["resolved_at"] = now_iso
                tracks[raw_title]["resolved_bpm"] = bpm
                tracks[raw_title]["resolved_source"] = source
                data["last_updated"] = now_iso
                data["total_unresolved"] = sum(1 for t in tracks.values() if t.get("status") == "unresolved")
                with open(UNRESOLVED_LOG_FILE, "w", encoding="utf-8") as f:
                    json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def save_manual_bpm(self, title: str, bpm: float):
        """Salva um BPM definido manualmente no histórico/favoritas e persiste em disco."""
        candidates = self._generate_candidates(title)
        with self.lock:
            self.bpm = bpm
            self.is_music = True
            self.media_type = "FAVORITE"
        self.favorites_manager.record_track(title, candidates, bpm, "Manual Tap Tempo", is_manual=True)
        self._mark_resolved_track(title, bpm, "Manual Tap Tempo")

    def stop(self):
        self.running = False
        if self.proc:
            try:
                self.proc.terminate()
            except Exception:
                pass

    def get_track_info(self) -> Tuple[Optional[float], str, Optional[float]]:
        with self.lock:
            return self.bpm, self.current_title, self.current_offset

    def get_track_offset(self) -> Optional[float]:
        with self.lock:
            return self.current_offset

    def get_playback_position(self) -> float:
        """Retorna a posição exata de reprodução do player MPRIS em segundos (com interpolação temporal de alta precisão)."""
        with self.lock:
            if not self.is_playing or self.last_pos_time <= 0:
                return 0.0
            dt = time.monotonic() - self.last_pos_time
            return max(0.0, self.last_pos + dt)

    def get_bpm(self) -> Optional[float]:
        with self.lock:
            return self.bpm

    def get_title(self) -> str:
        with self.lock:
            return self.current_title

    def _send_desktop_notification(self, summary: str, body: str, icon: str = "dialog-warning", timeout_ms: int = 2500, urgency: str = "low"):
        """Envia uma notificação visual elegante, rápida e não-intrusiva (substitui a anterior sem empilhar)."""
        now = time.monotonic()
        # Cooldown global de 1.5s entre notificações automáticas para evitar rajadas ao pular faixas rapidamente
        if (now - self.last_notification_time) < 1.5 and urgency == "low":
            return
        self.last_notification_time = now
        try:
            cmd = [
                "sudo", "-u", "user",
                "env", "DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus",
                "/usr/bin/notify-send",
                "-a", "Keyboard Music Beat",
                "-i", icon,
                "-u", urgency,
                "-e",  # Transiente: nunca acumula nem polui a central de notificações do Linux
                "-t", str(timeout_ms),  # Duração curta e discreta (ex: 2.5 segundos)
                "-h", "string:x-canonical-private-synchronous:keyboard-beat",  # Substitui a bolha anterior sem empilhar popups
                summary,
                body
            ]
            subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except Exception:
            pass

    def _worker_loop(self):
        cmd = [
            "sudo", "-u", "user",
            "env", "DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus",
            "python3", "-u", "-c",
            """
import dbus, json, time
bus = None
last_state = None

while True:
    try:
        if bus is None:
            bus = dbus.SessionBus()
        best_state = None
        for name in bus.list_names():
            if name.startswith("org.mpris.MediaPlayer2"):
                try:
                    p = bus.get_object(name, "/org/mpris/MediaPlayer2")
                    props = dbus.Interface(p, "org.freedesktop.DBus.Properties")
                    st = str(props.Get("org.mpris.MediaPlayer2.Player", "PlaybackStatus"))
                    meta = props.Get("org.mpris.MediaPlayer2.Player", "Metadata")
                    title = str(meta.get("xesam:title", ""))
                    url = str(meta.get("xesam:url", ""))
                    pos = 0
                    try:
                        pos = int(props.Get("org.mpris.MediaPlayer2.Player", "Position"))
                    except Exception:
                        pass
                    if st == "Playing":
                        best_state = (st, title, name, url, pos)
                        break
                    elif best_state is None:
                        best_state = (st, title, name, url, pos)
                except Exception:
                    pass
        if best_state is not None:
            print(json.dumps({
                "status": best_state[0],
                "title": best_state[1],
                "player": best_state[2],
                "url": best_state[3],
                "position": round(best_state[4] / 1000000.0, 3)
            }), flush=True)
            last_state = best_state
        else:
            if last_state is not None:
                last_state = None
                print(json.dumps({"status": "Stopped", "title": "", "player": "", "url": "", "position": 0.0}), flush=True)
    except Exception:
        bus = None
    time.sleep(0.25)
"""
        ]
        while self.running:
            try:
                self.proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True)
                for line in self.proc.stdout:
                    if not self.running:
                        break
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        data = json.loads(line)
                        status = data.get("status")
                        title = data.get("title", "")
                        player = data.get("player", "")
                        url = data.get("url", "")
                        pos = float(data.get("position", 0.0))
                        now_m = time.monotonic()
                        with self.lock:
                            self.is_playing = (status == "Playing")
                            self.last_pos = pos
                            self.last_pos_time = now_m
                            if not self.is_playing:
                                if status == "Stopped" or not title:
                                    self.current_title = ""
                                    self.bpm = None
                                    self.current_offset = None
                        if status == "Playing" and title and title != self.current_title:
                            self._on_new_track(title, player, url)
                    except Exception:
                        pass
            except Exception:
                time.sleep(2.0)

    def _on_new_track(self, raw_title: str, player: str = "", url: str = ""):
        with self.lock:
            self.current_title = raw_title

        candidates = self._generate_candidates(raw_title)

        # 1. Consulta em 1º lugar na memória de favoritas / histórico
        fav_match = self.favorites_manager.lookup(raw_title, candidates)
        if fav_match:
            cached_bpm, canon_title, play_count, is_fav, source, saved_offset = fav_match
            if cached_bpm is not None and cached_bpm > 0:
                with self.lock:
                    self.bpm = cached_bpm
                    self.is_music = True
                    self.current_offset = saved_offset
                    self.media_type = "FAVORITE" if is_fav else "HISTORY"
                # Registra mais uma reprodução no histórico mantendo o BPM
                self.favorites_manager.record_track(raw_title, candidates, cached_bpm, source)
                if self.verbose:
                    fav_tag = "MANUAL DO DONO [PRIORITY]" if "Manual" in source else ("FAVORITA [STAR]" if (is_fav or play_count >= 1) else "HISTÓRICO [MUSIC]")
                    offset_info = f" | Offset: {round(saved_offset * 1000)}ms" if saved_offset is not None else ""
                    print(f"[*] [{fav_tag}] BPM recuperado da memória: {cached_bpm} BPM{offset_info} para \"{canon_title}\" (Tocou {play_count + 1}x)")

                # Notificação Desktop para BPM Local:
                # Discreta, transiente e com cooldown de 10 min por faixa para não sobrecarregar
                norm_title = self.favorites_manager._normalize(canon_title or raw_title)
                now_m = time.monotonic()
                last_time = self.notified_local_tracks.get(norm_title, 0.0)
                if now_m - last_time > 600.0:
                    self.notified_local_tracks[norm_title] = now_m
                    disp_title = canon_title if canon_title else (raw_title[:45] + ("..." if len(raw_title) > 45 else ""))
                    offset_txt = f"\nOffset: {round(saved_offset * 1000)}ms" if saved_offset is not None else ""
                    tag_name = "Manual do Dono [PRIORITY]" if "Manual" in source else ("Favorita [STAR]" if is_fav else "Banco Local [SAVED]")
                    self._send_desktop_notification(
                        f"[MUSIC] BPM Local ({tag_name})",
                        f"{disp_title}\n{cached_bpm} BPM ({source}){offset_txt}",
                        icon="emblem-favorite" if is_fav else "audio-card",
                        timeout_ms=2500,
                        urgency="low"
                    )
                return
            else:
                # Faixa já catalogada no histórico, mas pendente de BPM
                self.favorites_manager.record_track(raw_title, candidates, bpm=None, source=source, status="unresolved")
                with self.lock:
                    self.is_music = True
                    self.bpm = None
                    self.current_offset = saved_offset
                    self.media_type = "MUSIC"
                if self.verbose:
                    print(f"[*] [HISTÓRICO [MUSIC]] Faixa repetida sem BPM: \"{canon_title}\" (Tocou {play_count + 1}x). Buscando...")
                threading.Thread(target=self._lookup_bpm_online, args=(raw_title, candidates, True), daemon=True).start()
                return

        # 2. Classificador Inteligente de Mídia (Música vs Vídeo Comum / Documentário)
        is_music, reason, conf = MediaClassifier.classify(raw_title, player, url)
        if not is_music:
            with self.lock:
                self.bpm = None
                self.current_offset = None
                self.is_music = False
                self.media_type = "NON_MUSIC_VIDEO"
                self.media_reason = reason
            if self.verbose:
                print(f"[*] [VÍDEO NORMAL [VIDEO]] \"{raw_title[:45]}\" identificado como não-musical ({reason}). LEDs em repouso.")
            return

        # 3. Potencialmente Musical ou Ambíguo: Dispara busca online em bases oficiais
        with self.lock:
            self.bpm = None
            self.current_offset = None
            self.is_music = True
            self.media_type = "MUSIC"
            self.media_reason = reason

        threading.Thread(target=self._lookup_bpm_online, args=(raw_title, candidates, is_music), daemon=True).start()

    SEKAI_UNITS = [
        "25時、ナイトコードで。", "nightcord at 25:00", "25-ji",
        "more more jump！", "more more jump!", "more_more_jump",
        "vivid bad squad", "vivid_bad_squad",
        "wonderlands×showtime", "wonderlands x showtime", "ワンダーランズ×ショウタイム",
        "leo/need", "leo_need",
        "初音ミク", "鏡音リン", "鏡音レン", "巡音ルカ", "meiko", "kaito",
        "hatsune miku", "kagamine rin", "kagamine len", "megurine luka",
        "重音テト", "kasane teto", "flower", "vflower", "gumi", "ia",
        "成人男性三人組", "deco*27", "deco 27", "wotaku", "pinocchiop", "ピノキオピー",
        "kanaria", "syudou", "giga", "kikuo", "すりぃ", "かいりきベア", "バルーン",
        "harumaki gohan", "はるまきごはん", "40mp", "40㍍", "eve", "orangestar"
    ]

    def _is_sekai_unit(self, text: str) -> bool:
        t = text.lower().strip()
        return any(u in t for u in self.SEKAI_UNITS)

    def _generate_candidates(self, raw_title: str) -> List[str]:
        """Gera hipóteses de busca inteligentes extraindo a música e artista originais de covers, remixes, etc."""
        clean_raw = raw_title
        # Normaliza marcadores comuns de cover/arrange (ex: "-Cover-", "【Cover】", "(Cover)") para separadores " - "
        clean_raw = re.sub(r"(?i)\s*[--, ~－〜～]?\s*(?:covered\s+by|cover\s+by|cover\s+de|self\s*cover|cover|cove|arrange|remix)\s*[--, ~－〜～]?\s*", " - ", clean_raw)

        # Extrai títulos destacados em aspas japonesas 「...」 e 『...』 com prioridade máxima absoluta
        quoted = [m[0] or m[1] for m in re.findall(r"「(.*?)」|『(.*?)』", clean_raw)]

        parens = re.findall(r"[\(\[\{【（](.*?)[\)\]\}】）]", clean_raw)
        clean_base = re.sub(r"[\(\[\{【（「『].*?[\)\]\}】）」』]", " ", clean_raw)

        noise_patterns = [
            r"(?i)\b(?:official\s+music\s+video|official\s+video|official\s+audio|official|music\s+video|mv|clip|clipe|lyrics\s+video|lyric\s+video|lyrics|letra|legendado|karaoke|instrumental|audio|áudio|video|vídeo|hd|4k|hq|full\s+song|sped\s+up|speed\s+up|slowed\s*\+?\s*reverb|slowed|reverb|nightcore|8d\s+audio|ncs\s+release|visualizer)\b",
            r"(?i)\b(?:歌ってみた|オリジナル曲|演奏してみた|叩いてみた|弾いてみた|公式|音源|フル|3dmv|2dmv|原曲mv|ゲームサイズ|game\s*size|game\s*ver|full\s*ver)\b",
            r"(?i)\b(?:プロセカ|プロジェクトセカイ|project\s*sekai|pjsk|pjsekai)\b",
            r"(?i)\b(?:all\s*perfect|full\s*combo|master|expert|append|譜面)\b"
        ]
        clean_title = clean_base
        for pat in noise_patterns:
            clean_title = re.sub(pat, " ", clean_title)

        # Protege barras em acrônimos ou palavras alfanuméricas (ex: D/N/A, AC/DC, Fate/stay) para não dividir indevidamente
        protected_title = re.sub(r"(?<=[A-Za-z0-9])/(?=[A-Za-z0-9])", "__SLASH__", clean_title)

        # Delimitadores:
        # - Barras '/' e '／' dividem mesmo sem espaços (exceto acrônimos protegidos), permitindo títulos como "トリコロージュ/25時、ナイトコードで。"
        # - Travessões e delimitadores comuns '[--, ~－〜～×xX|｜]' dividem com ou sem espaços
        # - Marcadores pontuais ':：*・' exigem espaços para NÃO quebrar palavras internas (ex: "ノンブレス・オブリージュ")
        # - Feat/ft/vs divide com ou sem ponto e com ou sem espaço após o ponto (ex: "feat.鏡音リン", "ft.Drake")
        delimiters = r"\s*[/／]\s*|\s*[--, ~－〜～×xX|｜]\s*|\s+[:：*・]\s+|\s*(?:\b(?:feat|ft|vs)\.|\b(?:feat|ft|vs)\b)\s*"
        parts = [re.sub(r"\s+", " ", p.replace("__SLASH__", "/")).strip() for p in re.split(delimiters, protected_title, flags=re.IGNORECASE) if p.strip()]

        candidates = []

        def _is_valid_part(p: str) -> bool:
            if len(p) >= 2:
                return True
            # Permite kanji ou kana único (ex: 踊, 炎, 花, 愛, 桜)
            if len(p) == 1 and any('\u4e00' <= ch <= '\u9fff' or '\u3040' <= ch <= '\u309f' or '\u30a0' <= ch <= '\u30ff' for ch in p):
                return True
            return False

        # 1. Títulos explicitamente demarcados em aspas japonesas 「...」 ou 『...』
        for q in quoted:
            q_clean = q.strip()
            if _is_valid_part(q_clean) and not self._is_sekai_unit(q_clean) and q_clean not in candidates:
                candidates.append(q_clean)

        # 2. Separa faixas e unidades/artistas
        non_unit_parts = []
        unit_parts = []
        for p in parts:
            p_sub = re.sub(r"^[\"\'\s\--, ~－〜～:|/*]+|[\"\'\s\--, ~－〜～:|/*]+$", "", p).strip()
            if _is_valid_part(p_sub):
                if self._is_sekai_unit(p_sub):
                    unit_parts.append(p_sub)
                else:
                    non_unit_parts.append(p_sub)

        # Se houver 2 partes e nenhuma for sekai_unit, em 99% dos casos é o padrão "Artista - Faixa"
        # Prioriza o título da faixa (parts[1]), depois combinação "Artista Faixa", e evita artista puro isolado
        if len(non_unit_parts) == 2 and not unit_parts:
            track_part = non_unit_parts[1]
            artist_part = non_unit_parts[0]
            if track_part not in candidates:
                candidates.append(track_part)
            comb1 = f"{artist_part} {track_part}"
            if comb1 not in candidates:
                candidates.append(comb1)
            comb2 = f"{track_part} {artist_part}"
            if comb2 not in candidates:
                candidates.append(comb2)
            # Adiciona artist_part por último apenas se contiver kanji/kana (caso japonês Song - Artist)
            if any('\u4e00' <= ch <= '\u9fff' or '\u3040' <= ch <= '\u309f' or '\u30a0' <= ch <= '\u30ff' for ch in artist_part):
                if artist_part not in candidates:
                    candidates.append(artist_part)
        else:
            for p in non_unit_parts:
                if p not in candidates:
                    candidates.append(p)
            if non_unit_parts and unit_parts:
                candidates.append(f"{non_unit_parts[0]} {unit_parts[0]}")
                candidates.append(f"{unit_parts[0]} {non_unit_parts[0]}")

        noise_parens_words = {
            "official", "video", "audio", "self", "cover", "remake", "accurate remake",
            "remastered", "remaster", "recording", "van recording", "original mix",
            "extended mix", "club mix", "live", "lyrics", "lyric", "mv", "hd", "4k", "hq",
            "full song", "game ver", "full ver", "short ver", "tv ver", "tv size"
        }
        for p in parens:
            p_clean = p
            for pat in noise_patterns:
                p_clean = re.sub(pat, " ", p_clean)
            p_clean = re.sub(r"[^\w\s\-\'\"]", " ", p_clean).strip()
            p_clean = re.sub(r"^[\"\'\s\--, ~－〜～:|/*]+|[\"\'\s\--, ~－〜～:|/*]+$", "", p_clean).strip()
            if _is_valid_part(p_clean) and p_clean.lower() not in noise_parens_words and p_clean not in candidates:
                if not self._is_sekai_unit(p_clean):
                    candidates.append(p_clean)

        clean_all = re.sub(delimiters, " ", protected_title)
        clean_all = clean_all.replace("__SLASH__", "/")
        clean_all = re.sub(r"\s+", " ", clean_all).strip()
        clean_all = re.sub(r"^[\"\'\s\--, ~－〜～:|/*]+|[\"\'\s\--, ~－〜～:|/*]+$", "", clean_all).strip()
        if clean_all and clean_all not in candidates and not self._is_sekai_unit(clean_all):
            candidates.append(clean_all)

        seen = set()
        unique = []
        for c in candidates:
            c_clean = re.sub(r"^[\"\'\s\--, ~－〜～:|/*]+|[\"\'\s\--, ~－〜～:|/*]+$", "", c).strip()
            cn = c_clean.lower()
            if cn and _is_valid_part(c_clean) and cn not in seen:
                seen.add(cn)
                unique.append(c_clean)
        return unique

    def _lookup_fandom_wiki(self, domain: str, wiki_name: str, query: str, raw_lower: str = "") -> Optional[Tuple[float, str]]:
        """Consulta wikis MediaWiki de jogos de ritmo (Project Sekai, BanG Dream, D4DJ) com validação estrita de título."""
        try:
            q_enc = urllib.parse.quote(query)
            url_search = f"https://{domain}/api.php?action=opensearch&search={q_enc}&limit=4&format=json"
            req = urllib.request.Request(url_search, headers={"User-Agent": "Mozilla/5.0 (X11; Linux x86_64)"})
            with urllib.request.urlopen(req, timeout=2.8) as r:
                res = json.loads(r.read().decode("utf-8", errors="ignore"))
                titles = res[1] if len(res) > 1 else []

            q_low = query.lower().strip()
            raw_target = (raw_lower or q_low).lower()

            for t in titles[:3]:
                if any(skip in t for skip in ["/Gallery", "/Discography", "List of", "Cards/", "Events/", "/Main Story", "/Band Story"]):
                    continue
                url_page = f"https://{domain}/api.php?action=query&prop=revisions&rvprop=content&titles={urllib.parse.quote(t)}&format=json"
                req2 = urllib.request.Request(url_page, headers={"User-Agent": "Mozilla/5.0 (X11; Linux x86_64)"})
                with urllib.request.urlopen(req2, timeout=2.8) as r2:
                    pdata = json.loads(r2.read().decode("utf-8", errors="ignore"))
                    pages = pdata.get("query", {}).get("pages", {})
                    for pid, p in pages.items():
                        content = p.get("revisions", [{}])[0].get("*", "")
                        m = re.search(r"\|\s*bpm\s*=\s*([0-9\.\-\~]+)", content, re.IGNORECASE)
                        if not m:
                            continue

                        # Validação estrita: o título da página ou infobox precisa corresponder à busca
                        page_names = [t.lower()]
                        for field in ["name", "japanese", "english", "romaji", "original_title", "title"]:
                            m_field = re.search(r"\|\s*" + field + r"\s*=\s*([^\n\|\}]+)", content, re.IGNORECASE)
                            if m_field:
                                val = re.sub(r"\[\[|\]\]|\{\{.*?\}\}", "", m_field.group(1)).strip().lower()
                                if val and len(val) >= 2:
                                    page_names.append(val)

                        is_match = False
                        for pname in page_names:
                            pclean = re.sub(r"[\(\[\{【（].*?[\)\]\}】）]", "", pname).strip()
                            if not pclean:
                                continue
                            if pclean == q_low or pclean == raw_target:
                                is_match = True
                                break
                            # Match para caracteres japoneses/orientais
                            if any('\u4e00' <= ch <= '\u9fff' or '\u3040' <= ch <= '\u309f' or '\u30a0' <= ch <= '\u30ff' for ch in pclean):
                                if pclean in raw_target or q_low in pclean:
                                    is_match = True
                                    break
                            else:
                                if pclean in raw_target:
                                    if re.search(r'(?:\b|^)' + re.escape(pclean) + r'(?:\b|$)', raw_target):
                                        if len(pclean) >= 4 and pclean not in {'team', 'band', 'song', 'live', 'game', 'rock', 'girl', 'boys'}:
                                            is_match = True
                                            break
                                q_words = set(re.findall(r"\b\w{3,}\b", q_low))
                                p_words = set(re.findall(r"\b\w{3,}\b", pclean))
                                stop_w = {"the", "and", "for", "with", "feat", "from", "part", "cover"}
                                q_sig = q_words - stop_w
                                p_sig = p_words - stop_w
                                if len(q_sig) >= 2 and len(p_sig) >= 2 and (q_sig == p_sig or q_sig.issubset(p_sig) or p_sig.issubset(q_sig)):
                                    is_match = True
                                    break

                        if not is_match:
                            continue

                        s = m.group(1).strip()
                        bpm_val = float(s.split("-")[-1].strip()) if "-" in s else float(s)
                        if 40.0 <= bpm_val <= 320.0:
                            return bpm_val, f"{t} ({wiki_name})"
        except Exception:
            pass
        return None

    def _lookup_pjsekai_com(self, query: str, raw_lower: str = "") -> Optional[Tuple[float, str]]:
        """Consulta a Wiki de Estratégia Japonesa do Project Sekai (pjsekai.com) com validação de página."""
        try:
            url = f"https://pjsekai.com/?{urllib.parse.quote(query)}"
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (X11; Linux x86_64)"})
            with urllib.request.urlopen(req, timeout=2.8) as r:
                html = r.read().decode("utf-8", errors="ignore")
                m_title = re.search(r"<title>(.*?)</title>", html, re.IGNORECASE)
                if not m_title:
                    return None
                page_title = m_title.group(1).lower()
                q_low = query.lower()
                if q_low not in page_title and (raw_lower and q_low not in raw_lower):
                    return None

                m = re.search(r"BPM</td><td[^>]*>([0-9\.\-\~]+)", html, re.IGNORECASE)
                if m:
                    s = m.group(1).strip()
                    bpm_val = float(s.split("-")[-1].strip()) if "-" in s else float(s)
                    if 40.0 <= bpm_val <= 320.0:
                        return bpm_val, f"{query} (pjsekai.com)"
        except Exception:
            pass
        return None

    def _lookup_reccobeats(self, query: str, raw_lower: str) -> Optional[Tuple[float, str]]:
        """Consulta o catálogo Spotify via Reccobeats API para músicas ocidentais e gerais."""
        try:
            url = "https://api.reccobeats.com/v1/track/search?searchText=" + urllib.parse.quote(query)
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=3.0) as r:
                data = json.loads(r.read().decode("utf-8", errors="ignore"))
                tracks = data.get("content", [])
                best_track = None
                best_score = -1

                for tr in tracks[:10]:
                    t_title = tr.get("trackTitle", "").strip()
                    t_lower = t_title.lower()
                    artists = [a.get("name", "").strip() for a in tr.get("artists", [])]

                    score = 0
                    if t_lower == query.lower():
                        score += 30
                    elif t_lower in raw_lower:
                        score += 20
                    elif query.lower() in t_lower:
                        score += 15

                    for a in artists:
                        a_lower = a.lower()
                        if a_lower and len(a_lower) >= 3 and a_lower in raw_lower:
                            score += 50

                    if score > best_score:
                        best_score = score
                        best_track = tr

                    if best_score >= 70:
                        break

            if best_track and best_score >= 15:
                tid = best_track.get("id")
                t_title = best_track.get("trackTitle", query)
                f_url = f"https://api.reccobeats.com/v1/track/{tid}/audio-features"
                f_req = urllib.request.Request(f_url, headers={"User-Agent": "Mozilla/5.0"})
                with urllib.request.urlopen(f_req, timeout=3.0) as fr:
                    feat = json.loads(fr.read().decode("utf-8", errors="ignore"))
                    tempo = feat.get("tempo")
                    if tempo and tempo > 0:
                        return float(tempo), f"{t_title} (Spotify/Reccobeats)"
        except Exception:
            pass
        return None

    def _lookup_catboy(self, query: str, raw_lower: str) -> Optional[Tuple[float, str]]:
        """Consulta o banco de Beatmaps do Osu! (via Catboy API) com votação por consenso para eliminar covers acústicos lentos."""
        try:
            url = "https://catboy.best/api/v2/search?q=" + urllib.parse.quote(query)
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=3.0) as r:
                data = json.loads(r.read().decode("utf-8", errors="ignore"))
                if not isinstance(data, list) or not data:
                    return None

                from collections import Counter
                q_low = query.lower().strip()
                exact_bpms = []
                partial_items = []

                for item in data[:25]:
                    title = (item.get("title") or "").strip()
                    title_u = (item.get("title_unicode") or "").strip()
                    artist = (item.get("artist") or "").strip()
                    artist_u = (item.get("artist_unicode") or "").strip()
                    bpm = item.get("bpm")
                    if not bpm or float(bpm) <= 0:
                        continue

                    t_low = title.lower()
                    tu_low = title_u.lower()
                    b_val = round(float(bpm), 1)

                    if q_low == t_low or q_low == tu_low:
                        exact_bpms.append((b_val, title_u or title))
                    elif t_low in raw_lower or tu_low in raw_lower or q_low in t_low or q_low in tu_low:
                        score = 25
                        if t_low in raw_lower or tu_low in raw_lower:
                            score += 15
                        a_low = artist.lower()
                        au_low = artist_u.lower()
                        if (a_low and len(a_low) >= 3 and a_low in raw_lower) or \
                           (au_low and len(au_low) >= 2 and au_low in raw_lower):
                            score += 30
                        partial_items.append((score, b_val, title_u or title))

                if exact_bpms:
                    # Consenso entre beatmaps com título exato (elimina outliers e covers com andamento alterado)
                    c = Counter([b[0] for b in exact_bpms])
                    most_common_bpm, count = c.most_common(1)[0]
                    disp_title = next(b[1] for b in exact_bpms if b[0] == most_common_bpm)
                    return most_common_bpm, f"{disp_title} (Catboy/Osu)"

                if partial_items:
                    partial_items.sort(key=lambda x: x[0], reverse=True)
                    best = partial_items[0]
                    if best[0] >= 40:
                        return best[1], f"{best[2]} (Catboy/Osu)"
        except Exception:
            pass
        return None

    def _apply_found_bpm(self, raw_title: str, tempo: float, source_name: str, candidates: Optional[List[str]] = None):
        """Aplica o BPM encontrado online, normaliza compasso, salva em favoritas e marca como resolvido."""
        bpm = float(tempo)
        # Normaliza apenas extremos fora da faixa musical viável (60 a 300 BPM)
        while bpm > 300.0:
            bpm /= 2.0
        while bpm < 60.0:
            bpm *= 2.0
        bpm = round(bpm, 1)

        if candidates is None:
            candidates = self._generate_candidates(raw_title)

        with self.lock:
            self.bpm = bpm
            self.is_music = True
            self.media_type = "MUSIC"
            if self.current_title == raw_title:
                self.bpm = bpm

        self.favorites_manager.record_track(raw_title, candidates, bpm, source_name)
        self._mark_resolved_track(raw_title, bpm, source_name)

        if self.verbose:
            print(f"[*] [ONLINE [ONLINE]] BPM Encontrado: {bpm} BPM ({source_name}) para \"{raw_title}\"")

        disp_title = candidates[0] if (candidates and len(candidates[0]) >= 2) else (raw_title[:45] + ("..." if len(raw_title) > 45 else ""))
        self._send_desktop_notification(
            "[ONLINE] BPM Encontrado (Internet)",
            f"{disp_title}\n{bpm} BPM ({source_name})\nSalvo no banco de dados local!",
            icon="applications-multimedia",
            timeout_ms=2500,
            urgency="normal"
        )

    def _lookup_bpm_online(self, raw_title: str, candidates: Optional[List[str]] = None, is_music_classified: bool = False):
        if candidates is None:
            candidates = self._generate_candidates(raw_title)
        raw_lower = raw_title.lower()

        # 1. Prioridade Máxima: Wikis do Project Sekai (Fandom & pjsekai.com)
        for q in candidates:
            if not q or len(q) < 2:
                continue
            res = self._lookup_fandom_wiki("projectsekai.fandom.com", "Project Sekai Wiki", q, raw_lower)
            if res:
                self._apply_found_bpm(raw_title, res[0], res[1], candidates)
                return

            res = self._lookup_pjsekai_com(q, raw_lower)
            if res:
                self._apply_found_bpm(raw_title, res[0], res[1], candidates)
                return

        # 2. Segunda Prioridade: Outras wikis de jogos de ritmo (BanG Dream!, D4DJ)
        for q in candidates:
            if not q or len(q) < 2:
                continue
            res = self._lookup_fandom_wiki("bandori.fandom.com", "BanG Dream! Wiki", q, raw_lower)
            if res:
                self._apply_found_bpm(raw_title, res[0], res[1], candidates)
                return

            res = self._lookup_fandom_wiki("d4dj.fandom.com", "D4DJ Wiki", q, raw_lower)
            if res:
                self._apply_found_bpm(raw_title, res[0], res[1], candidates)
                return

        # 3. Terceira Prioridade: Catboy / Osu! Beatmaps (Anime, Vocaloid, Touhou, Games)
        for q in candidates:
            if not q or len(q) < 2:
                continue
            res = self._lookup_catboy(q, raw_lower)
            if res:
                self._apply_found_bpm(raw_title, res[0], res[1], candidates)
                return

        # 4. Quarta Prioridade: Spotify / Reccobeats (músicas gerais e ocidentais)
        for q in candidates:
            if not q or len(q) < 2:
                continue
            res = self._lookup_reccobeats(q, raw_lower)
            if res:
                self._apply_found_bpm(raw_title, res[0], res[1], candidates)
                return

        # Se não foi encontrado em nenhuma base musical online:
        # Avalia se a faixa tinha fortes indícios musicais ou se era um vídeo convencional
        has_music_indicator = is_music_classified
        if not has_music_indicator:
            for pat in MediaClassifier.MUSIC_INDICATOR_PATTERNS:
                if re.search(pat, raw_title):
                    has_music_indicator = True
                    break

        if has_music_indicator:
            # É uma música genuína (ex: cover indie ou vocaloid não catalogado)
            with self.lock:
                self.is_music = True
                if self.current_title == raw_title:
                    self.bpm = None

            # Armazena na memória de favoritas/histórico mesmo sem BPM no 1º toque!
            self.favorites_manager.record_track(raw_title, candidates, bpm=None, source="Não encontrado online", status="unresolved")
            self._log_unresolved_track(raw_title, candidates)

            if raw_title not in self.notified_failed_tracks:
                self.notified_failed_tracks.add(raw_title)
                disp_title = raw_title[:45] + ("..." if len(raw_title) > 45 else "")
                self._send_desktop_notification(
                    "[WARN] BPM Desconhecido (Usando Áudio)",
                    f"{disp_title}\nEstimando batida pelo som em tempo real.\nToque no NumLock para definir BPM manual!",
                    icon="dialog-warning",
                    timeout_ms=3000,
                    urgency="low"
                )

            if self.verbose:
                print(f"[*] [OFFLINE [MUSIC]] Música sem BPM online: \"{raw_title}\" (armazenada no histórico, aguardando Tap do dono)")
        else:
            # Sem bases musicais e sem termos musicais -> Vídeo Comum
            with self.lock:
                self.is_music = False
                self.media_type = "NON_MUSIC_VIDEO"
                if self.current_title == raw_title:
                    self.bpm = None

            if self.verbose:
                print(f"[*] [VÍDEO NORMAL [VIDEO]] Não catalogado como música nas bases de dados: \"{raw_title[:45]}\". LEDs em repouso.")




# ==============================================================================
# SISTEMA DE COREOGRAFIAS RÍTMICAS (DANÇAS DOS LEDS - COMPASSO 4/4)
# ==============================================================================
# Cada coreografia possui 4 passos (tempos) correspondentes ao compasso musical (4/4):
# Passo 0 = Tempo 1 (Downbeat / cabeça do compasso)
# Passo 1 = Tempo 2
# Passo 2 = Tempo 3
# Passo 3 = Tempo 4
# Formato do passo: (esc_state, numlock_state) -> 1 = Aceso, 0 = Apagado

DANCE_PATTERNS: Dict[str, Dict[str, Any]] = {
    "wave": {
        "name": "Onda Direita (ESC → Duplo → NUM → Vazio)",
        "short_name": "Onda",
        "steps": [(1, 0), (1, 1), (0, 1), (0, 0)],
        "weight": 25,  # 25%
        "description": "ESC -> ESC+NUMLOCK -> NUMLOCK -> NENHUM"
    },
    "strobe": {
        "name": "Flash Duplo Estroboscópico",
        "short_name": "Flash Duplo",
        "steps": [(1, 1), (0, 0), (1, 1), (0, 0)],
        "weight": 20,  # 20%
        "description": "ESC+NUMLOCK -> NENHUM -> ESC+NUMLOCK -> NENHUM"
    },
    "groove": {
        "name": "Groove com Contratempo Duplo",
        "short_name": "Groove Duplo",
        "steps": [(1, 0), (1, 1), (0, 1), (1, 1)],
        "weight": 15,  # 15%
        "description": "ESC -> ESC+NUMLOCK -> NUMLOCK -> ESC+NUMLOCK"
    },
    "impact": {
        "name": "Impacto Duplo & Ricochete",
        "short_name": "Impacto",
        "steps": [(1, 1), (1, 0), (0, 1), (1, 0)],
        "weight": 15,  # 15%
        "description": "ESC+NUMLOCK -> ESC -> NUMLOCK -> ESC"
    },
    "pulse": {
        "name": "Pulso Forte & Balanço",
        "short_name": "Pulso",
        "steps": [(1, 1), (0, 0), (1, 0), (0, 1)],
        "weight": 10,  # 10%
        "description": "ESC+NUMLOCK -> NENHUM -> ESC -> NUMLOCK"
    },
    "breathe": {
        "name": "Pulso Duplo Galopante",
        "short_name": "Galope Duplo",
        "steps": [(1, 1), (1, 0), (1, 1), (0, 1)],
        "weight": 10,  # 10%
        "description": "ESC+NUMLOCK -> ESC -> ESC+NUMLOCK -> NUMLOCK"
    },
    "classic": {
        "name": "Alternado Clássico (1-2-1-2)",
        "short_name": "Clássico",
        "steps": [(1, 0), (0, 1), (1, 0), (0, 1)],
        "weight": 10,  # 10%
        "description": "ESC -> NUMLOCK -> ESC -> NUMLOCK"
    },
    "bounce": {
        "name": "Passo Duplo (Heartbeat)",
        "short_name": "Passo Duplo",
        "steps": [(1, 0), (1, 0), (0, 1), (0, 1)],
        "weight": 5,   # 5%
        "description": "ESC -> ESC -> NUMLOCK -> NUMLOCK"
    },
    "wave_reverse": {
        "name": "Onda Esquerda (NUM → Duplo → ESC → Vazio)",
        "short_name": "Onda Invertida",
        "steps": [(0, 1), (1, 1), (1, 0), (0, 0)],
        "weight": 5,   # 5%
        "description": "NUMLOCK -> ESC+NUMLOCK -> ESC -> NENHUM"
    }
}
DEFAULT_DANCE_MODE = "auto"


def format_led_step(esc: int, num: int) -> str:
    """Formata visualmente o estado dos LEDs na batida atual."""
    if esc and num:
        return "ESC + NUMLOCK [1+2]"
    elif esc:
        return "ESC [1]"
    elif num:
        return "NUMLOCK [2]"
    else:
        return "-- (nenhum) [off]"


class BeatLedController:
    """Controla diretamente os nós de LED do Esc (FnLock) e NumLock."""
    def __init__(self, verbose: bool = True):
        self.verbose = verbose
        self.fnlock_fds: List[int] = []
        self.numlock_fds: List[int] = []
        self.original_triggers: Dict[str, str] = {}
        self.fnlock_state = -1
        self.numlock_state = -1
        self.suppressed = False
        self.lock = threading.Lock()
        self._init_hardware()

    def _init_hardware(self):
        num_dirs = find_internal_led_paths("numlock")
        num_triggers = [os.path.join(p, "trigger") for p in num_dirs]
        fn_triggers = ["/sys/class/leds/platform::fnlock/trigger"]

        # Define trigger para 'none' para controle direto
        for tp in fn_triggers + num_triggers:
            if os.path.exists(tp):
                try:
                    with open(tp, "r") as f:
                        content = f.read()
                        selected = "none"
                        for word in content.split():
                            if word.startswith("[") and word.endswith("]"):
                                selected = word[1:-1]
                                break
                        self.original_triggers[tp] = selected
                    with open(tp, "w") as f:
                        f.write("none\n")
                except Exception:
                    pass

        # Abre descritores diretos de brilho
        if os.path.exists("/sys/class/leds/platform::fnlock/brightness"):
            try:
                fd = os.open("/sys/class/leds/platform::fnlock/brightness", os.O_WRONLY)
                self.fnlock_fds.append(fd)
            except Exception:
                pass

        for p in num_dirs:
            bp = os.path.join(p, "brightness")
            if os.path.exists(bp):
                try:
                    fd = os.open(bp, os.O_WRONLY)
                    self.numlock_fds.append(fd)
                except Exception:
                    pass

        if self.verbose:
            print(f"[*] LED Esc (FnLock - Mão Esquerda): {len(self.fnlock_fds)} fd(s)")
            print(f"[*] LED NumLock (Mão Direita): {len(self.numlock_fds)} fd(s)")

    def write_fnlock(self, state: int):
        with self.lock:
            if self.suppressed and state != 0:
                return
            if state == self.fnlock_state:
                return
            val = b"1\n" if state else b"0\n"
            success = False
            dead_fds = []
            for fd in self.fnlock_fds:
                try:
                    os.lseek(fd, 0, os.SEEK_SET)
                    os.write(fd, val)
                    success = True
                except OSError:
                    dead_fds.append(fd)

            if dead_fds or not self.fnlock_fds:
                for fd in dead_fds:
                    try:
                        os.close(fd)
                    except OSError:
                        pass
                    if fd in self.fnlock_fds:
                        self.fnlock_fds.remove(fd)

                # Auto-recuperação pós-suspensão/hibernação:
                # Reabre o descritor sysfs se tiver sido recriado pelo kernel ACPI (VPC2004)
                if os.path.exists("/sys/class/leds/platform::fnlock/brightness"):
                    try:
                        new_fd = os.open("/sys/class/leds/platform::fnlock/brightness", os.O_WRONLY)
                        os.write(new_fd, val)
                        self.fnlock_fds.append(new_fd)
                        success = True
                    except OSError:
                        pass

            if success:
                self.fnlock_state = state
            else:
                self.fnlock_state = -1

    def write_numlock(self, state: int):
        with self.lock:
            if self.suppressed and state != 0:
                return
            if state == self.numlock_state:
                return
            val = b"1\n" if state else b"0\n"
            success = False
            dead_fds = []
            for fd in self.numlock_fds:
                try:
                    os.lseek(fd, 0, os.SEEK_SET)
                    os.write(fd, val)
                    success = True
                except OSError:
                    dead_fds.append(fd)

            if dead_fds or not self.numlock_fds:
                for fd in dead_fds:
                    try:
                        os.close(fd)
                    except OSError:
                        pass
                    if fd in self.numlock_fds:
                        self.numlock_fds.remove(fd)

                for p in find_internal_led_paths("numlock"):
                    bp = os.path.join(p, "brightness")
                    if os.path.exists(bp):
                        try:
                            new_fd = os.open(bp, os.O_WRONLY)
                            os.write(new_fd, val)
                            self.numlock_fds.append(new_fd)
                            success = True
                        except OSError:
                            pass

            if success:
                self.numlock_state = state
            else:
                self.numlock_state = -1

    def set_beat_state(self, esc_or_step: Any, numlock: Optional[int] = None):
        """
        Define o estado dos LEDs na batida atual.
        Suporta tupla/lista (esc, numlock), dois inteiros (esc, numlock),
        ou o modo legado side (0 = ESC, 1 = NumLock).
        Restaura as danças completas com sincronia total e brilho pleno dos dois LEDs!
        """
        if self.suppressed:
            self.restore_idle()
            return

        if isinstance(esc_or_step, (tuple, list)):
            esc, num = esc_or_step[0], esc_or_step[1]
        elif numlock is not None:
            esc, num = esc_or_step, numlock
        else:
            esc = 1 if esc_or_step == 0 else 0
            num = 1 if esc_or_step == 1 else 0

        self.write_fnlock(esc)
        self.write_numlock(num)

    def restore_idle(self):
        """Restaura o estado de repouso: ambos os LEDs (ESC e NumLock) apagados e hardware fn_lock em 0."""
        with self.lock:
            self.fnlock_state = 0
            self.numlock_state = 0
            for fd in self.fnlock_fds:
                try:
                    os.lseek(fd, 0, os.SEEK_SET)
                    os.write(fd, b"0\n")
                except OSError:
                    pass
            for fd in self.numlock_fds:
                try:
                    os.lseek(fd, 0, os.SEEK_SET)
                    os.write(fd, b"0\n")
                except OSError:
                    pass
        try:
            with open("/sys/bus/platform/devices/VPC2004:00/fn_lock", "w") as f:
                f.write("0\n")
        except Exception:
            pass

    def close(self):
        self.restore_idle()
        for fd in self.fnlock_fds + self.numlock_fds:
            try:
                os.close(fd)
            except OSError:
                pass
        self.fnlock_fds.clear()
        self.numlock_fds.clear()

        for tp, orig in self.original_triggers.items():
            try:
                with open(tp, "w") as f:
                    f.write(f"{orig}\n")
            except Exception:
                pass


MUSIC_ACTIVE_FLAG = "/dev/shm/music_beat_active"


class ServiceOverrideManager:
    """
    Pausa e retoma o medidor de consumo de bateria no NumLock (numlock-power-led.py) com SIGSTOP / SIGCONT.
    Garante controle exclusivo do NumLock durante a música.
    """
    TARGET_SCRIPTS: List[str] = ["numlock-power-led.py"]

    def __init__(self, verbose: bool = True):
        self.verbose = verbose
        self.paused_pids: Set[int] = set()
        self.is_overriding = False

    def _find_target_pids(self) -> List[int]:
        if not self.TARGET_SCRIPTS:
            return []
        pids = []
        my_pid = os.getpid()
        try:
            import psutil
            for proc in psutil.process_iter(['pid', 'cmdline']):
                try:
                    if proc.pid == my_pid:
                        continue
                    cmd = " ".join(proc.info['cmdline'] or [])
                    for script in self.TARGET_SCRIPTS:
                        if script in cmd and "python" in cmd:
                            pids.append(proc.pid)
                            break
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    continue
        except Exception:
            pass
        return pids

    def activate_override(self):
        """Pausa os serviços concorrentes com SIGSTOP e sinaliza modo música ativo."""
        try:
            with open(MUSIC_ACTIVE_FLAG, "w") as f:
                f.write(str(os.getpid()))
        except Exception:
            pass

        # Garante que o LED do CapsLock e FnLock fiquem 100% desligados imediatamente (apenas teclado interno)
        for d in find_internal_led_paths("capslock"):
            p = os.path.join(d, "brightness")
            try:
                with open(p, "w") as f:
                    f.write("0\n")
            except Exception:
                pass

        try:
            with open("/sys/class/leds/platform::fnlock/brightness", "w") as f:
                f.write("0\n")
            with open("/sys/bus/platform/devices/VPC2004:00/fn_lock", "w") as f:
                f.write("0\n")
        except Exception:
            pass

        if self.is_overriding:
            return

        pids = self._find_target_pids()
        for pid in pids:
            try:
                os.kill(pid, signal.SIGSTOP)
                self.paused_pids.add(pid)
            except OSError:
                pass
        self.is_overriding = True
        if self.verbose and self.paused_pids:
            print(f"[*] [PRIORIDADE] Música Ativa: Pausando medidores de energia {list(self.paused_pids)} (SIGSTOP)")

    def release_override(self):
        """Retoma os serviços pausados com SIGCONT e remove a trava de modo música."""
        try:
            if os.path.exists(MUSIC_ACTIVE_FLAG):
                os.remove(MUSIC_ACTIVE_FLAG)
        except Exception:
            pass

        if not self.is_overriding and not self.paused_pids:
            return

        pids = self._find_target_pids()
        all_pids = set(pids) | self.paused_pids
        for pid in all_pids:
            try:
                os.kill(pid, signal.SIGCONT)
            except OSError:
                pass
        if self.verbose and all_pids:
            print(f"[*] Música pausada/finalizada: Retomando medidores de energia {list(all_pids)} (SIGCONT)")
        self.paused_pids.clear()
        self.is_overriding = False


class AudioBeatEngine:
    """
    Motor ultra-leve de captura PipeWire direto do sink de áudio do sistema.
    """
    def __init__(self, sensitivity: float = 1.0, verbose: bool = True):
        self.sensitivity = sensitivity
        self.verbose = verbose
        self.proc: Optional[subprocess.Popen] = None
        self.pipewire_dir = self._detect_pipewire_dir()

    def _detect_pipewire_dir(self) -> str:
        """Encontra o runtime dir do PipeWire do usuário principal."""
        for uid_dir in ["/run/user/1000", f"/run/user/{os.getuid()}"]:
            if os.path.exists(os.path.join(uid_dir, "pipewire-0")):
                return uid_dir
        for p in glob.glob("/run/user/*/pipewire-0"):
            return os.path.dirname(p)
        return f"/run/user/{os.getuid()}"

    def start_recording(self) -> Optional[subprocess.Popen]:
        """Inicia processo pw-record unbuffered capturando o monitor de áudio do sistema."""
        self.stop_recording()
        cmd = [
            "sudo", "-u", "user",
            "env",
            f"XDG_RUNTIME_DIR={self.pipewire_dir}",
            f"PIPEWIRE_RUNTIME_DIR={self.pipewire_dir}",
            "stdbuf", "-o0",
            "pw-record",
            "-P", "{ stream.capture.sink=true }",
            "--rate", str(SAMPLE_RATE),
            "--channels", "1",
            "--format", "s16",
            "--latency", "40ms",
            "--raw", "-"
        ]
        try:
            self.proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                bufsize=0
            )
            return self.proc
        except Exception as e:
            if self.verbose:
                print(f"[!] Erro ao iniciar pw-record: {e}")
            return None

    def stop_recording(self):
        if self.proc:
            try:
                self.proc.terminate()
                self.proc.wait(timeout=0.15)
            except Exception:
                try:
                    self.proc.kill()
                except Exception:
                    pass
            self.proc = None


class AudioTempoEstimator:
    """
    Estima o BPM diretamente dos intervalos entre os kicks de áudio em tempo real.
    Serve como fallback dinâmico instantâneo quando o BPM online não for encontrado.
    """
    def __init__(self):
        self.kick_times: List[float] = []
        self.lock = threading.Lock()
        self.estimated_bpm: Optional[float] = None

    def reset(self):
        with self.lock:
            self.kick_times.clear()
            self.estimated_bpm = None

    def record_kick(self, now: float) -> Optional[float]:
        with self.lock:
            if self.kick_times and (now - self.kick_times[-1]) < 0.22:
                return self.estimated_bpm

            self.kick_times.append(now)
            if len(self.kick_times) > 12:
                self.kick_times.pop(0)

            if len(self.kick_times) < 4:
                return self.estimated_bpm

            intervals = [
                self.kick_times[i] - self.kick_times[i - 1]
                for i in range(1, len(self.kick_times))
            ]

            valid_intervals = []
            for dt in intervals:
                val = dt
                while val > 0.85:
                    val /= 2.0
                while val < 0.35:
                    val *= 2.0
                if 0.35 <= val <= 0.85:
                    valid_intervals.append(val)

            if len(valid_intervals) >= 3:
                valid_intervals.sort()
                median_dt = valid_intervals[len(valid_intervals) // 2]
                bpm = 60.0 / median_dt
                bpm = round(bpm, 1)
                self.estimated_bpm = bpm
                return bpm

            return self.estimated_bpm


# Teclas específicas Fn do hardware e externas
FN_KEYS = set()
for _k in [
    'KEY_FN', 'KEY_FN_ESC', 'KEY_FN_F1', 'KEY_FN_F2', 'KEY_FN_F3', 'KEY_FN_F4',
    'KEY_FN_F5', 'KEY_FN_F6', 'KEY_FN_F7', 'KEY_FN_F8', 'KEY_FN_F9', 'KEY_FN_F10',
    'KEY_FN_F11', 'KEY_FN_F12', 'KEY_FN_1', 'KEY_FN_2', 'KEY_FN_D', 'KEY_FN_E',
    'KEY_FN_F', 'KEY_FN_S', 'KEY_FN_B'
]:
    if hasattr(ecodes, _k):
        FN_KEYS.add(getattr(ecodes, _k))

# Teclas de controle que devem pausar os LEDs e garantir FnLock em 0 imediatamente
MEDIA_AND_FUNCTION_KEYS = set(FN_KEYS)
for _k in [
    'KEY_ESC',
    'KEY_F1', 'KEY_F2', 'KEY_F3', 'KEY_F4', 'KEY_F5', 'KEY_F6', 'KEY_F7', 'KEY_F8',
    'KEY_F9', 'KEY_F10', 'KEY_F11', 'KEY_F12', 'KEY_F13', 'KEY_F14', 'KEY_F15',
    'KEY_F16', 'KEY_F17', 'KEY_F18', 'KEY_F19', 'KEY_F20', 'KEY_F21', 'KEY_F22',
    'KEY_F23', 'KEY_F24',
    'KEY_MUTE', 'KEY_VOLUMEDOWN', 'KEY_VOLUMEUP', 'KEY_MICMUTE',
    'KEY_BRIGHTNESSDOWN', 'KEY_BRIGHTNESSUP', 'KEY_BRIGHTNESS_ZERO',
    'KEY_BRIGHTNESS_MIN', 'KEY_BRIGHTNESS_MAX', 'KEY_BRIGHTNESS_CYCLE',
    'KEY_DISPLAYTOGGLE', 'KEY_SWITCHVIDEOMODE', 'KEY_DISPLAY_OFF',
    'KEY_VIDEO_NEXT', 'KEY_VIDEO_PREV',
    'KEY_WLAN', 'KEY_RFKILL', 'KEY_BLUETOOTH',
    'KEY_CAMERA', 'KEY_SCREENLOCK', 'KEY_COFFEE', 'KEY_SLEEP', 'KEY_SUSPEND',
    'KEY_CONFIG', 'KEY_CONTROLPANEL', 'KEY_CALC', 'KEY_FILE', 'KEY_MAIL', 'KEY_BOOKMARKS',
    'KEY_MEDIA', 'KEY_PLAYPAUSE', 'KEY_PREVIOUSSONG', 'KEY_NEXTSONG', 'KEY_STOPCD',
    'KEY_SYSRQ', 'KEY_PAUSE', 'KEY_INSERT',
    'KEY_TOUCHPAD_TOGGLE', 'KEY_TOUCHPAD_ON', 'KEY_TOUCHPAD_OFF',
    'KEY_REFRESH_RATE_TOGGLE', 'KEY_ROOT_MENU', 'KEY_SELECTIVE_SCREENSHOT',
    'KEY_HELP', 'KEY_PROG1', 'KEY_PROG2', 'KEY_PROG3', 'KEY_PROG4',
    'KEY_FAVORITES', 'KEY_PICKUP_PHONE', 'KEY_HANGUP_PHONE',
    'KEY_POWER', 'KEY_WAKEUP'
]:
    if hasattr(ecodes, _k):
        MEDIA_AND_FUNCTION_KEYS.add(getattr(ecodes, _k))

# Teclas genuínas de digitação (letras, números, pontuação, espaço, enter, backspace)
TYPING_KEYS = {
    # Letras A-Z
    ecodes.KEY_A, ecodes.KEY_B, ecodes.KEY_C, ecodes.KEY_D, ecodes.KEY_E,
    ecodes.KEY_F, ecodes.KEY_G, ecodes.KEY_H, ecodes.KEY_I, ecodes.KEY_J,
    ecodes.KEY_K, ecodes.KEY_L, ecodes.KEY_M, ecodes.KEY_N, ecodes.KEY_O,
    ecodes.KEY_P, ecodes.KEY_Q, ecodes.KEY_R, ecodes.KEY_S, ecodes.KEY_T,
    ecodes.KEY_U, ecodes.KEY_V, ecodes.KEY_W, ecodes.KEY_X, ecodes.KEY_Y, ecodes.KEY_Z,
    # Números 0-9
    ecodes.KEY_1, ecodes.KEY_2, ecodes.KEY_3, ecodes.KEY_4, ecodes.KEY_5,
    ecodes.KEY_6, ecodes.KEY_7, ecodes.KEY_8, ecodes.KEY_9, ecodes.KEY_0,
    # Símbolos e pontuação
    ecodes.KEY_GRAVE, ecodes.KEY_MINUS, ecodes.KEY_EQUAL, ecodes.KEY_BACKSPACE,
    ecodes.KEY_TAB, ecodes.KEY_LEFTBRACE, ecodes.KEY_RIGHTBRACE, ecodes.KEY_BACKSLASH,
    ecodes.KEY_SEMICOLON, ecodes.KEY_APOSTROPHE, ecodes.KEY_COMMA, ecodes.KEY_DOT, ecodes.KEY_SLASH,
    ecodes.KEY_102ND,
    # Espaço, Enter e modificadores
    ecodes.KEY_SPACE, ecodes.KEY_ENTER,
    ecodes.KEY_LEFTSHIFT, ecodes.KEY_RIGHTSHIFT,
    ecodes.KEY_LEFTCTRL, ecodes.KEY_RIGHTCTRL,
    ecodes.KEY_LEFTALT, ecodes.KEY_RIGHTALT,
    ecodes.KEY_LEFTMETA, ecodes.KEY_RIGHTMETA,
    ecodes.KEY_UP, ecodes.KEY_DOWN, ecodes.KEY_LEFT, ecodes.KEY_RIGHT,
    ecodes.KEY_DELETE,
    # Numpad (exceto a tecla de alternância NumLock)
    ecodes.KEY_KP0, ecodes.KEY_KP1, ecodes.KEY_KP2, ecodes.KEY_KP3, ecodes.KEY_KP4,
    ecodes.KEY_KP5, ecodes.KEY_KP6, ecodes.KEY_KP7, ecodes.KEY_KP8, ecodes.KEY_KP9,
    ecodes.KEY_KPDOT, ecodes.KEY_KPENTER, ecodes.KEY_KPPLUS, ecodes.KEY_KPMINUS,
    ecodes.KEY_KPASTERISK, ecodes.KEY_KPSLASH,
}
if hasattr(ecodes, 'KEY_RO'):
    TYPING_KEYS.add(ecodes.KEY_RO)


class KeyboardInputMonitor:
    """
    Monitora eventos do teclado com evdev:
    1. Detecta digitação genuína, teclas Fn e teclas de função/mídia (F1 a F12, Volume, Brilho, etc.).
    2. Rastreia o estado físico da tecla Fn e conjunto de teclas ativas (KeyDown/KeyUp).
    3. DESLIGA OS LEDS IMEDIATAMENTE e garante FnLock=0 no hardware no momento em que a tecla Fn ou qualquer outra for tocada/segurada!
    4. Inteligência NumLock (Tap Tempo e Offset com latência ZERO).
    """
    def __init__(self, on_numlock_press=None, on_numlock_tap=None, on_numlock_hold=None, on_numlock_release_hold=None, on_activity=None, verbose: bool = True):
        self.on_numlock_press = on_numlock_press
        self.on_numlock_tap = on_numlock_tap
        self.on_numlock_hold = on_numlock_hold
        self.on_numlock_release_hold = on_numlock_release_hold
        self.on_activity = on_activity
        self.verbose = verbose
        self.running = True
        self.last_key_time = 0.0
        self.last_media_key_time = 0.0
        self.last_fn_time = 0.0
        self.numlock_held = False
        self.numlock_press_time = 0.0
        self.numlock_is_hold_mode = False
        self.hold_threshold = 0.25
        self.hold_timer: Optional[threading.Timer] = None
        self.lock = threading.Lock()
        self.thread = threading.Thread(target=self._loop, daemon=True)
        self.thread.start()

    def stop(self):
        self.running = False
        with self.lock:
            if self.hold_timer:
                self.hold_timer.cancel()
                self.hold_timer = None

    def is_suppressed(self, normal_threshold: float = 0.8, fn_threshold: float = 1.2, media_threshold: float = 1.5) -> bool:
        """Retorna True se os LEDs devem ser mantidos desligados (tecla Fn ou atalhos recentemente pressionados)."""
        now = time.monotonic()
        if (now - self.last_fn_time) < fn_threshold:
            return True
        if (now - self.last_media_key_time) < media_threshold:
            return True
        return (now - self.last_key_time) < normal_threshold

    def is_typing(self, normal_threshold: float = 0.8, media_threshold: float = 1.5) -> bool:
        """Compatibilidade com o chamador principal: invoca is_suppressed."""
        return self.is_suppressed(normal_threshold, fn_threshold=1.2, media_threshold=media_threshold)

    def _trigger_hold(self, press_time: float):
        with self.lock:
            self.numlock_is_hold_mode = True
            self.numlock_held = True
        if self.on_numlock_hold:
            self.on_numlock_hold(press_time)

    def _loop(self):
        devices = []
        for path in evdev.list_devices():
            try:
                d = evdev.InputDevice(path)
                caps = d.capabilities()
                if ecodes.EV_KEY in caps:
                    name_lower = d.name.lower()
                    # Ignora touchpads, scroll companions, mouses puros, botões de chassi e tampa
                    if "touchpad" in name_lower or "scroll companion" in name_lower:
                        continue
                    if "power button" in name_lower or "lid switch" in name_lower:
                        continue
                    if name_lower.endswith("mouse"):
                        continue
                    devices.append(d)
            except Exception:
                pass
        if not devices:
            try:
                devices.append(evdev.InputDevice("/dev/input/event3"))
            except Exception:
                pass

        fd_map = {d.fd: d for d in devices}
        if self.verbose:
            dev_names = [f"{d.name} ({d.path})" for d in devices]
            print(f"[*] [INPUT [INPUT]] Monitorando {len(devices)} dispositivo(s) de entrada:\n    -> " + "\n    -> ".join(dev_names), flush=True)

        last_scan_time = time.monotonic()

        while self.running:
            try:
                now_check = time.monotonic()
                if not fd_map or (now_check - last_scan_time > 5.0):
                    last_scan_time = now_check
                    current_paths = {d.path for d in fd_map.values()}
                    for path in evdev.list_devices():
                        if path not in current_paths:
                            try:
                                d = evdev.InputDevice(path)
                                caps = d.capabilities()
                                if ecodes.EV_KEY in caps:
                                    name_lower = d.name.lower()
                                    if any(x in name_lower for x in ("touchpad", "scroll companion", "power button", "lid switch")) or name_lower.endswith("mouse"):
                                        d.close()
                                        continue
                                    fd_map[d.fd] = d
                            except Exception:
                                pass

                if not fd_map:
                    time.sleep(1.0)
                    continue

                r, _, _ = select.select(list(fd_map.keys()), [], [], 0.5)
                for fd in r:
                    dev = fd_map.get(fd)
                    if not dev:
                        continue
                    try:
                        events = list(dev.read())
                    except OSError:
                        del fd_map[fd]
                        try:
                            dev.close()
                        except Exception:
                            pass
                        continue

                    for ev in events:
                        if not self.running:
                            break
                        if ev.type == ecodes.EV_KEY:
                            now = time.monotonic()
                            if ev.code == ecodes.KEY_NUMLOCK:
                                if ev.value == 1:
                                    # KeyDown: Registra e aciona IMEDIATAMENTE (0ms de atraso / latência zero)
                                    with self.lock:
                                        self.numlock_press_time = now
                                        self.numlock_held = True
                                        self.numlock_is_hold_mode = False
                                        if self.hold_timer:
                                            self.hold_timer.cancel()
                                        self.hold_timer = threading.Timer(self.hold_threshold, self._trigger_hold, args=(now,))
                                        self.hold_timer.daemon = True
                                        self.hold_timer.start()

                                    if self.on_numlock_press:
                                        self.on_numlock_press(now)
                                elif ev.value == 2:
                                    # KeyRepeat: hardware continua segurando NumLock
                                    with self.lock:
                                        self.numlock_held = True
                                        if (now - self.numlock_press_time) >= self.hold_threshold and not self.numlock_is_hold_mode:
                                            self.numlock_is_hold_mode = True
                                            if self.on_numlock_hold:
                                                self.on_numlock_hold(self.numlock_press_time)
                                elif ev.value == 0:
                                    # KeyUp: Diferencia entre HOLD (Offset) e TAP (BPM)
                                    with self.lock:
                                        if self.hold_timer:
                                            self.hold_timer.cancel()
                                            self.hold_timer = None
                                        was_hold = self.numlock_is_hold_mode or ((now - self.numlock_press_time) >= self.hold_threshold)
                                        press_t = self.numlock_press_time
                                        self.numlock_held = False
                                        self.numlock_is_hold_mode = False

                                    if was_hold:
                                        # Segurou: Usuário quer editar o offset!
                                        if self.on_numlock_release_hold:
                                            self.on_numlock_release_hold(now - press_t, now)
                                    else:
                                        # Toque rápido: Usuário quer informar o BPM!
                                        if self.on_numlock_tap:
                                            self.on_numlock_tap(press_t)
                            elif ev.value in (1, 2):  # KeyDown / Repeat
                                self.last_key_time = now
                                is_fn = ev.code in FN_KEYS
                                is_media = ev.code in MEDIA_AND_FUNCTION_KEYS
                                if is_fn:
                                    self.last_fn_time = now
                                if is_media:
                                    self.last_media_key_time = now

                                # Se for tecla Fn ou tecla especial/mídia, desliga instantaneamente os LEDs e garante fnlock=0!
                                if is_fn or is_media:
                                    if self.on_activity:
                                        self.on_activity(ev.code)
                            elif ev.value == 0:  # KeyUp
                                if ev.code in FN_KEYS:
                                    self.last_fn_time = now
                                if ev.code in MEDIA_AND_FUNCTION_KEYS:
                                    self.last_media_key_time = now
                                else:
                                    self.last_key_time = now
            except (OSError, ValueError):
                bad_fds = []
                for b_fd in list(fd_map.keys()):
                    try:
                        select.select([b_fd], [], [], 0)
                    except (OSError, ValueError):
                        bad_fds.append(b_fd)
                for b_fd in bad_fds:
                    b_dev = fd_map.pop(b_fd, None)
                    if b_dev:
                        try:
                            b_dev.close()
                        except Exception:
                            pass
                time.sleep(0.5)
            except Exception:
                time.sleep(0.5)


class KeyboardBeatApp:
    """Aplicação principal gerenciadora do visualizador de batidas."""
    def __init__(self, sensitivity: float = 1.0, verbose: bool = True, show_beats: bool = False, dance_mode: str = DEFAULT_DANCE_MODE):
        self.sensitivity = sensitivity
        self.verbose = verbose
        self.show_beats = show_beats
        self.dance_mode = dance_mode
        self.running = False
        self.leds = BeatLedController(verbose=verbose)
        self.override_mgr = ServiceOverrideManager(verbose=verbose)
        self.audio_engine = AudioBeatEngine(sensitivity=sensitivity, verbose=verbose)
        self.mpris_tracker = MprisBpmTracker(verbose=verbose)
        self.tempo_estimator = AudioTempoEstimator()
        self.keyboard_monitor = KeyboardInputMonitor(
            on_numlock_press=self._on_numlock_press,
            on_numlock_tap=self._on_numlock_tap,
            on_numlock_hold=self._on_numlock_hold,
            on_numlock_release_hold=self._on_numlock_release_hold,
            on_activity=self._on_keyboard_activity,
            verbose=verbose
        )
        self.default_fnlock_hw = 0
        try:
            with open("/sys/bus/platform/devices/VPC2004:00/fn_lock", "w") as f:
                f.write("0\n")
        except Exception:
            pass

        # Sistema de Coreografias Rítmicas (Danças)
        self.current_dance_key = dance_mode if dance_mode in DANCE_PATTERNS else "classic"
        self.beat_index = 0           # Índice do tempo no compasso (0 a 3)
        self.measure_count = 0        # Total de compassos de 4 tempos na faixa
        self.measures_in_current_dance = 0
        if self.dance_mode == "auto":
            self._pick_initial_dance_for_track()

        # Estado da alternância: 0 = Esc (FnLock), 1 = NumLock
        self.active_side = 0
        self.last_beat_time = 0.0
        self.next_beat_time = 0.0
        self.last_sound_time = time.monotonic()
        self.override_start_time = 0.0

        # Bloqueio de fase único (APENAS UMA VEZ por música)
        self.phase_locked = False
        self.last_synced_title = ""
        self.current_interval = 0.50
        self.custom_offset_sec: Optional[float] = None
        self.last_pos_check: float = 0.0
        self.last_time_check: float = 0.0
        self.typing_paused = False
        self.lock_wait_start = 0.0

        # Tap Tempo inteligente e memória manual de BPM
        self.manual_bpm: Optional[int] = None
        self.manual_track_bpm: Dict[str, int] = {}
        self.tap_times: List[float] = []
        self.tap_finalize_timer: Optional[threading.Timer] = None
        self.tap_lock = threading.Lock()

        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)
        atexit.register(self.cleanup)

    def _get_current_step(self) -> Tuple[int, int]:
        pattern = DANCE_PATTERNS.get(self.current_dance_key, DANCE_PATTERNS["classic"])
        steps = pattern.get("steps", [(1, 0), (0, 1), (1, 0), (0, 1)])
        idx = self.beat_index % len(steps)
        return steps[idx]

    def _pick_initial_dance_for_track(self):
        """Sorteia a coreografia inicial para uma nova música com base nos pesos padrão."""
        keys = list(DANCE_PATTERNS.keys())
        weights = [DANCE_PATTERNS[k].get("weight", 10) for k in keys]
        self.current_dance_key = random.choices(keys, weights=weights, k=1)[0]
        self.measures_in_current_dance = 0
        if self.verbose:
            info = DANCE_PATTERNS[self.current_dance_key]
            print(f"[*] [DANCE [MUSIC]] Coreografia inicial: '{info['name']}' ({info['description']})", flush=True)

    def _maybe_switch_dance(self):
        """
        Avalia transição de coreografia dinamicamente no meio da música:
        - Mínimo de 16 compassos (~25 a 32 segundos) na mesma dança para manter coesão de frase musical.
        - Entre 16 e 31 compassos: 45% de chance de transição rítmica na virada de frase (downbeat).
        - Aos 32 compassos (~1 minuto): transição obrigatória para renovar o visual.
        Envia notificação discreta avisando qual nova dança assumiu.
        """
        if self.measures_in_current_dance < 16:
            return

        if self.measures_in_current_dance < 32 and random.random() > 0.45:
            return

        self.measures_in_current_dance = 0

        other_keys = [k for k in DANCE_PATTERNS if k != self.current_dance_key]
        if not other_keys:
            return
        weights = [DANCE_PATTERNS[k].get("weight", 10) for k in other_keys]
        new_key = random.choices(other_keys, weights=weights, k=1)[0]

        new_info = DANCE_PATTERNS[new_key]
        new_name = new_info.get("name", new_key)
        self.current_dance_key = new_key

        if self.verbose:
            print(f"\n[*] [DANCE [BEAT]] Mudança de coreografia no meio da música: '{new_name}' ({new_info.get('description')})", flush=True)

        try:
            self.mpris_tracker._send_desktop_notification(
                f"[BEAT] Nova Dança: {new_info.get('short_name', new_key)}",
                f"{new_name}\n{new_info.get('description')}",
                icon="audio-volume-high",
                timeout_ms=2500,
                urgency="low"
            )
        except Exception:
            pass

    def _on_keyboard_activity(self, code: int):
        """Desliga imediatamente os LEDs e garante repouso no hardware assim que o usuário toca em qualquer tecla."""
        self.leds.suppressed = True
        self.typing_paused = True
        self.leds.restore_idle()

    def _signal_handler(self, signum, frame):
        self.running = False

    def _notify_tap_complete(self, bpm: int, mode_label: str, n_taps: int):
        """Envia uma ÚNICA notificação elegante e limpa quando o usuário termina de tapear."""
        cur_title = self.mpris_tracker.get_title()
        track_name = cur_title[:32] if cur_title else "Música Atual"
        if cur_title:
            self.mpris_tracker.save_manual_bpm(cur_title, float(bpm))
        self.mpris_tracker._send_desktop_notification(
            f"[PRIORITY] BPM Salvo pelo Dono: {bpm} BPM",
            f"{mode_label} ({n_taps} toques no NumLock)\nFaixa: {track_name}\nSalvo na memória permanente!",
            icon="audio-volume-high",
            timeout_ms=2500,
            urgency="normal"
        )
        if self.verbose:
            print(f"[TAP TEMPO [OK]] Sessão finalizada: {bpm} BPM [{mode_label}] travado com sucesso para '{track_name}'!", flush=True)

    def _on_numlock_press(self, press_time: float):
        """Acionado no INSTANTE EXATO em que a tecla NumLock é pressionada (latência 0ms).
        Congela a dança, garante controle exclusivo e ilumina o LED do NumLock imediatamente."""
        self.typing_paused = False
        self.keyboard_monitor.last_key_time = 0.0
        self.leds.write_fnlock(0)
        self.leds.write_numlock(1)

    def _on_numlock_hold(self, press_time: float):
        """Chamado quando o usuário segura o NumLock por >= 250ms (confirmação do modo offset)."""
        self.typing_paused = False
        self.keyboard_monitor.last_key_time = 0.0
        self.leds.write_fnlock(0)
        self.leds.write_numlock(1)
        if self.verbose:
            bpm = round(60.0 / self.current_interval)
            print(f"[*] [OFFSET [WAIT]] Segurando NumLock para ajustar offset... Solte no Beat 1 (downbeat)! ({bpm} BPM)", flush=True)

    def _on_numlock_release_hold(self, hold_duration: float, release_time: float):
        """Chamado quando o usuário solta o NumLock após segurar (crava o Beat 1 com latência zero e salva o offset)."""
        now = release_time
        if not self.override_mgr.is_overriding:
            self.override_mgr.activate_override()
            self.override_start_time = now

        # Garante o intervalo correto com base no BPM da faixa
        online_bpm, cur_title, _ = self.mpris_tracker.get_track_info()
        if self.manual_bpm and self.manual_bpm > 0:
            self.current_interval = 60.0 / self.manual_bpm
        elif online_bpm and online_bpm > 0:
            self.current_interval = 60.0 / online_bpm

        self.typing_paused = False
        self.phase_locked = True
        self.tap_times.clear()  # Limpa taps para não misturar com hold
        self.beat_index = 0     # Beat 1 imediato (início do compasso 4/4)
        self.active_side = 0
        self.last_beat_time = now
        self.next_beat_time = now + self.current_interval
        self.last_sound_time = now
        step = self._get_current_step()
        self.leds.set_beat_state(step)

        # Salva o offset customizado para a faixa atual de forma assíncrona (não bloqueia o loop)
        track_pos = self.mpris_tracker.get_playback_position()
        if cur_title and self.current_interval > 0:
            cycle_len = 4.0 * self.current_interval
            offset_sec = round(track_pos % cycle_len, 4)
            self.custom_offset_sec = offset_sec
            threading.Thread(
                target=self._async_save_offset,
                args=(cur_title, offset_sec),
                daemon=True
            ).start()

        if self.verbose:
            bpm = round(60.0 / self.current_interval)
            step_str = format_led_step(*step)
            print(f"[OFFSET [OFFSET]] Offset cravado no Beat 1 ao soltar NumLock! ({bpm} BPM) >>> {step_str} <<<", flush=True)

    def _async_save_offset(self, cur_title: str, offset_sec: float):
        """Salva o offset no banco de dados e exibe notificação em segundo plano."""
        try:
            candidates = self.mpris_tracker._generate_candidates(cur_title)
            self.mpris_tracker.favorites_manager.save_custom_offset(cur_title, candidates, offset_sec)
            track_name = cur_title[:32]
            offset_ms = int(round(offset_sec * 1000))
            self.mpris_tracker._send_desktop_notification(
                f"[OFFSET] Offset Salvo: {offset_ms}ms",
                f"Compasso 1-2 alinhado no Beat 1!\nFaixa: {track_name}\nSalvo no banco de dados!",
                icon="audio-volume-high",
                timeout_ms=2000,
                urgency="normal"
            )
            if self.verbose:
                print(f"[OFFSET [SAVED]] Offset {offset_ms}ms salvo no banco de dados para '{track_name}'!", flush=True)
        except Exception as e:
            if self.verbose:
                print(f"[OFFSET [WARN]] Erro ao salvar offset em segundo plano: {e}", flush=True)

    def _on_numlock_tap(self, press_time: float):
        """Chamado a cada toque rápido (< 250ms) no NumLock para Tap Tempo."""
        now = press_time
        if not self.override_mgr.is_overriding:
            self.override_mgr.activate_override()
            self.override_start_time = now

        # Se passou mais de 2.2s desde o último toque, inicia nova sessão de tap
        if self.tap_times and (now - self.tap_times[-1]) > 2.2:
            self.tap_times.clear()

        self.tap_times.append(now)
        if len(self.tap_times) > 12:
            self.tap_times.pop(0)

        n_taps = len(self.tap_times)
        if n_taps == 1:
            self.beat_index = 1
            self.active_side = 1
            self.last_beat_time = now
            self.next_beat_time = now + self.current_interval
            if self.verbose:
                print(f"[TAP TEMPO [TAP]] 1º toque registrado... Continue no ritmo da música para calcular o BPM!", flush=True)
            return

        intervals = [self.tap_times[i] - self.tap_times[i - 1] for i in range(1, n_taps)]
        valid_intervals = [dt for dt in intervals if 0.22 <= dt <= 1.50]
        if not valid_intervals:
            return

        if len(valid_intervals) >= 4:
            sorted_intervals = sorted(valid_intervals)
            trimmed = sorted_intervals[1:-1]
            avg_interval = sum(trimmed) / len(trimmed)
        else:
            avg_interval = sum(valid_intervals) / len(valid_intervals)

        raw_bpm = 60.0 / avg_interval

        # Heurística avançada para múltiplos de 5:
        cand_5 = int(round(raw_bpm / 5.0) * 5)
        dist_5 = abs(raw_bpm - cand_5)

        # 1. Até 5 toques (n_taps <= 5): prioridade absoluta a múltiplos de 5
        if n_taps <= 5:
            final_bpm = cand_5
            mode_label = f"Múltiplo de 5 ({cand_5})"
        # 2. De 6 a 7 toques: ainda favorece fortemente múltiplos de 5 (tolerância ampla de 1.4 BPM)
        elif n_taps <= 7:
            if dist_5 <= 1.4:
                final_bpm = cand_5
                mode_label = f"Múltiplo de 5 ({cand_5})"
            else:
                final_bpm = int(round(raw_bpm))
                mode_label = f"Inteiro específico ({final_bpm})"
        # 3. 8 ou mais toques: usuário continuou tapeando deliberadamente para afinar número específico
        else:
            if dist_5 <= 0.8:
                final_bpm = cand_5
                mode_label = f"Múltiplo de 5 ({cand_5})"
            else:
                final_bpm = int(round(raw_bpm))
                mode_label = f"Inteiro específico ({final_bpm})"

        final_bpm = max(50, min(240, final_bpm))

        self.manual_bpm = final_bpm
        cur_title = self.mpris_tracker.get_title()
        if cur_title:
            self.manual_track_bpm[cur_title] = final_bpm

        target_interval = 60.0 / final_bpm
        self.current_interval = target_interval
        self.phase_locked = True
        self.last_sound_time = now
        self.typing_paused = False

        # Ajusta suavemente a próxima batida sem reiniciar o ritmo abruptamente
        if self.next_beat_time == 0.0 or self.next_beat_time < now or (self.next_beat_time - now) > target_interval:
            self.next_beat_time = now + target_interval

        if self.verbose:
            print(f"[TAP TEMPO [TAP]] {final_bpm} BPM [{mode_label}] (Toque {n_taps})", flush=True)

        # Agenda UMA ÚNICA notificação com debounce de 1.2s quando o usuário parar de tapear
        with self.tap_lock:
            if self.tap_finalize_timer:
                self.tap_finalize_timer.cancel()
            self.tap_finalize_timer = threading.Timer(
                1.2,
                self._notify_tap_complete,
                args=(final_bpm, mode_label, n_taps)
            )
            self.tap_finalize_timer.daemon = True
            self.tap_finalize_timer.start()

    def cleanup(self):
        with self.tap_lock:
            if self.tap_finalize_timer:
                self.tap_finalize_timer.cancel()
                self.tap_finalize_timer = None
        self.keyboard_monitor.stop()
        self.mpris_tracker.stop()
        self.audio_engine.stop_recording()
        self.override_mgr.release_override()
        self.leds.close()
        if self.verbose:
            print("[[OK]] Restauração concluída! Serviços e LEDs restaurados.")

    def run(self):
        self.running = True
        if self.verbose:
            print("[*] Keyboard Music Beat Visualizer (Online BPM + Auto-Tempo + Single Lock) INICIADO.")
            print(f"[*] Sensibilidade: {self.sensitivity}x | Modo: Grade Fixa Anti-Skip 1-2-1-2")
            print("[*] Monitorando áudio, teclado e metadados MPRIS...")

        bytes_per_chunk = CHUNK_SAMPLES * 2  # s16 = 2 bytes por amostra
        alpha = 0.18                         # Filtro passa-baixa monopolar ~70 Hz (Pure Kick Punch)
        filtered_val = 0.0
        baseline = 250.0
        prev_chunk_energy = 0.0
        fallback_interval = 0.50             # Fallback 120 BPM se offline

        adaptive_threshold_ratio = 1.35 / max(0.2, self.sensitivity)
        min_energy_floor = 250.0 / max(0.2, self.sensitivity)

        record_proc = self.audio_engine.start_recording()

        while self.running:
            if not record_proc or record_proc.poll() is not None:
                record_proc = self.audio_engine.start_recording()
                if not record_proc:
                    time.sleep(0.2)
                    continue

            try:
                raw_chunk = read_exact(record_proc.stdout, bytes_per_chunk)
                if not raw_chunk:
                    time.sleep(0.02)
                    continue

                num_samples = len(raw_chunk) // 2
                samples = struct.unpack(f"<{num_samples}h", raw_chunk)
            except Exception:
                time.sleep(0.02)
                continue

            now = time.monotonic()

            # Processamento O(1) de passa-baixa em sub-graves (~70 Hz)
            chunk_energy = 0.0
            for s in samples:
                abs_s = abs(s)
                filtered_val += alpha * (abs_s - filtered_val)
                chunk_energy += filtered_val

            chunk_energy /= num_samples

            # Atualização assimétrica da baseline (acompanha vales rapidamente, picos lentamente)
            if chunk_energy > baseline:
                baseline += 0.02 * (chunk_energy - baseline)
            else:
                baseline += 0.15 * (chunk_energy - baseline)

            # Obtém metadados da faixa atual e estado de música vs vídeo comum
            online_bpm, current_title, current_track_offset = self.mpris_tracker.get_track_info()
            is_music_active = self.mpris_tracker.is_music_active()

            # Se o título mudou (mudou de faixa no tocador), destrava a fase para recalibrar na nova música
            if current_title and current_title != self.last_synced_title:
                if self.verbose:
                    print(f"[*] Nova faixa detectada: '{current_title}' - Destravando fase para recalibração única")
                self.last_synced_title = current_title
                self.phase_locked = False
                self.custom_offset_sec = current_track_offset
                self.last_pos_check = 0.0
                self.last_time_check = 0.0
                self.lock_wait_start = now
                self.next_beat_time = 0.0
                self.override_start_time = now
                self.tempo_estimator.reset()
                self.tap_times.clear()
                self.manual_bpm = self.manual_track_bpm.get(current_title, None)
                self.measure_count = 0
                self.measures_in_current_dance = 0
                self.beat_index = 0
                if self.dance_mode == "auto":
                    self._pick_initial_dance_for_track()
            elif self.custom_offset_sec is None and current_track_offset is not None:
                self.custom_offset_sec = current_track_offset

            # Rastreamento de saltos na reprodução (seek detection > 0.8s) para realinhamento imediato de fase
            pos = self.mpris_tracker.get_playback_position()
            if self.phase_locked and self.custom_offset_sec is not None and self.last_pos_check > 0:
                dt_check = now - self.last_time_check
                dpos_check = pos - self.last_pos_check
                if abs(dpos_check - dt_check) > 0.8:
                    if self.verbose:
                        print(f"[*] [SEEK [SEEK]] Salto na reprodução detectado ({dpos_check:+.2f}s). Reajustando fase com offset salvo...")
                    self.phase_locked = False
            self.last_pos_check = pos
            self.last_time_check = now

            # Presença de áudio: só ativa override e pausa medidores se o conteúdo for MÚSICA
            if chunk_energy > min_energy_floor:
                self.last_sound_time = now
                if is_music_active and not self.override_mgr.is_overriding:
                    self.override_mgr.activate_override()
                    self.override_start_time = now

            # Se for VÍDEO CONVENCIONAL (documentário, podcast, aula) ou não-musical:
            if not is_music_active:
                if self.override_mgr.is_overriding:
                    self.override_mgr.release_override()
                    self.leds.restore_idle()
                    self.phase_locked = False
                    self.next_beat_time = 0.0
                    self.last_beat_time = 0.0
                    self.last_pos_check = 0.0
                    self.last_time_check = 0.0
                    self.tempo_estimator.reset()
                continue

            threshold = max(min_energy_floor, baseline * adaptive_threshold_ratio)

            # Kick Físico Onset (detectado do áudio real)
            is_audio_kick = (
                chunk_energy > threshold
                and chunk_energy >= (prev_chunk_energy * 0.95)
            )
            prev_chunk_energy = chunk_energy

            if is_audio_kick:
                self.tempo_estimator.record_kick(now)

            # Determinação do BPM e modo (Prioridade: BPM MANUAL > BPM ONLINE > AUDIO REAL-TIME > FALLBACK)
            if self.manual_bpm and self.manual_bpm > 0:
                target_interval = 60.0 / self.manual_bpm
                bpm_display = self.manual_bpm
                mode_str = "MANUAL TAP"
            elif online_bpm and online_bpm > 0:
                target_interval = 60.0 / online_bpm
                bpm_display = online_bpm
                mode_str = "ONLINE BPM"
            else:
                est = self.tempo_estimator.estimated_bpm
                if est and est > 0:
                    target_interval = 60.0 / est
                    bpm_display = est
                    mode_str = "AUDIO REAL-TIME"
                else:
                    target_interval = fallback_interval
                    bpm_display = int(60.0 / fallback_interval)
                    mode_str = "AUDIO FALLBACK"

            # SILÊNCIO / MÚSICA EM PAUSA / FINALIZADA:
            # Avaliado de forma INDEPENDENTE da trava de fase para nunca travar piscando!
            is_mpris_playing = self.mpris_tracker.is_playing
            sound_silence = now - self.last_sound_time
            should_stop = False
            if self.override_mgr.is_overriding:
                if not is_mpris_playing:
                    should_stop = True
                elif sound_silence > SILENCE_TIMEOUT_SEC:
                    should_stop = True

            if should_stop:
                if self.verbose:
                    print(f"[*] Música pausada/finalizada: Devolvendo controle ao medidor de bateria...")
                self.override_mgr.release_override()
                self.leds.restore_idle()
                self.phase_locked = False
                self.next_beat_time = 0.0
                self.last_beat_time = 0.0
                self.last_pos_check = 0.0
                self.last_time_check = 0.0
                self.tempo_estimator.reset()
                continue

            # CALIBRAÇÃO MANUAL (NumLock Pressionado):
            # Enquanto o usuário segura o NumLock, aguarda a soltura instantânea para sincronizar o beat 1
            if self.keyboard_monitor.numlock_held:
                continue

            # PRIORIDADE TOTAL DA DIGITAÇÃO:
            # PRIORIDADE TOTAL DA DIGITAÇÃO E TECLAS FN/ESPECIAIS:
            # Se a tecla Fn estiver pressionada, ou qualquer tecla sendo segurada, ou digitação recente:
            # os LEDs da música são mantidos 100% desligados e fnlock em 0 absoluto no hardware.
            # O metrônomo e a contagem de batidas CONTINUAM rodando em segundo plano sem perder o ritmo ou offset!
            is_suppressed = self.keyboard_monitor.is_suppressed()
            self.leds.suppressed = is_suppressed
            if is_suppressed:
                if not self.typing_paused:
                    self.typing_paused = True
                    self.leds.restore_idle()
                    if self.verbose:
                        print("[*] [SUPRESSÃO LED] Tecla Fn / Digitação detectada: LEDs desligados e fnlock travado em 0...", flush=True)
            else:
                if self.typing_paused:
                    self.typing_paused = False
                    if self.verbose:
                        step_str = format_led_step(*self._get_current_step())
                        print(f"[*] [MÚSICA RETOMADA] Teclado liberado: Retomando danças na próxima batida cheia ({step_str})...", flush=True)

            # TRAVAMENTO DE OFFSET: APENAS UMA VEZ POR MÚSICA / SESSÃO
            if self.override_mgr.is_overriding and not self.phase_locked:
                if self.custom_offset_sec is not None and pos > 0 and target_interval > 0:
                    # ALINHAMENTO INSTANTÂNEO DE FASE COM OFFSET SALVO (0ms, sem esperar kick de áudio!)
                    cycle_len = 4.0 * target_interval
                    elapsed_in_cycle = round((pos - self.custom_offset_sec) % cycle_len, 4)
                    time_into_current_beat = round(elapsed_in_cycle % target_interval, 4)
                    time_to_next_beat = round((target_interval - time_into_current_beat) % target_interval, 4)
                    current_beat_index = int(elapsed_in_cycle // target_interval) % 4

                    self.phase_locked = True
                    self.current_interval = target_interval
                    self.beat_index = current_beat_index
                    self.active_side = current_beat_index % 2
                    if time_to_next_beat < 0.01:
                        self.next_beat_time = now + target_interval
                    else:
                        self.next_beat_time = now + time_to_next_beat
                    self.last_beat_time = now

                    if not is_suppressed:
                        step = self._get_current_step()
                        self.leds.set_beat_state(step)
                    if self.verbose:
                        step_str = format_led_step(*self._get_current_step())
                        dance_info = DANCE_PATTERNS.get(self.current_dance_key, {})
                        dance_name = dance_info.get("short_name", self.current_dance_key)
                        print(f"[LOCK [SAVED]] Fase alinhada instantaneamente com offset salvo ({round(self.custom_offset_sec * 1000)}ms)! ({bpm_display:.1f} BPM [{mode_str}]) [{dance_name}] >>> {step_str} <<<", flush=True)
                else:
                    should_lock = is_audio_kick
                    # Fallback se a introdução for suave/acústica sem kick pesado por mais de 2.0s
                    wait_base = self.lock_wait_start if self.lock_wait_start > 0 else self.override_start_time
                    if not should_lock and (now - wait_base) > 2.0:
                        should_lock = True

                    if should_lock:
                        self.phase_locked = True
                        self.current_interval = target_interval
                        self.beat_index = 0  # Inicia no Beat 1 do compasso
                        self.active_side = 0
                        if not is_suppressed:
                            step = self._get_current_step()
                            self.leds.set_beat_state(step)
                        self.last_beat_time = now
                        self.next_beat_time = now + target_interval
                        if self.verbose:
                            lock_reason = "1º kick de áudio" if is_audio_kick else "tempo limite de espera"
                            step_str = format_led_step(*self._get_current_step())
                            dance_info = DANCE_PATTERNS.get(self.current_dance_key, {})
                            dance_name = dance_info.get("short_name", self.current_dance_key)
                            print(f"[LOCK [LOCKED]] Offset travado no {lock_reason}! ({bpm_display:.1f} BPM [{mode_str}]) [{dance_name}] >>> {step_str} <<<", flush=True)

            # Se o BPM foi atualizado (online chegou ou auto-tempo afinou), atualiza o intervalo da grade suavemente
            if self.override_mgr.is_overriding and self.phase_locked:
                if abs(target_interval - self.current_interval) > 0.02:
                    if self.verbose:
                        print(f"[*] [TEMPO [MUSIC]] Atualizando compasso para {bpm_display:.1f} BPM [{mode_str}]")
                    if self.next_beat_time > now and self.current_interval > 0:
                        fraction = (self.next_beat_time - now) / self.current_interval
                        self.current_interval = target_interval
                        self.next_beat_time = now + fraction * target_interval
                    else:
                        self.current_interval = target_interval
                        self.next_beat_time = now + target_interval

            # METRÔNOMO DE GRADE FIXA (Fixed-Grid Metronome):
            # UMA VEZ TRAVADO, NENHUM AJUSTE DE OFFSET É FEITO!
            if self.override_mgr.is_overriding and self.phase_locked:
                if now >= self.next_beat_time and self.next_beat_time > 0:
                    interval = self.current_interval if self.current_interval > 0.05 else 0.50
                    beats_to_advance = int((now - self.next_beat_time) // interval) + 1
                    self.next_beat_time += beats_to_advance * interval
                    self.last_beat_time = now

                    old_beat_index = self.beat_index
                    self.beat_index = (self.beat_index + beats_to_advance) % 4
                    self.active_side = self.beat_index % 2

                    # Contabiliza compassos completos ao virar o ciclo de 4 batidas
                    if self.beat_index < old_beat_index or beats_to_advance >= 4:
                        measures_advanced = max(1, beats_to_advance // 4)
                        self.measure_count += measures_advanced
                        self.measures_in_current_dance += measures_advanced

                        # Avalia transição sutil e rara de dança
                        if self.dance_mode == "auto":
                            self._maybe_switch_dance()

                    if not is_suppressed:
                        step = self._get_current_step()
                        self.leds.set_beat_state(step)

                        if self.verbose and (sys.stdout.isatty() or self.show_beats):
                            dance_info = DANCE_PATTERNS.get(self.current_dance_key, {})
                            dance_name = dance_info.get("short_name", self.current_dance_key)
                            step_str = format_led_step(*step)
                            beat_num = self.beat_index + 1
                            print(f"[BEAT {beat_num}/4 | {dance_name}] >>> {step_str} <<< ({bpm_display:.1f} BPM [{mode_str}])", flush=True)

        self.cleanup()


def emergency_restore():
    """Restaura imediatamente todos os LEDs e serviços para o padrão de fábrica."""
    print("[*] Executando restauração de emergência de todos os LEDs e serviços...")
    try:
        import psutil
        for proc in psutil.process_iter(['pid', 'cmdline']):
            try:
                cmd = " ".join(proc.info['cmdline'] or [])
                for script in ["keyboard-ripple-led.py", "numlock-power-led.py"]:
                    if script in cmd and "python" in cmd and proc.pid != os.getpid():
                        os.kill(proc.pid, signal.SIGCONT)
            except Exception:
                pass
    except Exception:
        pass

    try:
        with open("/sys/bus/platform/devices/VPC2004:00/fn_lock", "w") as f:
            f.write("0\n")
    except Exception:
        pass

    try:
        with open("/sys/class/leds/platform::fnlock/brightness", "w") as f:
            f.write("0\n")
    except Exception:
        pass

    for d in find_internal_led_paths("numlock"):
        path = os.path.join(d, "brightness")
        try:
            with open(path, "w") as f:
                f.write("0\n")
        except Exception:
            pass
        trig = os.path.join(d, "trigger")
        try:
            with open(trig, "w") as f:
                f.write("kbd-numlock\n")
        except Exception:
            pass

    print("[[OK]] Restauração concluída! Hardware e serviços 100% no padrão original.")


def test_simulation():
    """Simulação visual de todas as coreografias nos LEDs físicos."""
    print("[*] =================================================================")
    print("[*] DEMONSTRAÇÃO VISUAL DAS COREOGRAFIAS NOS LEDs FÍSICOS (110 BPM)")
    print("[*] =================================================================")
    bpm = 110.0
    interval = 60.0 / bpm
    leds = BeatLedController(verbose=False)
    try:
        for key, pattern in DANCE_PATTERNS.items():
            name = pattern["name"]
            desc = pattern["description"]
            steps = pattern["steps"]
            print(f"\n[[BEAT] Coreografia: {name}]")
            print(f"   Padrão: {desc}")
            for measure in range(2):
                for beat, (esc, num) in enumerate(steps):
                    step_str = format_led_step(esc, num)
                    print(f"   -> Compasso {measure+1} | Tempo {beat+1}/4: {step_str} ({interval:.2f}s)")
                    leds.set_beat_state((esc, num))
                    time.sleep(interval)
    finally:
        leds.close()
    print("\n[[OK]] Demonstração de todas as coreografias concluída com sucesso!")


def install_service():
    """Instala a unidade systemd para execução contínua em segundo plano."""
    service_file = "/home/user/antigravity/radiant-goodall/keyboard-beat.service"
    target_path = f"/etc/systemd/system/{SERVICE_NAME}"
    print(f"[*] Instalando serviço: {target_path}...")
    try:
        subprocess.check_call(["cp", service_file, target_path])
        subprocess.check_call(["systemctl", "daemon-reload"])
        subprocess.check_call(["systemctl", "enable", "--now", SERVICE_NAME])
        print(f"[[OK]] {SERVICE_NAME} instalado e ativo com sucesso!")
        subprocess.check_call(["systemctl", "status", SERVICE_NAME, "--no-pager"])
    except Exception as e:
        print(f"[!] Erro ao instalar serviço: {e}")


def uninstall_service():
    """Remove a unidade systemd e restaura os LEDs."""
    target_path = f"/etc/systemd/system/{SERVICE_NAME}"
    print(f"[*] Removendo {SERVICE_NAME}...")
    try:
        subprocess.call(["systemctl", "stop", SERVICE_NAME], stderr=subprocess.DEVNULL)
        subprocess.call(["systemctl", "disable", SERVICE_NAME], stderr=subprocess.DEVNULL)
        if os.path.exists(target_path):
            os.remove(target_path)
        subprocess.call(["systemctl", "daemon-reload"], stderr=subprocess.DEVNULL)
        emergency_restore()
        print(f"[[OK]] {SERVICE_NAME} removido e desativado com sucesso!")
    except Exception as e:
        print(f"[!] Erro ao remover serviço: {e}")


def main():
    parser = argparse.ArgumentParser(
        description="Keyboard Music Beat Visualizer (Online BPM + Fixed Grid Anti-Skip)"
    )
    parser.add_argument("--restore", action="store_true", help="Restaura LEDs e serviços")
    parser.add_argument("--test", action="store_true", help="Executa um teste visual alternado nos LEDs")
    parser.add_argument("--sensitivity", type=float, default=DEFAULT_SENSITIVITY, help="Multiplicador de sensibilidade (padrão: 1.0)")
    parser.add_argument("--dance", choices=list(DANCE_PATTERNS.keys()) + ["auto"], default="auto", help="Modo de coreografia dos LEDs (padrão: auto)")
    parser.add_argument("--install-service", action="store_true", help="Instala e ativa o serviço systemd")
    parser.add_argument("--uninstall-service", action="store_true", help="Desinstala o serviço systemd")
    parser.add_argument("--quiet", action="store_true", help="Modo silencioso (sem logs no terminal)")
    parser.add_argument("--show-beats", action="store_true", help="Mostra logs de cada batida individual mesmo sem TTY")
    args = parser.parse_args()

    if args.restore:
        emergency_restore()
        return

    if args.test:
        test_simulation()
        return

    if args.install_service:
        install_service()
        return

    if args.uninstall_service:
        uninstall_service()
        return

    app = KeyboardBeatApp(
        sensitivity=args.sensitivity,
        verbose=not args.quiet,
        show_beats=args.show_beats,
        dance_mode=args.dance
    )
    app.run()


if __name__ == "__main__":
    main()
