# keyboard-music-beat

Real-time rhythmic beat visualizer for Linux keyboard LEDs featuring MPRIS track tracking, online BPM discovery, a fixed-grid zero-drift phase accumulator, and tap-tempo calibration.

## Architecture

keyboard-music-beat modulates Linux keyboard LEDs (such as NumLock, CapsLock, and FnLock) in synchronization with background music playback:

1. Persistent MPRIS Tracker: Monitors active audio players (Spotify, YouTube in Brave/Firefox, VLC) via DBus signals with zero polling overhead.
2. Online BPM Discovery: Queries audio metadata APIs (such as ReccoBeats) to fetch precise song tempo figures on track changes.
3. Fixed-Grid Phase Accumulator: Advances beat positions at constant mathematical intervals (`next_beat += interval`), preventing beat skips or cumulative timing drift over long playback sessions.
4. Audio Signal Fallback: When online metadata is unavailable, samples local audio playback streams via PulseAudio or PipeWire monitor sources to detect low-frequency kick drum transients.
5. Interactive Tap-Tempo: Allows manual tempo locking by tapping the physical NumLock key to establish or override rhythm cadence.
6. Energy Efficiency: Consumes 0.0% CPU during idle silence and under 0.2% CPU during active playback.

## Requirements

- Linux with `/sys/class/leds` or platform backlight access
- Python 3.8+
- python-evdev

```bash
sudo apt install python3-evdev
```

## Installation

1. Install the binary:

```bash
sudo cp keyboard_music_beat.py /usr/local/bin/keyboard-music-beat
sudo chmod +x /usr/local/bin/keyboard-music-beat
```

2. Enable the systemd service:

```bash
sudo cp systemd/keyboard-beat.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable --now keyboard-beat.service
```

## Usage

Run directly from terminal for debugging or manual tap-tempo:

```bash
sudo python3 /usr/local/bin/keyboard-music-beat
```

Controls:
- Tap `NumLock` rhythmically to set manual BPM.
- Hold `NumLock` and release on Beat 1 to calibrate phase alignment.

## License

MIT
