// script.js - Audio visualization, FFT and rendering logic
(function() {
  // ---------- DOM Elements ----------
  const canvas = document.getElementById('visualizer-canvas');
  const ctx = canvas.getContext('2d');
  const playlistDiv = document.getElementById('playlistContainer');
  const progressSlider = document.getElementById('progressSlider');
  const currentTimeSpan = document.getElementById('currentTime');
  const durationSpan = document.getElementById('durationTime');
  const playPauseBtn = document.getElementById('playPauseBtn');
  const prevBtn = document.getElementById('prevBtn');
  const nextBtn = document.getElementById('nextBtn');
  const uploadBtn = document.getElementById('uploadBtn');
  const fileInput = document.getElementById('fileInput');
  const collapseBtn = document.getElementById('collapsePanelBtn');
  const uiPanel = document.getElementById('uiPanel');
  const nowPlayingLabel = document.getElementById('nowPlayingLabel');
  const edgeReveal = document.getElementById('edgeRevealBtn');

  // ---------- Audio & Visualization Globals ----------
  let audioElement = new Audio();
  let audioCtx = null;
  let sourceNode = null;
  let analyserNode = null;
  let isPlaying = false;

  // Playlist and play mode
  let playlist = [];
  let currentTrackIndex = 0;
  let playMode = 'list';   // 'list', 'shuffle', 'loop'

  // ---------- FFT implementation (ported from C) ----------
  const FFT_SIZE = 8192;                       // 2^13
  let inRaw = new Float32Array(FFT_SIZE);      // raw input samples
  let inWin = new Float32Array(FFT_SIZE);      // windowed samples
  let outRawReal = new Float32Array(FFT_SIZE); // real part after FFT
  let outRawImag = new Float32Array(FFT_SIZE); // imag part after FFT
  let outLog = new Float32Array(FFT_SIZE);     // log-scaled magnitude
  let outSmooth = new Float32Array(FFT_SIZE);  // smoothed values (attack/decay)
  let outSmear = new Float32Array(FFT_SIZE);   // trailing effect

  // Hann window
  let hannWindow = new Float32Array(FFT_SIZE);
  for (let i = 0; i < FFT_SIZE; i++) {
    let t = i / (FFT_SIZE - 1);
    hannWindow[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * t);
  }

  // In-place FFT (Cooley-Tukey)
  function fft(real, imag, n) {
    // Bit-reversal permutation
    for (let i = 1, j = 0; i < n; i++) {
      let bit = n >> 1;
      while (j & bit) {
        j ^= bit;
        bit >>= 1;
      }
      j ^= bit;
      if (i < j) {
        let tempReal = real[i];
        real[i] = real[j];
        real[j] = tempReal;
        let tempImag = imag[i];
        imag[i] = imag[j];
        imag[j] = tempImag;
      }
    }

    // Cooley-Tukey iterative FFT
    for (let len = 2; len <= n; len <<= 1) {
      let ang = 2 * Math.PI / len;
      let wLenReal = Math.cos(ang);
      let wLenImag = Math.sin(ang);
      for (let i = 0; i < n; i += len) {
        let wReal = 1;
        let wImag = 0;
        for (let j = 0; j < len / 2; j++) {
          let uReal = real[i + j];
          let uImag = imag[i + j];
          let vReal = real[i + j + len/2] * wReal - imag[i + j + len/2] * wImag;
          let vImag = real[i + j + len/2] * wImag + imag[i + j + len/2] * wReal;
          real[i + j] = uReal + vReal;
          imag[i + j] = uImag + vImag;
          real[i + j + len/2] = uReal - vReal;
          imag[i + j + len/2] = uImag - vImag;
          let nextWReal = wReal * wLenReal - wImag * wLenImag;
          let nextWImag = wReal * wLenImag + wImag * wLenReal;
          wReal = nextWReal;
          wImag = nextWImag;
        }
      }
    }
  }

  // Amplitude from complex number (log scale)
  function amp(real, imag) {
    return Math.log(real * real + imag * imag);
  }

  // Core FFT analysis (returns number of bars)
  function fftAnalyze(dt) {
    // Apply Hann window
    for (let i = 0; i < FFT_SIZE; i++) {
      inWin[i] = inRaw[i] * hannWindow[i];
    }

    // Copy to FFT buffers
    for (let i = 0; i < FFT_SIZE; i++) {
      outRawReal[i] = inWin[i];
      outRawImag[i] = 0;
    }

    fft(outRawReal, outRawImag, FFT_SIZE);

    // Logarithmic frequency mapping
    let step = 1.06;
    let lowf = 1.0;
    let m = 0;
    let maxAmp = 1.0;
    for (let f = lowf; Math.floor(f) < FFT_SIZE/2; f = Math.ceil(f * step)) {
      let f1 = Math.ceil(f * step);
      let a = 0.0;
      for (let q = Math.floor(f); q < FFT_SIZE/2 && q < Math.floor(f1); q++) {
        let b = amp(outRawReal[q], outRawImag[q]);
        if (b > a) a = b;
      }
      if (maxAmp < a) maxAmp = a;
      outLog[m++] = a;
    }

    // Normalize to [0,1]
    for (let i = 0; i < m; i++) {
      outLog[i] /= maxAmp;
    }

    // Smoothing and smearing (exponential filters)
    const smoothness = 8.0;   // attack/decay speed for main bars
    const smearness = 3.0;    // trailing effect speed
    for (let i = 0; i < m; i++) {
      outSmooth[i] += (outLog[i] - outSmooth[i]) * smoothness * dt;
      outSmear[i] += (outSmooth[i] - outSmear[i]) * smearness * dt;
    }
    return m;
  }

  // Push a single audio sample into the circular buffer
  function fftPush(frame) {
    for (let i = 0; i < FFT_SIZE - 1; i++) {
      inRaw[i] = inRaw[i + 1];
    }
    inRaw[FFT_SIZE - 1] = frame;
  }

  // Trail history for each bar (used for cone-shaped trailing)
  let prevBarTopY = [];
  let prevBarRadius = [];
  let prevBarCount = 0;

  // ---------- Rendering (bars + cone trail + glowing orb) ----------
  function fftRender(boundary, m) {
    const cellWidth = boundary.width / m;          // width of each frequency bar
    const saturation = 0.85;                       // color saturation

    // Reinitialize trail arrays if bar count changed
    if (prevBarCount !== m) {
      prevBarTopY = new Array(m).fill(null);
      prevBarRadius = new Array(m).fill(0);
      prevBarCount = m;
    }

    // Clear background (same dark color as original)
    ctx.fillStyle = '#151515';
    ctx.fillRect(boundary.x, boundary.y, boundary.width, boundary.height);

    // 1. Draw bars (thickened and more vivid)
    for (let i = 0; i < m; i++) {
      let t = outSmooth[i];
      let hue = (i / m) * 360;
      let vividColor = `hsl(${hue}, 85%, 65%)`;   // high saturation, medium brightness

      const startPos = {
        x: boundary.x + i * cellWidth + cellWidth / 2,
        y: boundary.y + boundary.height - boundary.height * 2/3 * t
      };
      const endPos = {
        x: boundary.x + i * cellWidth + cellWidth / 2,
        y: boundary.y + boundary.height
      };
      // Bar thickness: 0.55 * cellWidth * sqrt(amplitude) (much thicker than original)
      const thick = cellWidth * 0.55 * Math.sqrt(t);

      ctx.beginPath();
      ctx.moveTo(startPos.x, startPos.y);
      ctx.lineTo(endPos.x, endPos.y);
      ctx.lineWidth = thick;
      ctx.strokeStyle = vividColor;
      ctx.lineCap = 'round';
      ctx.stroke();
    }

    // 2. Draw cone-shaped trail using dense dot array
    for (let i = 0; i < m; i++) {
      const tCurr = outSmooth[i];
      if (tCurr < 0.01) continue;

      const hue = (i / m) * 360;
      const currX = boundary.x + i * cellWidth + cellWidth / 2;
      const currY = boundary.y + boundary.height - boundary.height * 2/3 * tCurr;
      // Orb radius (enlarged)
      let ballRadius = cellWidth * 2.2 * Math.sqrt(tCurr);
      ballRadius = Math.min(ballRadius, cellWidth * 1.2);
      // Trail max radius (close to inner glow radius)
      const maxTrailRadius = ballRadius * 0.55;
      const minTrailRadius = maxTrailRadius * 0.15;   // tip becomes very thin

      if (prevBarTopY[i] !== null) {
        const prevY = prevBarTopY[i];
        const dy = currY - prevY;
        const distance = Math.abs(dy);
        if (distance > 1) {
          // Dynamic step count: at least one dot per 2 pixels, up to 30 dots
          let steps = Math.min(30, Math.max(10, Math.floor(distance / 2)));
          for (let step = 1; step <= steps; step++) {
            const t = step / steps;   // 0 = old position, 1 = new position
            const interpY = prevY + dy * t;
            const radius = minTrailRadius + (maxTrailRadius - minTrailRadius) * t;
            const alpha = 0.85 * t;    // transparency increases towards the tip
            ctx.beginPath();
            ctx.arc(currX, interpY, radius, 0, Math.PI * 2);
            ctx.fillStyle = `hsla(${hue}, 85%, 70%, ${alpha})`;
            ctx.fill();
          }
        }
      }
      prevBarTopY[i] = currY;
      prevBarRadius[i] = ballRadius;
    }

    // 3. Draw glowing orbs (radial gradient, no white highlight)
    for (let i = 0; i < m; i++) {
      let t = outSmooth[i];
      if (t < 0.008) continue;

      let hue = (i / m) * 360;
      const center = {
        x: boundary.x + i * cellWidth + cellWidth / 2,
        y: boundary.y + boundary.height - boundary.height * 2/3 * t
      };
      let radius = cellWidth * 2.2 * Math.sqrt(t);
      radius = Math.min(radius, cellWidth * 1.2);

      // Main orb: radial gradient fading to transparent at edge
      const gradient = ctx.createRadialGradient(center.x, center.y, 0, center.x, center.y, radius);
      gradient.addColorStop(0, `hsl(${hue}, 92%, 78%)`);
      gradient.addColorStop(0.4, `hsl(${hue}, 88%, 68%)`);
      gradient.addColorStop(1, `hsla(${hue}, 80%, 55%, 0)`);
      ctx.beginPath();
      ctx.arc(center.x, center.y, radius, 0, Math.PI * 2);
      ctx.fillStyle = gradient;
      ctx.fill();

      // Inner glow (larger than before)
      const innerRadius = radius * 0.65;
      const innerGradient = ctx.createRadialGradient(center.x, center.y, 0, center.x, center.y, innerRadius);
      innerGradient.addColorStop(0, `hsl(${hue}, 95%, 85%)`);
      innerGradient.addColorStop(1, `hsla(${hue}, 90%, 75%, 0.7)`);
      ctx.beginPath();
      ctx.arc(center.x, center.y, innerRadius, 0, Math.PI * 2);
      ctx.fillStyle = innerGradient;
      ctx.fill();
    }
  }

  // Audio callback: push time-domain data into FFT input
  function audioCallback(timeDomainData) {
    for (let i = 0; i < timeDomainData.length; i++) {
      fftPush(timeDomainData[i]);
    }
  }

  // ---------- Playlist Management (identical logic, translated UI) ----------
  function addTrack(file) {
    const url = URL.createObjectURL(file);
    const name = file.name.length > 48 ? file.name.slice(0, 45) + '...' : file.name;
    playlist.push({ name, url, duration: 0 });
    if (playlist.length === 1) {
      loadTrack(0).then(() => {
        renderPlaylist();
        updateNowPlaying();
        scrollToCurrent();
      });
    } else {
      renderPlaylist();
    }
  }

  function deleteTrack(idx) {
    if (idx < 0 || idx >= playlist.length) return;
    URL.revokeObjectURL(playlist[idx].url);
    playlist.splice(idx, 1);
    if (playlist.length === 0) {
      audioElement.pause();
      audioElement.src = '';
      isPlaying = false;
      playPauseBtn.innerHTML = '▶';
      currentTrackIndex = -1;
      nowPlayingLabel.innerText = '✨ No track loaded';
      durationSpan.innerText = '0:00';
      progressSlider.value = 0;
      renderPlaylist();
      return;
    }
    if (currentTrackIndex >= playlist.length) currentTrackIndex = playlist.length - 1;
    if (currentTrackIndex === idx || (currentTrackIndex > idx && currentTrackIndex > 0)) {
      if (currentTrackIndex > idx) currentTrackIndex--;
      loadTrack(currentTrackIndex).then(() => { if (isPlaying) playCurrent(); else updateNowPlaying(); });
    }
    renderPlaylist();
    scrollToCurrent();
  }

  async function loadTrack(index) {
    if (playlist.length === 0) return false;
    if (index < 0) index = 0;
    if (index >= playlist.length) index = playlist.length - 1;
    currentTrackIndex = index;
    const track = playlist[currentTrackIndex];
    if (!track.url) return false;
    const wasPlaying = isPlaying;
    if (wasPlaying) audioElement.pause();
    audioElement.src = track.url;
    audioElement.load();
    return new Promise((resolve) => {
      audioElement.onloadedmetadata = () => {
        track.duration = audioElement.duration;
        durationSpan.innerText = formatTime(track.duration);
        progressSlider.max = track.duration;
        if (wasPlaying) audioElement.play().catch(e => console.warn);
        updateNowPlaying();
        renderPlaylist();
        scrollToCurrent();
        resolve(true);
      };
      audioElement.onerror = () => resolve(false);
    });
  }

  async function playCurrent() {
    if (playlist.length === 0) return;
    if (!audioElement.src) await loadTrack(currentTrackIndex);
    if (!audioCtx) await initAudioContext();
    if (audioCtx.state === 'suspended') await audioCtx.resume();
    if (!sourceNode && audioCtx) {
      sourceNode = audioCtx.createMediaElementSource(audioElement);
      sourceNode.connect(analyserNode);
      analyserNode.connect(audioCtx.destination);
    }
    await audioElement.play();
    isPlaying = true;
    playPauseBtn.innerHTML = '⏸';
  }

  function pauseCurrent() {
    audioElement.pause();
    isPlaying = false;
    playPauseBtn.innerHTML = '▶';
  }

  function togglePlayPause() {
    if (playlist.length === 0) return;
    isPlaying ? pauseCurrent() : playCurrent();
  }

  async function nextTrack() {
    if (playlist.length === 0) return;
    if (playMode === 'loop') {
      audioElement.currentTime = 0;
      if (isPlaying) playCurrent();
      else playCurrent();
      return;
    }
    let nextIdx = currentTrackIndex;
    if (playMode === 'shuffle') {
      do { nextIdx = Math.floor(Math.random() * playlist.length); } while (nextIdx === currentTrackIndex && playlist.length > 1);
    } else if (playMode === 'list') {
      nextIdx = (currentTrackIndex + 1) % playlist.length;
    }
    await changeTrack(nextIdx, true);
  }

  async function prevTrack() {
    if (playlist.length === 0) return;
    let prevIdx = currentTrackIndex - 1;
    if (playMode === 'shuffle') {
      do { prevIdx = Math.floor(Math.random() * playlist.length); } while (prevIdx === currentTrackIndex && playlist.length > 1);
    } else {
      if (prevIdx < 0) prevIdx = playlist.length - 1;
    }
    await changeTrack(prevIdx, true);
  }

  async function changeTrack(index, autoPlay) {
    await loadTrack(index);
    if (autoPlay) await playCurrent();
    else updateNowPlaying();
    renderPlaylist();
    scrollToCurrent();
    prevBarTopY.fill(null);   // reset trail history
  }

  function updateNowPlaying() {
    if (playlist.length && playlist[currentTrackIndex]) {
      nowPlayingLabel.innerText = `🎧 ${playlist[currentTrackIndex].name}`;
    } else {
      nowPlayingLabel.innerText = '✨ No track loaded';
    }
  }

  function updateProgress() {
    if (audioElement && !isNaN(audioElement.duration) && audioElement.duration > 0) {
      const cur = audioElement.currentTime;
      progressSlider.value = cur;
      currentTimeSpan.innerText = formatTime(cur);
    }
  }

  function seekTo(val) {
    if (audioElement) audioElement.currentTime = parseFloat(val);
  }

  function formatTime(sec) {
    if (isNaN(sec)) return '0:00';
    const m = Math.floor(sec / 60);
    const s = Math.floor(sec % 60);
    return `${m}:${s < 10 ? '0' : ''}${s}`;
  }

  function renderPlaylist() {
    playlistDiv.innerHTML = '';
    if (playlist.length === 0) {
      playlistDiv.innerHTML = '<div class="empty-playlist">🎤 Click below to add music</div>';
      return;
    }
    playlist.forEach((track, idx) => {
      const div = document.createElement('div');
      div.className = 'playlist-item' + (idx === currentTrackIndex ? ' active' : '');
      div.innerHTML = `<div class="track-info"><div class="track-name">${escapeHtml(track.name)}</div><div class="track-duration">${track.duration ? formatTime(track.duration) : '--:--'}</div></div><button class="delete-track" data-idx="${idx}">🗑️</button>`;
      div.addEventListener('click', (e) => {
        if (!e.target.classList.contains('delete-track')) {
          if (idx === currentTrackIndex) togglePlayPause();
          else changeTrack(idx, true);
        }
      });
      div.querySelector('.delete-track').addEventListener('click', (e) => { e.stopPropagation(); deleteTrack(idx); });
      playlistDiv.appendChild(div);
    });
  }

  function scrollToCurrent() {
    const active = playlistDiv.querySelector('.playlist-item.active');
    if (active) active.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  }

  function escapeHtml(str) {
    return str.replace(/[&<>]/g, function(m) {
      return m === '&' ? '&amp;' : m === '<' ? '&lt;' : '&gt;';
    });
  }

  function handleFiles(files) {
    for (let f of files) if (f.type.startsWith('audio/')) addTrack(f);
  }

  // ---------- Edge Reveal Interaction (show panel button on mouse hover) ----------
  function initEdgeReveal() {
    let checkEdge = (e) => {
      if (uiPanel.classList.contains('collapsed')) {
        if (e.clientX >= window.innerWidth - 20) edgeReveal.classList.add('show');
        else edgeReveal.classList.remove('show');
      } else {
        edgeReveal.classList.remove('show');
      }
    };
    window.addEventListener('mousemove', checkEdge);
    edgeReveal.querySelector('.reveal-btn').addEventListener('click', () => {
      uiPanel.classList.remove('collapsed');
      edgeReveal.classList.remove('show');
    });
    collapseBtn.addEventListener('click', () => uiPanel.classList.add('collapsed'));
  }

  // ---------- AudioContext initialization ----------
  async function initAudioContext() {
    if (audioCtx && audioCtx.state !== 'closed') return audioCtx;
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    analyserNode = audioCtx.createAnalyser();
    analyserNode.fftSize = FFT_SIZE * 2;
    analyserNode.smoothingTimeConstant = 0.8;
    return audioCtx;
  }

  // ---------- Animation Loop ----------
  let lastFrameTime = 0;
  function animate(timestamp) {
    let dt = Math.min(0.033, (timestamp - lastFrameTime) / 1000);
    if (lastFrameTime === 0) dt = 0.016;
    lastFrameTime = timestamp;

    if (audioCtx && analyserNode && playlist.length > 0) {
      let dataArray = new Float32Array(analyserNode.fftSize);
      analyserNode.getFloatTimeDomainData(dataArray);
      audioCallback(dataArray);
      let m = fftAnalyze(dt);
      const boundary = { x: 0, y: 0, width: canvas.width, height: canvas.height };
      fftRender(boundary, m);
    } else {
      ctx.fillStyle = '#151515';
      ctx.fillRect(0, 0, canvas.width, canvas.height);
    }

    if (audioElement && !audioElement.paused && !isNaN(audioElement.duration)) updateProgress();

    // Auto next track when ended (unless loop mode)
    if (audioElement && audioElement.ended && playlist.length > 0) {
      if (playMode === 'loop') {
        audioElement.currentTime = 0;
        playCurrent();
      } else {
        nextTrack().catch(e => console.warn);
      }
    }

    requestAnimationFrame(animate);
  }

  // ---------- Event Binding ----------
  function bindEvents() {
    playPauseBtn.addEventListener('click', togglePlayPause);
    prevBtn.addEventListener('click', prevTrack);
    nextBtn.addEventListener('click', nextTrack);
    progressSlider.addEventListener('input', (e) => {
      progressSlider.dragging = true;
      seekTo(e.target.value);
    });
    progressSlider.addEventListener('change', () => progressSlider.dragging = false);
    uploadBtn.addEventListener('click', () => fileInput.click());
    fileInput.addEventListener('change', (e) => {
      if (e.target.files) handleFiles(Array.from(e.target.files));
      fileInput.value = '';
    });
    document.querySelectorAll('.mode-btn').forEach(btn => {
      btn.addEventListener('click', () => {
        document.querySelectorAll('.mode-btn').forEach(b => b.classList.remove('active'));
        btn.classList.add('active');
        playMode = btn.getAttribute('data-mode');
      });
    });
    document.querySelector('.mode-btn[data-mode="list"]').classList.add('active');
    window.addEventListener('dragover', e => e.preventDefault());
    window.addEventListener('drop', e => { e.preventDefault(); });   // disable drag & drop add (only button)
    audioElement.addEventListener('timeupdate', () => {
      if (!progressSlider.dragging) {
        progressSlider.value = audioElement.currentTime;
        currentTimeSpan.innerText = formatTime(audioElement.currentTime);
      }
    });
    audioElement.addEventListener('play', () => {
      isPlaying = true;
      playPauseBtn.innerHTML = '⏸';
    });
    audioElement.addEventListener('pause', () => {
      isPlaying = false;
      playPauseBtn.innerHTML = '▶';
    });
  }

  // ---------- Start ----------
  async function start() {
    canvas.width = window.innerWidth;
    canvas.height = window.innerHeight;
    bindEvents();
    initEdgeReveal();
    await initAudioContext();
    renderPlaylist();
    requestAnimationFrame(animate);
  }
  start();
})();
