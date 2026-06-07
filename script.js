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
  const nowPlayingLabel = document.getElementById('nowPlayingLabel');
  const volumeSlider = document.getElementById('volumeSlider');
  const volumePercent = document.getElementById('volumePercent');

  // Panel size persistence
  let leftWidth = parseInt(localStorage.getItem('pake-left-width')) || 280;
  let panelHeight = parseInt(localStorage.getItem('pake-panel-height')) || 33;
  const leftMin = 180, leftMax = Math.floor(window.innerWidth * 0.5);
  const panelMin = 20, panelMax = 66;

  // Audio related
  let audioElement = new Audio();
  let audioCtx = null;
  let sourceNode = null;
  let analyserNode = null;
  let isPlaying = false;

  let playlist = [];
  let currentTrackIndex = 0;
  let playMode = 'list';   // 'list', 'shuffle', 'loop'

  let currentVolume = 0.8;
  let isMuted = false;
  let lastVolume = currentVolume;

  // Drag state
  let isResizingX = false, isResizingY = false;
  let startX, startY, startWidth, startHeight;

  // ---------- FFT core algorithm (unchanged) ----------
  const FFT_SIZE = 8192;
  let inRaw = new Float32Array(FFT_SIZE);
  let inWin = new Float32Array(FFT_SIZE);
  let outRawReal = new Float32Array(FFT_SIZE);
  let outRawImag = new Float32Array(FFT_SIZE);
  let outLog = new Float32Array(FFT_SIZE);
  let outSmooth = new Float32Array(FFT_SIZE);
  let outSmear = new Float32Array(FFT_SIZE);
  let hannWindow = new Float32Array(FFT_SIZE);
  for (let i = 0; i < FFT_SIZE; i++) {
    let t = i / (FFT_SIZE - 1);
    hannWindow[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * t);
  }

  function fft(real, imag, n) {
    for (let i = 1, j = 0; i < n; i++) {
      let bit = n >> 1;
      while (j & bit) { j ^= bit; bit >>= 1; }
      j ^= bit;
      if (i < j) {
        [real[i], real[j]] = [real[j], real[i]];
        [imag[i], imag[j]] = [imag[j], imag[i]];
      }
    }
    for (let len = 2; len <= n; len <<= 1) {
      let ang = 2 * Math.PI / len;
      let wLenReal = Math.cos(ang);
      let wLenImag = Math.sin(ang);
      for (let i = 0; i < n; i += len) {
        let wReal = 1, wImag = 0;
        for (let j = 0; j < len/2; j++) {
          let uReal = real[i+j], uImag = imag[i+j];
          let vReal = real[i+j+len/2] * wReal - imag[i+j+len/2] * wImag;
          let vImag = real[i+j+len/2] * wImag + imag[i+j+len/2] * wReal;
          real[i+j] = uReal + vReal;
          imag[i+j] = uImag + vImag;
          real[i+j+len/2] = uReal - vReal;
          imag[i+j+len/2] = uImag - vImag;
          let nextWReal = wReal * wLenReal - wImag * wLenImag;
          let nextWImag = wReal * wLenImag + wImag * wLenReal;
          wReal = nextWReal; wImag = nextWImag;
        }
      }
    }
  }
  function amp(real, imag) { return Math.log(real*real + imag*imag); }
  function fftAnalyze(dt) {
    for (let i = 0; i < FFT_SIZE; i++) inWin[i] = inRaw[i] * hannWindow[i];
    for (let i = 0; i < FFT_SIZE; i++) { outRawReal[i] = inWin[i]; outRawImag[i] = 0; }
    fft(outRawReal, outRawImag, FFT_SIZE);
    let step = 1.06, lowf = 1.0, m = 0, maxAmp = 1.0;
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
    for (let i = 0; i < m; i++) outLog[i] /= maxAmp;
    const smoothness = 8.0, smearness = 3.0;
    for (let i = 0; i < m; i++) {
      outSmooth[i] += (outLog[i] - outSmooth[i]) * smoothness * dt;
      outSmear[i] += (outSmooth[i] - outSmear[i]) * smearness * dt;
    }
    return m;
  }
  function fftPush(frame) {
    for (let i = 0; i < FFT_SIZE-1; i++) inRaw[i] = inRaw[i+1];
    inRaw[FFT_SIZE-1] = frame;
  }
  let prevBarTopY = [], prevBarRadius = [], prevBarCount = 0;
  function fftRender(boundary, m) {
    const cellWidth = boundary.width / m;
    if (prevBarCount !== m) {
      prevBarTopY = new Array(m).fill(null);
      prevBarRadius = new Array(m).fill(0);
      prevBarCount = m;
    }
    ctx.fillStyle = '#0D0C0C';
    ctx.fillRect(boundary.x, boundary.y, boundary.width, boundary.height);
    for (let i = 0; i < m; i++) {
      let t = outSmooth[i];
      let hue = (i / m) * 360;
      let vividColor = `hsl(${hue}, 100%, 65%)`;
      const startX = boundary.x + i * cellWidth + cellWidth/2;
      const startY = boundary.y + boundary.height - boundary.height * 2/3 * t;
      const endX = startX, endY = boundary.y + boundary.height;
      const thick = cellWidth * 0.25 * Math.sqrt(t);
      ctx.beginPath();
      ctx.moveTo(startX, startY);
      ctx.lineTo(endX, endY);
      ctx.lineWidth = thick;
      ctx.strokeStyle = vividColor;
      ctx.lineCap = 'round';
      ctx.stroke();
    }
    for (let i = 0; i < m; i++) {
      const tCurr = outSmooth[i];
      if (tCurr < 0.01) continue;
      const hue = (i / m) * 360;
      const currX = boundary.x + i * cellWidth + cellWidth/2;
      const currY = boundary.y + boundary.height - boundary.height * 2/3 * tCurr;
      let ballRadius = cellWidth * 2.2 * Math.sqrt(tCurr);
      ballRadius = Math.min(ballRadius, cellWidth * 1.2);
      const maxTrailRadius = ballRadius * 0.55, minTrailRadius = maxTrailRadius * 0.15;
      if (prevBarTopY[i] !== null) {
        const prevY = prevBarTopY[i];
        const dy = currY - prevY;
        const distance = Math.abs(dy);
        if (distance > 1) {
          let steps = Math.min(30, Math.max(10, Math.floor(distance / 2)));
          for (let step = 1; step <= steps; step++) {
            const t = step / steps;
            const interpY = prevY + dy * t;
            const radius = minTrailRadius + (maxTrailRadius - minTrailRadius) * t;
            const alpha = 0.85 * t;
            ctx.beginPath();
            ctx.arc(currX, interpY, radius, 0, Math.PI*2);
            ctx.fillStyle = `hsla(${hue}, 80%, 65%, ${alpha})`;
            ctx.fill();
          }
        }
      }
      prevBarTopY[i] = currY;
      prevBarRadius[i] = ballRadius;
    }
    for (let i = 0; i < m; i++) {
      let t = outSmooth[i];
      if (t < 0.008) continue;
      let hue = (i / m) * 360;
      const centerX = boundary.x + i * cellWidth + cellWidth/2;
      const centerY = boundary.y + boundary.height - boundary.height * 2/3 * t;
      let radius = cellWidth * 3.2 * Math.sqrt(t);
      const gradient = ctx.createRadialGradient(centerX, centerY, 0, centerX, centerY, radius);
      gradient.addColorStop(0, `hsl(${hue}, 92%, 78%)`);
      gradient.addColorStop(0.4, `hsl(${hue}, 88%, 68%)`);
      gradient.addColorStop(1, `hsla(${hue}, 80%, 55%, 0)`);
      ctx.beginPath();
      ctx.arc(centerX, centerY, radius, 0, Math.PI*2);
      ctx.fillStyle = gradient;
      ctx.fill();
    }
  }
  function audioCallback(timeDomainData) {
    for (let i = 0; i < timeDomainData.length; i++) fftPush(timeDomainData[i]);
  }

  // ---------- Helper functions ----------
  function formatTime(sec) {
    if (isNaN(sec)) return '0:00';
    const m = Math.floor(sec / 60);
    const s = Math.floor(sec % 60);
    return `${m}:${s < 10 ? '0' : ''}${s}`;
  }
  function setVolume(value) {
    let vol = Math.min(1, Math.max(0, value));
    currentVolume = vol;
    if (!isMuted) audioElement.volume = vol;
    volumeSlider.value = vol;
    volumePercent.innerText = Math.round(vol * 100) + '%';
    updateRangeStyle(volumeSlider, vol, 1, '#5a6bc0', '#3a3a4a');
  }
  function toggleMute() {
    if (isMuted) {
      audioElement.volume = lastVolume;
      setVolume(lastVolume);
      isMuted = false;
    } else {
      lastVolume = currentVolume;
      audioElement.volume = 0;
      isMuted = true;
      volumePercent.innerText = 'Mute';
    }
  }
  function updateRangeStyle(range, value, max, colorActive, colorInactive) {
    let percent = (value / max) * 100;
    range.style.background = `linear-gradient(to right, ${colorActive} 0%, ${colorActive} ${percent}%, ${colorInactive} ${percent}%, ${colorInactive} 100%)`;
  }
  function updateProgressRange() {
    if (audioElement && audioElement.duration) {
      let percent = (audioElement.currentTime / audioElement.duration) * 100;
      progressSlider.style.background = `linear-gradient(to right, #5a6bc0 0%, #5a6bc0 ${percent}%, #3a3a4a ${percent}%, #3a3a4a 100%)`;
    }
  }

  // Reset visualization state (used when toggling UI to remove artifacts)
  function resetVisualizationState() {
    for (let i = 0; i < outSmooth.length; i++) {
      outSmooth[i] = 0;
      outSmear[i] = 0;
    }
    for (let i = 0; i < inRaw.length; i++) {
      inRaw[i] = 0;
    }
    prevBarTopY = [];
    prevBarRadius = [];
    prevBarCount = 0;
    ctx.fillStyle = '#0D0C0C';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
  }

  // ---------- Playlist management ----------
  function addTrack(file) {
    const url = URL.createObjectURL(file);
    const name = file.name;
    playlist.push({ name, url });
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
    const wasCurrent = (idx === currentTrackIndex);
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

    if (wasCurrent) {
      if (idx >= playlist.length) currentTrackIndex = playlist.length - 1;
      else currentTrackIndex = idx;
      loadTrack(currentTrackIndex).then(() => {
        if (isPlaying) playCurrent();
        else updateNowPlaying();
      });
    } else if (idx < currentTrackIndex) {
      currentTrackIndex--;
      renderPlaylist();
      updateNowPlaying();
    } else {
      renderPlaylist();
      updateNowPlaying();
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
        durationSpan.innerText = formatTime(audioElement.duration);
        progressSlider.max = audioElement.duration;
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
    } else {
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
    resetVisualizationState();
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
      updateProgressRange();
    }
  }
  function seekTo(val) { if (audioElement) audioElement.currentTime = parseFloat(val); }

  // Render playlist (only currently playing song can scroll)
  function renderPlaylist() {
    playlistDiv.innerHTML = '';
    if (playlist.length === 0) {
      playlistDiv.innerHTML = '<div class="empty-playlist">🎤 Click below to add music</div>';
      return;
    }
    const containerWidth = playlistDiv.clientWidth - 48;
    const dummy = document.createElement('span');
    dummy.style.position = 'absolute';
    dummy.style.visibility = 'hidden';
    dummy.style.whiteSpace = 'nowrap';
    dummy.style.fontSize = '1rem';

    playlist.forEach((track, idx) => {
      const div = document.createElement('div');
      div.className = 'playlist-item' + (idx === currentTrackIndex ? ' active' : '');
      const trackInfo = document.createElement('div');
      trackInfo.className = 'track-info';
      const isActive = (idx === currentTrackIndex);

      dummy.textContent = track.name;
      document.body.appendChild(dummy);
      const textWidth = dummy.offsetWidth;
      document.body.removeChild(dummy);
      const needScroll = isActive && textWidth > containerWidth;

      if (needScroll) {
        const wrapper = document.createElement('div');
        wrapper.className = 'marquee-wrapper';
        const content = document.createElement('div');
        content.className = 'marquee-content';
        const span1 = document.createElement('span');
        span1.textContent = track.name;
        const span2 = document.createElement('span');
        span2.textContent = track.name;
        content.appendChild(span1);
        content.appendChild(span2);
        wrapper.appendChild(content);
        trackInfo.appendChild(wrapper);
      } else {
        const nameSpan = document.createElement('span');
        nameSpan.className = 'track-name truncate';
        nameSpan.textContent = track.name;
        trackInfo.appendChild(nameSpan);
      }
      const deleteBtn = document.createElement('button');
      deleteBtn.className = 'delete-track';
      deleteBtn.innerHTML = '✕';
      div.appendChild(trackInfo);
      div.appendChild(deleteBtn);
      div.addEventListener('click', (e) => {
        if (e.target === deleteBtn || deleteBtn.contains(e.target)) return;
        if (idx === currentTrackIndex) togglePlayPause();
        else changeTrack(idx, true);
      });
      deleteBtn.addEventListener('click', (e) => { e.stopPropagation(); deleteTrack(idx); });
      playlistDiv.appendChild(div);
    });
  }
  function scrollToCurrent() {
    const active = playlistDiv.querySelector('.playlist-item.active');
    if (active) active.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  }
  function handleFiles(files) {
    for (let f of files) if (f.type.startsWith('audio/')) addTrack(f);
  }

  // Panel resize handling
  function initResizeHandles() {
    const sidebar = document.getElementById('playlistSidebar');
    const handleX = document.getElementById('resizeHandleX');
    const panel = document.getElementById('controlPanel');
    const handleY = document.getElementById('resizeHandleY');
    const mainArea = document.querySelector('.main-area');

    sidebar.style.width = leftWidth + 'px';
    panel.style.height = panelHeight + '%';

    handleX.addEventListener('mousedown', (e) => {
      isResizingX = true;
      startX = e.clientX;
      startWidth = sidebar.offsetWidth;
      document.body.style.cursor = 'ew-resize';
      e.preventDefault();
    });
    handleY.addEventListener('mousedown', (e) => {
      isResizingY = true;
      startY = e.clientY;
      startHeight = panel.offsetHeight;
      document.body.style.cursor = 'ns-resize';
      e.preventDefault();
    });
    window.addEventListener('mousemove', (e) => {
      if (isResizingX) {
        let newWidth = startWidth + (e.clientX - startX);
        const maxWidth = window.innerWidth * 0.5;
        newWidth = Math.min(maxWidth, Math.max(leftMin, newWidth));
        sidebar.style.width = newWidth + 'px';
        localStorage.setItem('pake-left-width', newWidth);
        leftWidth = newWidth;
        renderPlaylist();
      }
      if (isResizingY) {
        let delta = startY - e.clientY;
        let newHeightPx = startHeight + delta;
        let totalHeight = mainArea.clientHeight;
        let newPercent = (newHeightPx / totalHeight) * 100;
        newPercent = Math.min(panelMax, Math.max(panelMin, newPercent));
        panel.style.height = newPercent + '%';
        localStorage.setItem('pake-panel-height', newPercent);
        panelHeight = newPercent;
      }
    });
    window.addEventListener('mouseup', () => {
      if (isResizingX) { isResizingX = false; document.body.style.cursor = ''; }
      if (isResizingY) { isResizingY = false; document.body.style.cursor = ''; }
      resizeCanvas();
    });
  }

  async function initAudioContext() {
    if (audioCtx && audioCtx.state !== 'closed') return audioCtx;
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    analyserNode = audioCtx.createAnalyser();
    analyserNode.fftSize = FFT_SIZE * 2;
    analyserNode.smoothingTimeConstant = 0.8;
    return audioCtx;
  }

  function resizeCanvas() {
    const container = document.querySelector('.viz-container');
    if (!container) return;
    const rect = container.getBoundingClientRect();
    canvas.width = rect.width;
    canvas.height = rect.height;
    ctx.fillStyle = '#0D0C0C';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
  }

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
      ctx.fillStyle = '#0D0C0C';
      ctx.fillRect(0, 0, canvas.width, canvas.height);
    }
    if (audioElement && !audioElement.paused && !isNaN(audioElement.duration)) updateProgress();
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

  function bindEvents() {
    playPauseBtn.addEventListener('click', togglePlayPause);
    prevBtn.addEventListener('click', prevTrack);
    nextBtn.addEventListener('click', nextTrack);
    progressSlider.addEventListener('input', (e) => {
      seekTo(e.target.value);
      updateProgressRange();
    });
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
    window.addEventListener('drop', e => e.preventDefault());
    audioElement.addEventListener('timeupdate', () => {
      progressSlider.value = audioElement.currentTime;
      currentTimeSpan.innerText = formatTime(audioElement.currentTime);
      updateProgressRange();
    });
    audioElement.addEventListener('play', () => { isPlaying = true; playPauseBtn.innerHTML = '⏸'; });
    audioElement.addEventListener('pause', () => { isPlaying = false; playPauseBtn.innerHTML = '▶'; });
    volumeSlider.addEventListener('input', (e) => setVolume(parseFloat(e.target.value)));
  }

  function handleKeydown(e) {
    const key = e.key.toLowerCase();
    if (document.activeElement && document.activeElement.tagName === 'INPUT') return;

    if (key === 'e') {
      e.preventDefault();
      const viz = document.querySelector('.viz-container');

      // Fade out
      viz.classList.add('fade-out');

      // Wait for fade-out animation to complete (200ms)
      setTimeout(() => {
        // Toggle UI visibility
        document.body.classList.toggle('ui-hidden');

        // Resize canvas and reset rendering state
        resizeCanvas();
        resetVisualizationState();

        // Fade in
        viz.classList.remove('fade-out');
      }, 200);
    }
    else if (key === 'a') { e.preventDefault(); prevTrack(); }
    else if (key === 'd') { e.preventDefault(); nextTrack(); }
    else if (key === 'w') { e.preventDefault(); setVolume(currentVolume + 0.1); }
    else if (key === 's') { e.preventDefault(); setVolume(currentVolume - 0.1); }
    else if (key === 'q') { e.preventDefault(); toggleMute(); }
    else if (key === ' ') { e.preventDefault(); togglePlayPause(); }
    else if (key === 'c') {
      e.preventDefault();
      // Cycle play modes
      const modes = ['list', 'shuffle', 'loop'];
      let nextIndex = (modes.indexOf(playMode) + 1) % modes.length;
      playMode = modes[nextIndex];
      // Update UI highlight
      document.querySelectorAll('.mode-btn').forEach(btn => {
        if (btn.getAttribute('data-mode') === playMode) {
          btn.classList.add('active');
        } else {
          btn.classList.remove('active');
        }
      });
    }
  }

  function initResizeObserver() {
    let resizeTimer;
    window.addEventListener('resize', () => {
      clearTimeout(resizeTimer);
      resizeTimer = setTimeout(() => {
        resizeCanvas();
        renderPlaylist();
        resetVisualizationState();  // Reset on window resize to avoid scaling artifacts
        const panel = document.getElementById('controlPanel');
        const mainArea = document.querySelector('.main-area');
        if (panel && mainArea && panelHeight) {
          let totalHeight = mainArea.clientHeight;
          let newPx = (panelHeight / 100) * totalHeight;
          panel.style.height = newPx + 'px';
        }
      }, 100);
    });
  }

  async function start() {
    bindEvents();
    await initAudioContext();
    initResizeHandles();
    resizeCanvas();
    initResizeObserver();
    setVolume(currentVolume);
    updateRangeStyle(progressSlider, 0, 1, '#5a6bc0', '#3a3a4a');
    document.addEventListener('keydown', handleKeydown);
    renderPlaylist();
    requestAnimationFrame(animate);
  }
  start();
})();
