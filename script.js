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
  const searchInput = document.getElementById('searchInput');
  const helpBtn = document.getElementById('helpBtn');
  const helpModal = document.getElementById('helpModal');
  const closeHelpBtn = document.getElementById('closeHelpBtn');

  // Panel size persistence
  let leftWidth = parseInt(localStorage.getItem('pake-left-width')) || 280;
  let panelHeight = parseInt(localStorage.getItem('pake-panel-height')) || 45;
  const leftMin = 180, leftMax = Math.floor(window.innerWidth * 0.5);
  const panelMin = 20, panelMax = 66;

  // Audio
  let audioElement = new Audio();
  let audioCtx = null;
  let sourceNode = null;
  let analyserNode = null;
  let isPlaying = false;

  let playlist = [];
  let currentTrackIndex = 0;
  let playMode = 'list';
  let currentVolume = 0.8;
  let isMuted = false;
  let lastVolume = currentVolume;

  // Drag state
  let isResizingX = false, isResizingY = false;
  let startX, startY, startWidth, startHeight;

  let searchKeyword = '';

  // ---------- FFT (untouched) ----------
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

  function audioCallback(timeDomainData) {
    for (let i = 0; i < timeDomainData.length; i++) fftPush(timeDomainData[i]);
  }

  // HSV helper
  function hsvToRgb(h, s, v) {
    let r, g, b;
    const i = Math.floor(h * 6);
    const f = h * 6 - i;
    const p = v * (1 - s);
    const q = v * (1 - f * s);
    const t = v * (1 - (1 - f) * s);
    switch (i % 6) {
      case 0: r = v; g = t; b = p; break;
      case 1: r = q; g = v; b = p; break;
      case 2: r = p; g = v; b = t; break;
      case 3: r = p; g = q; b = v; break;
      case 4: r = t; g = p; b = v; break;
      default: r = v; g = p; b = q; break;
    }
    return { r, g, b };
  }

  // WebGL renderer (unchanged logic)
  let gl, barProgram, circleProgram, glCanvas;
  let barColorLoc, barPosLoc, barTexLoc;
  let circleRadiusLoc, circlePowerLoc, circleColorLoc, circlePosLoc, circleTexLoc;

  function compileShader(gl, src, type) {
    const shader = gl.createShader(type);
    gl.shaderSource(shader, src);
    gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
      console.error(gl.getShaderInfoLog(shader));
      gl.deleteShader(shader);
      return null;
    }
    return shader;
  }

  function initWebGL() {
    glCanvas = document.getElementById('gl-canvas');
    if (!glCanvas) return false;
    gl = glCanvas.getContext('webgl') || glCanvas.getContext('experimental-webgl');
    if (!gl) return false;

    const vsSource = `
      attribute vec2 a_position;
      attribute vec2 a_texCoord;
      varying vec2 v_texCoord;
      void main() {
        gl_Position = vec4(a_position, 0.0, 1.0);
        v_texCoord = a_texCoord;
      }
    `;
    const barFsSource = `
      precision mediump float;
      uniform vec4 u_color;
      void main() {
        gl_FragColor = u_color;
      }
    `;
    const circleFsSource = `
      precision mediump float;
      varying vec2 v_texCoord;
      uniform vec4 u_color;
      uniform float u_radius;
      uniform float u_power;
      void main() {
        float r = u_radius;
        vec2 p = v_texCoord - vec2(0.5);
        float len = length(p);
        if (len <= 0.5) {
          float s = len - r;
          if (s <= 0.0) {
            gl_FragColor = u_color * 1.5;
          } else {
            float t = 1.0 - s / (0.5 - r);
            float alpha = pow(t, u_power);
            gl_FragColor = mix(vec4(u_color.rgb, 0.0), u_color * 1.5, alpha);
          }
        } else {
          gl_FragColor = vec4(0.0);
        }
      }
    `;

    const vs = compileShader(gl, vsSource, gl.VERTEX_SHADER);
    const barFs = compileShader(gl, barFsSource, gl.FRAGMENT_SHADER);
    const circleFs = compileShader(gl, circleFsSource, gl.FRAGMENT_SHADER);
    if (!vs || !barFs || !circleFs) return false;

    barProgram = gl.createProgram();
    gl.attachShader(barProgram, vs);
    gl.attachShader(barProgram, barFs);
    gl.linkProgram(barProgram);
    circleProgram = gl.createProgram();
    gl.attachShader(circleProgram, vs);
    gl.attachShader(circleProgram, circleFs);
    gl.linkProgram(circleProgram);

    gl.useProgram(barProgram);
    barColorLoc = gl.getUniformLocation(barProgram, 'u_color');
    barPosLoc = gl.getAttribLocation(barProgram, 'a_position');
    barTexLoc = gl.getAttribLocation(barProgram, 'a_texCoord');
    gl.enableVertexAttribArray(barPosLoc);
    gl.enableVertexAttribArray(barTexLoc);

    gl.useProgram(circleProgram);
    circleColorLoc = gl.getUniformLocation(circleProgram, 'u_color');
    circleRadiusLoc = gl.getUniformLocation(circleProgram, 'u_radius');
    circlePowerLoc = gl.getUniformLocation(circleProgram, 'u_power');
    circlePosLoc = gl.getAttribLocation(circleProgram, 'a_position');
    circleTexLoc = gl.getAttribLocation(circleProgram, 'a_texCoord');
    gl.enableVertexAttribArray(circlePosLoc);
    gl.enableVertexAttribArray(circleTexLoc);

    gl.disable(gl.DEPTH_TEST);
    gl.enable(gl.BLEND);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
    return true;
  }

  function resizeWebGL() {
    if (!glCanvas) return;
    const container = document.querySelector('.viz-container');
    if (!container) return;
    const rect = container.getBoundingClientRect();
    glCanvas.width = rect.width;
    glCanvas.height = rect.height;
    gl.viewport(0, 0, glCanvas.width, glCanvas.height);
  }

  function drawRectWithProgram(program, colorLoc, x1, y1, x2, y2, width, height, colorRgba) {
    const nx1 = (x1 / width) * 2 - 1;
    const ny1 = 1 - (y1 / height) * 2;
    const nx2 = (x2 / width) * 2 - 1;
    const ny2 = 1 - (y2 / height) * 2;
    const verts = new Float32Array([
      nx1, ny1, 0, 0,
      nx2, ny1, 1, 0,
      nx1, ny2, 0, 1,
      nx2, ny2, 1, 1
    ]);
    const buffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
    gl.bufferData(gl.ARRAY_BUFFER, verts, gl.STREAM_DRAW);
    const posLoc = (program === barProgram) ? barPosLoc : circlePosLoc;
    const texLoc = (program === barProgram) ? barTexLoc : circleTexLoc;
    gl.vertexAttribPointer(posLoc, 2, gl.FLOAT, false, 16, 0);
    gl.vertexAttribPointer(texLoc, 2, gl.FLOAT, false, 16, 8);
    gl.uniform4f(colorLoc, colorRgba.r, colorRgba.g, colorRgba.b, colorRgba.a);
    gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);
    gl.deleteBuffer(buffer);
  }

  function drawBars(m, boundary) { /* unchanged */
    if (!gl) return;
    gl.useProgram(barProgram);
    const width = glCanvas.width;
    const height = glCanvas.height;
    const cellWidth = boundary.width / m;
    for (let i = 0; i < m; i++) {
      const t = outSmooth[i];
      if (t < 0.001) continue;
      const hue = i / m;
      const color = hsvToRgb(hue, 0.75, 1.0);
      const rgba = { r: color.r, g: color.g, b: color.b, a: 1.0 };
      const centerX = boundary.x + i * cellWidth + cellWidth / 2;
      const topY = boundary.y + boundary.height - boundary.height * 2 / 3 * t;
      const bottomY = boundary.y + boundary.height;
      const thick = cellWidth / 3 * Math.sqrt(t);
      const x1 = centerX - thick * 0.5;
      const x2 = centerX + thick * 0.5;
      drawRectWithProgram(barProgram, barColorLoc, x1, topY, x2, bottomY, width, height, rgba);
    }
  }

  function drawSmears(m, boundary) { /* unchanged */
    if (!gl) return;
    const width = glCanvas.width;
    const height = glCanvas.height;
    const cellWidth = boundary.width / m;
    gl.useProgram(circleProgram);
    gl.uniform1f(circleRadiusLoc, 0.3);
    gl.uniform1f(circlePowerLoc, 3.0);
    for (let i = 0; i < m; i++) {
      const start = outSmear[i];
      const end = outSmooth[i];
      if (start < 0.01 && end < 0.01) continue;
      const hue = i / m;
      const color = hsvToRgb(hue, 0.75, 1.0);
      gl.uniform4f(circleColorLoc, color.r, color.g, color.b, 1.0);
      const centerX = boundary.x + i * cellWidth + cellWidth/2;
      const startY = boundary.y + boundary.height - boundary.height * 2/3 * start;
      const endY = boundary.y + boundary.height - boundary.height * 2/3 * end;
      const radius = cellWidth * 3 * Math.sqrt(end);
      let x1, y1, x2, y2;
      let sourceRect;
      if (endY >= startY) {
        x1 = centerX - radius/2;
        y1 = startY;
        x2 = centerX + radius/2;
        y2 = endY;
        sourceRect = [0, 0, 1, 0.5];
      } else {
        x1 = centerX - radius/2;
        y1 = endY;
        x2 = centerX + radius/2;
        y2 = startY;
        sourceRect = [0, 0.5, 1, 0.5];
      }
      const nx1 = (x1 / width) * 2 - 1;
      const ny1 = 1 - (y1 / height) * 2;
      const nx2 = (x2 / width) * 2 - 1;
      const ny2 = 1 - (y2 / height) * 2;
      const texLeft = sourceRect[0];
      const texRight = sourceRect[0] + sourceRect[2];
      const texTop = sourceRect[1];
      const texBottom = sourceRect[1] + sourceRect[3];
      const positions = new Float32Array([
        nx1, ny1, texLeft, texTop,
        nx2, ny1, texRight, texTop,
        nx1, ny2, texLeft, texBottom,
        nx2, ny2, texRight, texBottom
      ]);
      const buffer = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
      gl.bufferData(gl.ARRAY_BUFFER, positions, gl.STREAM_DRAW);
      gl.vertexAttribPointer(circlePosLoc, 2, gl.FLOAT, false, 16, 0);
      gl.vertexAttribPointer(circleTexLoc, 2, gl.FLOAT, false, 16, 8);
      gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);
      gl.deleteBuffer(buffer);
    }
  }

  function drawCircles(m, boundary) { /* unchanged */
    if (!gl) return;
    const width = glCanvas.width;
    const height = glCanvas.height;
    const cellWidth = boundary.width / m;
    gl.useProgram(circleProgram);
    gl.uniform1f(circleRadiusLoc, 0.07);
    gl.uniform1f(circlePowerLoc, 5.0);
    for (let i = 0; i < m; i++) {
      const t = outSmooth[i];
      if (t < 0.008) continue;
      const hue = i / m;
      const color = hsvToRgb(hue, 0.75, 1.0);
      gl.uniform4f(circleColorLoc, color.r, color.g, color.b, 1.0);
      const centerX = boundary.x + i * cellWidth + cellWidth/2;
      const centerY = boundary.y + boundary.height - boundary.height * 2/3 * t;
      let radius = cellWidth * 6 * Math.sqrt(t);
      const nx = (centerX / width) * 2 - 1;
      const ny = 1 - (centerY / height) * 2;
      const rw = (radius / width) * 2;
      const rh = (radius / height) * 2;
      const left = nx - rw;
      const right = nx + rw;
      const bottom = ny - rh;
      const top = ny + rh;
      const positions = new Float32Array([
        left, bottom, 0, 0,
        right, bottom, 1, 0,
        left, top, 0, 1,
        right, top, 1, 1
      ]);
      const buffer = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
      gl.bufferData(gl.ARRAY_BUFFER, positions, gl.STREAM_DRAW);
      gl.vertexAttribPointer(circlePosLoc, 2, gl.FLOAT, false, 16, 0);
      gl.vertexAttribPointer(circleTexLoc, 2, gl.FLOAT, false, 16, 8);
      gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);
      gl.deleteBuffer(buffer);
    }
  }

  // ---------- Helper functions (UI) ----------
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
      document.getElementById('volumeIcon').innerHTML = '<i class="fas fa-volume-up"></i>';
      audioElement.volume = lastVolume;
      setVolume(lastVolume);
      isMuted = false;
    } else {
      document.getElementById('volumeIcon').innerHTML = '<i class="fas fa-volume-mute"></i>';
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

  function resetVisualizationState() {
    for (let i = 0; i < outSmooth.length; i++) {
      outSmooth[i] = 0;
      outSmear[i] = 0;
    }
    for (let i = 0; i < inRaw.length; i++) inRaw[i] = 0;
    ctx.fillStyle = '#0D0C0C';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    if (gl) {
      gl.clearColor(0, 0, 0, 0);
      gl.clear(gl.COLOR_BUFFER_BIT);
    }
  }

  // ---------- Playlist logic (unchanged except english UI strings) ----------
  function getFilteredIndices() {
    if (!searchKeyword.trim()) return playlist.map((_, idx) => idx);
    const kw = searchKeyword.trim().toLowerCase();
    return playlist.reduce((acc, track, idx) => {
      if (track.name.toLowerCase().includes(kw)) acc.push(idx);
      return acc;
    }, []);
  }

  function renderPlaylist() {
    playlistDiv.innerHTML = '';
    const filteredIdx = getFilteredIndices();
    if (filteredIdx.length === 0) {
      playlistDiv.innerHTML = '<div class="empty-playlist">🎵 No matching tracks</div>';
      return;
    }
    const containerWidth = playlistDiv.clientWidth - 48;
    filteredIdx.forEach(originalIdx => {
      const track = playlist[originalIdx];
      const div = document.createElement('div');
      const isActive = (originalIdx === currentTrackIndex);
      div.className = 'playlist-item' + (isActive ? ' active' : '');
      const trackInfo = document.createElement('div');
      trackInfo.className = 'track-info';
      const dummy = document.createElement('span');
      dummy.style.position = 'absolute';
      dummy.style.visibility = 'hidden';
      dummy.style.whiteSpace = 'nowrap';
      dummy.style.fontSize = '1rem';
      dummy.style.fontWeight = '500';
      dummy.textContent = track.name;
      document.body.appendChild(dummy);
      const textWidth = dummy.offsetWidth;
      document.body.removeChild(dummy);
      const needMarquee = isActive && textWidth > containerWidth;
      if (needMarquee) {
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
        if (originalIdx === currentTrackIndex) togglePlayPause();
        else changeTrack(originalIdx, true);
      });
      deleteBtn.addEventListener('click', (e) => { e.stopPropagation(); deleteTrack(originalIdx); });
      playlistDiv.appendChild(div);
    });
    scrollToCurrent();
  }

  function scrollToCurrent() {
    const activeItem = playlistDiv.querySelector('.playlist-item.active');
    if (activeItem) activeItem.scrollIntoView({ behavior: 'instant', block: 'center' });
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
      // playPauseBtn.innerHTML = '▶';
      playPauseBtn.innerHTML = '<i class="fas fa-play"></i>';
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
    // playPauseBtn.innerHTML = '⏸';
    playPauseBtn.innerHTML = '<i class="fas fa-pause"></i>';
  }

  function pauseCurrent() {
    audioElement.pause();
    isPlaying = false;
    // playPauseBtn.innerHTML = '▶';
    playPauseBtn.innerHTML = '<i class="fas fa-play"></i>';
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
    resetVisualizationState();
  }

  function updateNowPlaying() {
    if (playlist.length && playlist[currentTrackIndex]) {
      nowPlayingLabel.innerText = `✨ ${playlist[currentTrackIndex].name}`;
    } else {
      nowPlayingLabel.innerText = '✨ No track loaded';
    }
  }

  function addTrack(file) {
    const url = URL.createObjectURL(file);
    const name = file.name;
    playlist.push({ name, url });
    if (playlist.length === 1) {
      loadTrack(0).then(() => { renderPlaylist(); updateNowPlaying(); });
    } else {
      renderPlaylist();
    }
  }

  function handleFiles(files) {
    for (let f of files) if (f.type.startsWith('audio/')) addTrack(f);
  }

  // ---------- Audio Context ----------
  async function initAudioContext() {
    if (audioCtx && audioCtx.state !== 'closed') return audioCtx;
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    analyserNode = audioCtx.createAnalyser();
    analyserNode.fftSize = FFT_SIZE * 2;
    analyserNode.smoothingTimeConstant = 0.8;
    return audioCtx;
  }

  // ---------- Canvas & Animation ----------
  function resizeCanvas() {
    const container = document.querySelector('.viz-container');
    if (!container) return;
    const rect = container.getBoundingClientRect();
    canvas.width = rect.width;
    canvas.height = rect.height;
    ctx.fillStyle = '#0D0C0C';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    resizeWebGL();
  }

  let lastFrameTime = 0;
  let currentM = 0;

  function animate(timestamp) {
    let dt = Math.min(0.033, (timestamp - lastFrameTime) / 1000);
    if (lastFrameTime === 0) dt = 0.016;
    lastFrameTime = timestamp;
    if (isPlaying && audioCtx && analyserNode && playlist.length > 0) {
      let dataArray = new Float32Array(analyserNode.fftSize);
      analyserNode.getFloatTimeDomainData(dataArray);
      audioCallback(dataArray);
      currentM = fftAnalyze(dt);
    }
    const boundary = { x: 0, y: 0, width: canvas.width, height: canvas.height };
    if (gl) {
      gl.clearColor(0, 0, 0, 0);
      gl.clear(gl.COLOR_BUFFER_BIT);
      if (currentM > 0) {
        drawBars(currentM, boundary);
        drawSmears(currentM, boundary);
        drawCircles(currentM, boundary);
      }
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

  function updateProgress() {
    if (audioElement && !isNaN(audioElement.duration) && audioElement.duration > 0) {
      const cur = audioElement.currentTime;
      progressSlider.value = cur;
      currentTimeSpan.innerText = formatTime(cur);
      updateProgressRange();
    }
  }

  // ---------- Resize Handlers ----------
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
        newWidth = Math.min(leftMax, Math.max(leftMin, newWidth));
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
      resizeWebGL();
    });
  }

  function initResizeObserver() {
    let resizeTimer;
    window.addEventListener('resize', () => {
      clearTimeout(resizeTimer);
      resizeTimer = setTimeout(() => {
        resizeCanvas();
        renderPlaylist();
        resetVisualizationState();
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

  // ---------- Event Binding ----------
  function bindEvents() {
    playPauseBtn.addEventListener('click', togglePlayPause);
    prevBtn.addEventListener('click', prevTrack);
    nextBtn.addEventListener('click', nextTrack);
    progressSlider.addEventListener('input', (e) => {
      audioElement.currentTime = parseFloat(e.target.value);
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
    audioElement.addEventListener('timeupdate', () => {
      progressSlider.value = audioElement.currentTime;
      currentTimeSpan.innerText = formatTime(audioElement.currentTime);
      updateProgressRange();
    });
    // audioElement.addEventListener('play', () => { isPlaying = true; playPauseBtn.innerHTML = '⏸'; });
    // audioElement.addEventListener('pause', () => { isPlaying = false; playPauseBtn.innerHTML = '▶'; });
    audioElement.addEventListener('play', () => { isPlaying = true; playPauseBtn.innerHTML = '<i class="fas fa-pause"></i>'; });
    audioElement.addEventListener('pause', () => { isPlaying = false; playPauseBtn.innerHTML = '<i class="fas fa-play"></i>'; });
    volumeSlider.addEventListener('input', (e) => setVolume(parseFloat(e.target.value)));
  }

  function handleKeydown(e) {
    if (document.activeElement === searchInput) return;

    const key = e.key.toLowerCase();
    if (key === 'e') {
      e.preventDefault();
      const viz = document.querySelector('.viz-container');
      viz.classList.add('fade-out');
      setTimeout(() => {
        document.body.classList.toggle('ui-hidden');
        resizeCanvas();
        resetVisualizationState();
        viz.classList.remove('fade-out');
      }, 200);
    } else if (key === 'a') { e.preventDefault(); prevTrack(); }
    else if (key === 'd') { e.preventDefault(); nextTrack(); }
    else if (key === 'w') { e.preventDefault(); setVolume(currentVolume + 0.1); }
    else if (key === 's') { e.preventDefault(); setVolume(currentVolume - 0.1); }
    else if (key === 'q') { e.preventDefault(); toggleMute(); }
    else if (key === ' ') { e.preventDefault(); togglePlayPause(); }
    else if (key === 'c') {
      e.preventDefault();
      const modes = ['list', 'shuffle', 'loop'];
      let nextIndex = (modes.indexOf(playMode) + 1) % modes.length;
      playMode = modes[nextIndex];
      document.querySelectorAll('.mode-btn').forEach(btn => {
        if (btn.getAttribute('data-mode') === playMode) btn.classList.add('active');
        else btn.classList.remove('active');
      });
    }
  }

  function initHelpModal() {
    helpBtn.addEventListener('click', () => helpModal.classList.add('active'));
    closeHelpBtn.addEventListener('click', () => helpModal.classList.remove('active'));
    helpModal.addEventListener('click', (e) => {
      if (e.target === helpModal) helpModal.classList.remove('active');
    });
  }

  function initSearch() {
    searchInput.addEventListener('input', (e) => {
      searchKeyword = e.target.value;
      renderPlaylist();
    });
    searchInput.addEventListener('keydown', (e) => e.stopPropagation());
  }

  // ---------- Start ----------
  async function start() {
    bindEvents();
    await initAudioContext();
    initResizeHandles();
    resizeCanvas();
    initResizeObserver();
    setVolume(currentVolume);
    updateRangeStyle(progressSlider, 0, 1, '#5a6bc0', '#3a3a4a');
    document.addEventListener('keydown', handleKeydown);
    initHelpModal();
    initSearch();
    renderPlaylist();
    if (!initWebGL()) console.warn('WebGL not supported, glow disabled');
    requestAnimationFrame(animate);
  }
  start();
})();
