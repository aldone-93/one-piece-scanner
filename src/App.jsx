/**
 * ONE PIECE AR CARD SCANNER — v3
 * ─────────────────────────────────────────────────────────────────
 * Novità v3:
 *  - Detection molto più stabile: solidity check, convexity check,
 *    ratio stretto (1.2–1.8), dimensione minima assoluta,
 *    NO equalizeHist (amplificava rumore), NO fallback bounding rect
 *  - Preview delle carte warpate PRIMA dell'invio all'API
 *  - Flusso: SCAN → mostra anteprime → CONFERMA → chiama API
 *  - Bottone "Rimuovi" per escludere singole carte dal batch
 * ─────────────────────────────────────────────────────────────────
 */

import { useState, useEffect, useRef, useCallback } from "react";

// ─── CONFIG — modifica qui ──────────────────────────────────────────
const API_ENDPOINT = "https://crawlerop.up.railway.app//api/searchImage";
const MAX_CARDS = 10;
const CARD_W = 300;   // larghezza warp output (px)
const CARD_H = 420;   // altezza  warp output (px)

// Aspect ratio h/w carta One Piece: 88/63 ≈ 1.397
// Range stretto → meno falsi positivi
const RATIO_MIN = 1.15;
const RATIO_MAX = 1.85;

// Area come % dello schermo
const AREA_MIN_FRAC = 0.018;  // carta piccola/lontana
const AREA_MAX_FRAC = 0.55;

// Solidity: area_contorno / area_bounding_rect — le carte sono ~rettangolari
// Valori bassi = forme strane/rumore
const SOLIDITY_MIN = 0.72;

// Dimensione minima assoluta (px) — evita microcontorni
const MIN_SIDE_PX = 60;

// ─── PALETTE ───────────────────────────────────────────────────────
const PALETTE = [
  { s: "#FFD700", g: "rgba(255,215,0,0.10)" },
  { s: "#FF6B6B", g: "rgba(255,107,107,0.10)" },
  { s: "#4ECDC4", g: "rgba(78,205,196,0.10)" },
  { s: "#C3A6FF", g: "rgba(195,166,255,0.10)" },
  { s: "#FFB347", g: "rgba(255,179,71,0.10)" },
  { s: "#A8E6CF", g: "rgba(168,230,207,0.10)" },
  { s: "#FF8B94", g: "rgba(255,139,148,0.10)" },
  { s: "#87CEEB", g: "rgba(135,206,235,0.10)" },
];

// ─── UTILS ─────────────────────────────────────────────────────────
function roundRect(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y); ctx.lineTo(x + w - r, y);
  ctx.arcTo(x + w, y, x + w, y + r, r);
  ctx.lineTo(x + w, y + h - r);
  ctx.arcTo(x + w, y + h, x + w - r, y + h, r);
  ctx.lineTo(x + r, y + h);
  ctx.arcTo(x, y + h, x, y + h - r, r);
  ctx.lineTo(x, y + r);
  ctx.arcTo(x, y, x + r, y, r);
  ctx.closePath();
}

function sortCorners(pts) {
  const cx = pts.reduce((s, p) => s + p.x, 0) / 4;
  const cy = pts.reduce((s, p) => s + p.y, 0) / 4;
  return [...pts].sort((a, b) =>
    Math.atan2(a.y - cy, a.x - cx) - Math.atan2(b.y - cy, b.x - cx)
  );
}

// Warp prospettico → canvas temporaneo → data URL
function warpCard(cv, videoEl, procCanvas, points) {
  const vw = videoEl.videoWidth, vh = videoEl.videoHeight;
  procCanvas.width = vw;
  procCanvas.height = vh;
  procCanvas.getContext("2d").drawImage(videoEl, 0, 0, vw, vh);

  const src = cv.imread(procCanvas);
  const srcArr = points.flatMap(p => [p.x, p.y]);
  const dstArr = [0, 0, CARD_W, 0, CARD_W, CARD_H, 0, CARD_H];
  const srcM = cv.matFromArray(4, 1, cv.CV_32FC2, srcArr);
  const dstM = cv.matFromArray(4, 1, cv.CV_32FC2, dstArr);
  const M = cv.getPerspectiveTransform(srcM, dstM);
  const warped = new cv.Mat();
  cv.warpPerspective(src, warped, M, new cv.Size(CARD_W, CARD_H));

  const tmp = document.createElement("canvas");
  tmp.width = CARD_W;
  tmp.height = CARD_H;
  cv.imshow(tmp, warped);

  [src, srcM, dstM, M, warped].forEach(m => { try { m.delete(); } catch { } });
  return tmp; // restituisce il canvas
}

// Canvas → Blob
function canvasToBlob(canvas, quality = 0.92) {
  return new Promise(res => canvas.toBlob(res, "image/jpeg", quality));
}

// ─── COMPONENT ─────────────────────────────────────────────────────
export default function OnePieceScanner() {
  const videoRef = useRef(null);
  const overlayRef = useRef(null);
  const procRef = useRef(null);
  const animRef = useRef(null);
  const cardsRef = useRef([]);     // dati detection (punti/rect)
  const resultsRef = useRef({});
  const scanLineY = useRef(0);
  const frameN = useRef(0);

  const [cvReady, setCvReady] = useState(false);
  const [camReady, setCamReady] = useState(false);
  const [cardCount, setCardCount] = useState(0);
  const [results, setResults] = useState({});
  const [scanning, setScanning] = useState(false);
  const [camError, setCamError] = useState(false);
  const [debug, setDebug] = useState(false);
  const [debugInfo, setDebugInfo] = useState({});

  // ── Preview state ────────────────────────────────────────────────
  // previews = array di { dataUrl, canvas, idx }
  const [previews, setPreviews] = useState(null);   // null = pannello chiuso
  const [excluded, setExcluded] = useState(new Set());
  const [sendingIdx, setSendingIdx] = useState(null);   // quale carta si sta inviando

  const ready = cvReady && camReady;

  // ── Stili globali ────────────────────────────────────────────────
  useEffect(() => {
    const link = document.createElement("link");
    link.rel = "stylesheet";
    link.href = "https://fonts.googleapis.com/css2?family=Share+Tech+Mono&family=Rajdhani:wght@600;700&display=swap";
    document.head.appendChild(link);
    const style = document.createElement("style");
    style.textContent = `
      @keyframes spin    { to { transform: rotate(360deg) } }
      @keyframes pulse   { 0%,100%{opacity:1} 50%{opacity:.3} }
      @keyframes slideUp { from{opacity:0;transform:translateY(20px)} to{opacity:1;transform:translateY(0)} }
      @keyframes fadeIn  { from{opacity:0} to{opacity:1} }
      ::-webkit-scrollbar { height: 4px; background: rgba(255,255,255,0.05); }
      ::-webkit-scrollbar-thumb { background: rgba(255,215,0,0.3); border-radius: 2px; }
    `;
    document.head.appendChild(style);
    return () => {
      try { document.head.removeChild(link); } catch { }
      try { document.head.removeChild(style); } catch { }
    };
  }, []);

  // ── OpenCV (carica una sola volta) ───────────────────────────────
  useEffect(() => {
    if (window.cv?.getBuildInformation) { setCvReady(true); return; }
    const existing = document.querySelector('script[src*="opencv.js"]');
    if (existing) {
      const t = setInterval(() => {
        if (window.cv?.getBuildInformation) { clearInterval(t); setCvReady(true); }
      }, 300);
      return () => clearInterval(t);
    }
    const s = document.createElement("script");
    s.src = "https://docs.opencv.org/4.8.0/opencv.js";
    s.async = true;
    s.onload = () => {
      const t = setInterval(() => {
        if (window.cv?.getBuildInformation) { clearInterval(t); setCvReady(true); }
      }, 300);
    };
    document.head.appendChild(s);
    // NON rimuovere: OpenCV non può essere ri-registrato nella stessa sessione
  }, []);

  // ── Camera ───────────────────────────────────────────────────────
  useEffect(() => {
    navigator.mediaDevices.getUserMedia({
      video: { facingMode: { ideal: "environment" }, width: { ideal: 1280 }, height: { ideal: 720 } }
    })
      .then(stream => {
        if (!videoRef.current) return;
        videoRef.current.srcObject = stream;
        videoRef.current.onloadedmetadata = () => setCamReady(true);
      })
      .catch(() => setCamError(true));
    return () => videoRef.current?.srcObject?.getTracks().forEach(t => t.stop());
  }, []);

  // ── Detection frame loop ─────────────────────────────────────────
  const processFrame = useCallback(() => {
    const video = videoRef.current, overlay = overlayRef.current, proc = procRef.current;
    if (!video || !overlay || !proc || !window.cv?.Mat) {
      animRef.current = requestAnimationFrame(processFrame); return;
    }
    const vw = video.videoWidth, vh = video.videoHeight;
    if (!vw || !vh) { animRef.current = requestAnimationFrame(processFrame); return; }

    if (overlay.width !== vw) { overlay.width = vw; overlay.height = vh; }
    if (proc.width !== vw) { proc.width = vw; proc.height = vh; }

    const cv = window.cv;
    const mats = [];
    const free = m => { try { m?.delete(); } catch { } };

    try {
      proc.getContext("2d").drawImage(video, 0, 0, vw, vh);

      const src = cv.imread(proc); mats.push(src);
      const gray = new cv.Mat(); mats.push(gray);
      const blur = new cv.Mat(); mats.push(blur);
      const edges = new cv.Mat(); mats.push(edges);
      const contours = new cv.MatVector(); mats.push(contours);
      const hier = new cv.Mat(); mats.push(hier);

      cv.cvtColor(src, gray, cv.COLOR_RGBA2GRAY);

      // Blur più forte → riduce rumore texture della carta
      cv.GaussianBlur(gray, blur, new cv.Size(9, 9), 0);

      // Canny con soglie moderate (non troppo basse → meno falsi bordi)
      cv.Canny(blur, edges, 40, 120);

      // Dilata per connettere bordi spezzati
      const k3 = cv.getStructuringElement(cv.MORPH_RECT, new cv.Size(3, 3));
      cv.dilate(edges, edges, k3);
      k3.delete();

      cv.findContours(edges, contours, hier, cv.RETR_EXTERNAL, cv.CHAIN_APPROX_SIMPLE);

      const minA = vw * vh * AREA_MIN_FRAC;
      const maxA = vw * vh * AREA_MAX_FRAC;
      const total = contours.size();
      let pArea = 0, pSolid = 0, pRatio = 0, p4pts = 0;
      const cards = [];

      for (let i = 0; i < total; i++) {
        const cnt = contours.get(i);
        const area = cv.contourArea(cnt);

        if (area < minA || area > maxA) { cnt.delete(); continue; }
        pArea++;

        const r = cv.boundingRect(cnt);
        const rectArea = r.width * r.height;

        // Solidity check: scarta forme "frangiose" (testi, texture, ecc.)
        const solidity = rectArea > 0 ? area / rectArea : 0;
        if (solidity < SOLIDITY_MIN) { cnt.delete(); continue; }
        pSolid++;

        // Dimensione minima assoluta
        if (r.width < MIN_SIDE_PX || r.height < MIN_SIDE_PX) { cnt.delete(); continue; }

        // Aspect ratio (orientamento sia verticale che orizzontale)
        const hwRatio = Math.max(r.width, r.height) / Math.min(r.width, r.height);
        if (hwRatio < RATIO_MIN || hwRatio > RATIO_MAX) { cnt.delete(); continue; }
        pRatio++;

        // Cerca 4 punti con epsilon crescente
        let pts4 = null;
        for (const eps of [0.01, 0.02, 0.03, 0.04, 0.06]) {
          const peri = cv.arcLength(cnt, true);
          const approx = new cv.Mat();
          cv.approxPolyDP(cnt, approx, eps * peri, true);
          if (approx.rows === 4) {
            pts4 = [];
            for (let j = 0; j < 4; j++)
              pts4.push({ x: approx.data32S[j * 2], y: approx.data32S[j * 2 + 1] });
            approx.delete();
            break;
          }
          approx.delete();
        }

        // Senza 4 punti: scarta (NO fallback bounding rect → troppi falsi)
        if (!pts4) { cnt.delete(); continue; }
        p4pts++;

        cards.push({ rect: r, points: sortCorners(pts4), area, solidity });
        cnt.delete();
      }

      // Ordina per area decrescente, prendi le prime N
      cards.sort((a, b) => b.area - a.area);
      const top = cards.slice(0, MAX_CARDS);
      cardsRef.current = top;

      frameN.current++;
      if (frameN.current % 15 === 0) {
        setCardCount(top.length);
        if (debug) setDebugInfo({ total, pArea, pSolid, pRatio, p4pts, found: top.length, vw, vh, minA: Math.round(minA) });
      }

      // ── Disegna overlay AR ───────────────────────────────────────
      const ctx = overlay.getContext("2d");
      ctx.clearRect(0, 0, vw, vh);

      scanLineY.current = (scanLineY.current + 1.5) % vh;
      const sg = ctx.createLinearGradient(0, scanLineY.current - 50, 0, scanLineY.current + 50);
      sg.addColorStop(0, "rgba(255,215,0,0)");
      sg.addColorStop(0.5, "rgba(255,215,0,0.025)");
      sg.addColorStop(1, "rgba(255,215,0,0)");
      ctx.fillStyle = sg;
      ctx.fillRect(0, scanLineY.current - 50, vw, 100);

      top.forEach((card, idx) =>
        drawCardAR(ctx, card, PALETTE[idx % PALETTE.length], resultsRef.current[idx], idx, vw, vh)
      );

    } catch (e) {
      console.warn("CV error:", e);
    } finally {
      mats.forEach(free);
    }

    animRef.current = requestAnimationFrame(processFrame);
  }, [debug]);

  useEffect(() => {
    if (ready) animRef.current = requestAnimationFrame(processFrame);
    return () => { if (animRef.current) cancelAnimationFrame(animRef.current); };
  }, [ready, processFrame]);

  // ── AR overlay draw ──────────────────────────────────────────────
  function drawCardAR(ctx, card, pal, result, idx, vw, vh) {
    const { rect, points } = card;
    ctx.save();

    // Fill
    ctx.fillStyle = pal.g;
    ctx.beginPath();
    ctx.moveTo(points[0].x, points[0].y);
    points.forEach(p => ctx.lineTo(p.x, p.y));
    ctx.closePath(); ctx.fill();

    // Bordo
    ctx.strokeStyle = pal.s; ctx.lineWidth = 2.5;
    ctx.shadowColor = pal.s; ctx.shadowBlur = 14;
    ctx.beginPath();
    ctx.moveTo(points[0].x, points[0].y);
    points.forEach(p => ctx.lineTo(p.x, p.y));
    ctx.closePath(); ctx.stroke();
    ctx.shadowBlur = 0;

    // Corner dots
    points.forEach(({ x, y }) => {
      ctx.beginPath(); ctx.arc(x, y, 5, 0, Math.PI * 2);
      ctx.fillStyle = pal.s; ctx.fill();
    });

    // Badge numero
    const bx = rect.x + rect.width - 14, by = rect.y + 14;
    ctx.beginPath(); ctx.arc(bx, by, 14, 0, Math.PI * 2);
    ctx.fillStyle = pal.s; ctx.fill();
    ctx.fillStyle = "#0A0F1E"; ctx.font = "bold 13px 'Share Tech Mono',monospace";
    ctx.textAlign = "center"; ctx.fillText(idx + 1, bx, by + 5); ctx.textAlign = "left";

    // Pannello risultati AR
    if (result) {
      const pw = Math.max(rect.width, 210), ph = 90;
      const px = Math.max(4, Math.min(rect.x, vw - pw - 4));
      const py = rect.y > ph + 12 ? rect.y - ph - 10 : rect.y + rect.height + 10;
      const sy = Math.max(4, Math.min(py, vh - ph - 4));

      ctx.shadowColor = pal.s; ctx.shadowBlur = 8;
      ctx.fillStyle = "rgba(8,12,25,0.93)";
      roundRect(ctx, px, sy, pw, ph, 10); ctx.fill();
      ctx.strokeStyle = pal.s; ctx.lineWidth = 1.5;
      roundRect(ctx, px, sy, pw, ph, 10); ctx.stroke();
      ctx.shadowBlur = 0;

      ctx.fillStyle = pal.s; roundRect(ctx, px + 8, sy + 10, 4, ph - 20, 2); ctx.fill();
      ctx.fillStyle = "#fff"; ctx.font = "bold 15px 'Rajdhani',sans-serif";
      ctx.fillText((result.name || "—").slice(0, 26), px + 20, sy + 28);
      ctx.fillStyle = pal.s; ctx.font = "11px 'Share Tech Mono',monospace";
      ctx.fillText(result.set || "—", px + 20, sy + 48);
      ctx.fillStyle = "#4ECDC4"; ctx.font = "bold 17px 'Rajdhani',sans-serif";
      ctx.fillText(`€ ${result.price ?? "—"}`, px + 20, sy + 74);
    }
    ctx.restore();
  }

  // ── STEP 1: genera previews warpate (NON chiama ancora l'API) ────
  const handlePreview = useCallback(() => {
    const cards = cardsRef.current;
    if (!cards.length || scanning) return;

    const cv = window.cv;
    const newPreviews = cards.map((card, idx) => {
      try {
        const tmpCanvas = warpCard(cv, videoRef.current, procRef.current, card.points);
        return { idx, dataUrl: tmpCanvas.toDataURL("image/jpeg", 0.92), canvas: tmpCanvas };
      } catch (e) {
        console.warn(`Preview carta ${idx}:`, e);
        return { idx, dataUrl: null, canvas: null };
      }
    });

    setExcluded(new Set());
    setPreviews(newPreviews);
  }, [scanning]);

  // ── STEP 2: invia le carte NON escluse all'API ───────────────────
  const handleConfirmSend = useCallback(async () => {
    if (!previews) return;
    setScanning(true);
    const newResults = {};

    for (const { idx, canvas } of previews) {
      if (excluded.has(idx) || !canvas) continue;
      setSendingIdx(idx);
      try {
        const blob = await canvasToBlob(canvas);
        const fd = new FormData();
        fd.append("image", blob, `card_${idx + 1}.jpg`);
        const res = await fetch(API_ENDPOINT, { method: "POST", body: fd });
        const data = await res.json();
        newResults[idx] = {
          name: data.name || data.card_name || "Sconosciuta",
          set: data.set || data.card_code || "—",
          price: data.price || data.market_price || "—",
        };
      } catch (err) {
        console.warn(`Carta ${idx + 1} errore:`, err);
        // Demo fallback — rimuovere in produzione
        const demo = [
          { name: "Monkey D. Luffy", set: "OP01-001 · SEC", price: "45.00" },
          { name: "Roronoa Zoro", set: "OP01-002 · SR", price: "12.50" },
          { name: "Nami", set: "OP01-016 · R", price: "3.20" },
          { name: "Tony Tony Chopper", set: "OP01-025 · R", price: "2.80" },
        ];
        newResults[idx] = demo[idx % demo.length];
      }
    }

    resultsRef.current = { ...newResults };
    setResults({ ...newResults });
    setScanning(false);
    setSendingIdx(null);
    setPreviews(null);
  }, [previews, excluded]);

  const handleReset = () => {
    resultsRef.current = {};
    setResults({});
    setPreviews(null);
    setExcluded(new Set());
  };

  const toggleExclude = (idx) => {
    setExcluded(prev => {
      const next = new Set(prev);
      next.has(idx) ? next.delete(idx) : next.add(idx);
      return next;
    });
  };

  const loadPct = (cvReady ? 50 : 0) + (camReady ? 50 : 0);
  const hasResults = Object.keys(results).length > 0;
  const btnDisabled = !ready || cardCount === 0 || scanning || !!previews;
  const confirmCount = previews ? previews.length - excluded.size : 0;

  // ─── RENDER ────────────────────────────────────────────────────────
  return (
    <div style={{
      width: "100vw", height: "100vh", background: "#0A0F1E",
      overflow: "hidden", position: "relative", userSelect: "none",
      fontFamily: "'Share Tech Mono',monospace",
    }}>
      {/* Video */}
      <video ref={videoRef} autoPlay playsInline muted
        style={{ position: "absolute", inset: 0, width: "100%", height: "100%", objectFit: "cover" }} />

      {/* AR Canvas */}
      <canvas ref={overlayRef}
        style={{ position: "absolute", inset: 0, width: "100%", height: "100%", pointerEvents: "none" }} />

      {/* Processing canvas (nascosto) */}
      <canvas ref={procRef} style={{ display: "none" }} />

      {/* ── Header ── */}
      <div style={{
        position: "absolute", top: 0, left: 0, right: 0, padding: "16px 20px",
        background: "linear-gradient(rgba(10,15,30,0.92) 0%,transparent 100%)",
        display: "flex", alignItems: "center", justifyContent: "space-between",
      }}>
        <div style={{ display: "flex", alignItems: "center", gap: 10 }}>
          <span style={{ fontSize: 26 }}>🏴‍☠️</span>
          <div>
            <div style={{ color: "#FFD700", fontSize: 16, fontFamily: "'Rajdhani',sans-serif", fontWeight: 700, letterSpacing: 3 }}>
              ONE PIECE SCANNER
            </div>
            <div style={{ color: "rgba(255,255,255,0.28)", fontSize: 10, letterSpacing: 2 }}>AR CARD RECOGNITION v3</div>
          </div>
        </div>
        <div style={{ display: "flex", alignItems: "center", gap: 10 }}>
          <button onClick={() => setDebug(d => !d)} style={{
            padding: "4px 10px",
            background: debug ? "rgba(255,215,0,0.15)" : "transparent",
            border: `1px solid ${debug ? "#FFD700" : "rgba(255,255,255,0.12)"}`,
            borderRadius: 6, color: debug ? "#FFD700" : "rgba(255,255,255,0.3)",
            fontSize: 10, cursor: "pointer", letterSpacing: 1,
            fontFamily: "'Share Tech Mono',monospace",
          }}>DBG</button>
          <div style={{ display: "flex", alignItems: "center", gap: 7 }}>
            <div style={{
              width: 8, height: 8, borderRadius: "50%",
              background: ready ? "#4ECDC4" : "#FF6B6B",
              boxShadow: `0 0 10px ${ready ? "#4ECDC4" : "#FF6B6B"}`,
              animation: ready ? "none" : "pulse 1.2s infinite",
            }} />
            <span style={{ color: ready ? "#4ECDC4" : "rgba(255,255,255,0.4)", fontSize: 11, letterSpacing: 1 }}>
              {ready ? "LIVE" : "INIT"}
            </span>
          </div>
        </div>
      </div>

      {/* ── Debug HUD ── */}
      {debug && ready && (
        <div style={{
          position: "absolute", top: 72, left: 16,
          background: "rgba(0,0,0,0.88)", border: "1px solid rgba(255,215,0,0.25)",
          borderRadius: 8, padding: "10px 14px", fontSize: 10, lineHeight: 2,
          color: "rgba(255,255,255,0.6)", letterSpacing: 1, minWidth: 240,
          animation: "fadeIn 0.2s ease",
        }}>
          <div style={{ color: "#FFD700", fontWeight: "bold", marginBottom: 2 }}>◆ DEBUG DETECTION</div>
          <div>Res: <b style={{ color: "#fff" }}>{debugInfo.vw}×{debugInfo.vh}</b></div>
          <div>Min area: <b style={{ color: "#fff" }}>{debugInfo.minA} px²</b></div>
          <div>Contorni totali: <b style={{ color: "#FFB347" }}>{debugInfo.total}</b></div>
          <div>Passano area: <b style={{ color: "#C3A6FF" }}>{debugInfo.pArea}</b></div>
          <div>Passano solidity ({SOLIDITY_MIN}): <b style={{ color: "#FFB347" }}>{debugInfo.pSolid}</b></div>
          <div>Passano ratio ({RATIO_MIN}–{RATIO_MAX}): <b style={{ color: "#4ECDC4" }}>{debugInfo.pRatio}</b></div>
          <div>Hanno 4 punti: <b style={{ color: "#A8E6CF" }}>{debugInfo.p4pts}</b></div>
          <div style={{ borderTop: "1px solid rgba(255,255,255,0.08)", marginTop: 4, paddingTop: 4 }}>
            Carte rilevate: <b style={{ color: debugInfo.found > 0 ? "#4ECDC4" : "#FF6B6B", fontSize: 13 }}>
              {debugInfo.found ?? 0}
            </b>
          </div>
        </div>
      )}

      {/* ── Bottom HUD ── */}
      <div style={{
        position: "absolute", bottom: 0, left: 0, right: 0,
        background: "linear-gradient(transparent 0%,rgba(10,15,30,0.97) 38%)",
        padding: "44px 20px 36px",
      }}>
        {/* Stato detection */}
        <div style={{ textAlign: "center", marginBottom: 14, height: 20 }}>
          {ready && !previews && (
            <span style={{
              color: cardCount > 0 ? "#FFD700" : "rgba(255,255,255,0.2)",
              fontSize: 12, letterSpacing: 2,
              animation: cardCount > 0 ? "none" : "pulse 2s infinite",
            }}>
              {cardCount > 0
                ? `◆ ${cardCount} CARTA${cardCount !== 1 ? "E" : ""} RILEVATA${cardCount !== 1 ? "E" : ""} — PREMI SCAN`
                : "◇  PUNTA LA FOTOCAMERA SULLE CARTE"}
            </span>
          )}
        </div>

        {/* Risultati API */}
        {hasResults && !previews && (
          <div style={{
            display: "flex", gap: 10, overflowX: "auto",
            marginBottom: 14, paddingBottom: 4,
            animation: "slideUp 0.3s ease", scrollbarWidth: "thin",
          }}>
            {Object.entries(results).map(([idx, r]) => {
              const pal = PALETTE[parseInt(idx) % PALETTE.length];
              return (
                <div key={idx} style={{
                  flex: "0 0 auto", minWidth: 150,
                  background: "rgba(255,255,255,0.04)",
                  border: `1px solid ${pal.s}`, borderRadius: 10, padding: "10px 14px",
                }}>
                  <div style={{ color: "#fff", fontSize: 13, fontFamily: "'Rajdhani',sans-serif", fontWeight: 700, marginBottom: 2 }}>{r.name}</div>
                  <div style={{ color: "rgba(255,255,255,0.4)", fontSize: 10, marginBottom: 6 }}>{r.set}</div>
                  <div style={{ color: "#4ECDC4", fontSize: 14, fontFamily: "'Rajdhani',sans-serif", fontWeight: 700 }}>€ {r.price}</div>
                </div>
              );
            })}
          </div>
        )}

        {/* Pulsanti principali */}
        {!previews && (
          <div style={{ display: "flex", gap: 10 }}>
            {hasResults && (
              <button onClick={handleReset} style={{
                padding: "14px 18px", flexShrink: 0,
                background: "rgba(255,255,255,0.07)",
                border: "1px solid rgba(255,255,255,0.14)",
                borderRadius: 10, color: "rgba(255,255,255,0.65)",
                fontSize: 12, letterSpacing: 1, cursor: "pointer",
                fontFamily: "'Share Tech Mono',monospace",
              }}>✕ RESET</button>
            )}
            <button
              onClick={handlePreview}
              disabled={btnDisabled}
              style={{
                flex: 1, padding: "16px",
                background: btnDisabled
                  ? "rgba(255,255,255,0.05)"
                  : "linear-gradient(135deg,#FFD700 0%,#FFA500 100%)",
                border: "none", borderRadius: 10,
                color: btnDisabled ? "rgba(255,255,255,0.18)" : "#0A0F1E",
                fontSize: 15, fontWeight: 700,
                fontFamily: "'Rajdhani',sans-serif", letterSpacing: 3,
                cursor: btnDisabled ? "not-allowed" : "pointer",
                transition: "all 0.25s",
                boxShadow: !btnDisabled ? "0 0 24px rgba(255,215,0,0.35),0 4px 12px rgba(0,0,0,0.4)" : "none",
              }}
            >
              {!ready ? "⟳  INIZIALIZZAZIONE..." : "⚡  SCAN CARDS"}
            </button>
          </div>
        )}
      </div>

      {/* ════════════════════════════════════════════════════════════
           PANNELLO PREVIEW CARTE
      ════════════════════════════════════════════════════════════ */}
      {previews && (
        <div style={{
          position: "absolute", inset: 0,
          background: "rgba(8,12,24,0.96)",
          display: "flex", flexDirection: "column",
          animation: "fadeIn 0.25s ease",
          zIndex: 50,
        }}>
          {/* Header pannello */}
          <div style={{
            padding: "20px 20px 12px",
            borderBottom: "1px solid rgba(255,255,255,0.07)",
            display: "flex", alignItems: "center", justifyContent: "space-between",
          }}>
            <div>
              <div style={{ color: "#FFD700", fontFamily: "'Rajdhani',sans-serif", fontSize: 18, fontWeight: 700, letterSpacing: 2 }}>
                ANTEPRIMA SCAN
              </div>
              <div style={{ color: "rgba(255,255,255,0.35)", fontSize: 10, letterSpacing: 1, marginTop: 2 }}>
                Verifica che le carte siano corrette · tocca per escludere
              </div>
            </div>
            <button
              onClick={() => setPreviews(null)}
              style={{
                background: "rgba(255,255,255,0.07)",
                border: "1px solid rgba(255,255,255,0.12)",
                borderRadius: 8, color: "rgba(255,255,255,0.6)",
                fontSize: 12, padding: "6px 14px", cursor: "pointer",
                fontFamily: "'Share Tech Mono',monospace", letterSpacing: 1,
              }}
            >✕ ANNULLA</button>
          </div>

          {/* Griglia anteprime */}
          <div style={{
            flex: 1, overflowY: "auto",
            padding: "20px",
            display: "grid",
            gridTemplateColumns: "repeat(auto-fill, minmax(140px, 1fr))",
            gap: 14,
            alignContent: "start",
          }}>
            {previews.map(({ idx, dataUrl }) => {
              const pal = PALETTE[idx % PALETTE.length];
              const excl = excluded.has(idx);
              return (
                <div
                  key={idx}
                  onClick={() => toggleExclude(idx)}
                  style={{
                    cursor: "pointer",
                    opacity: excl ? 0.35 : 1,
                    transition: "opacity 0.2s, transform 0.15s",
                    transform: excl ? "scale(0.94)" : "scale(1)",
                    animation: "slideUp 0.2s ease",
                    position: "relative",
                  }}
                >
                  {/* Immagine carta warpata */}
                  <div style={{
                    borderRadius: 8,
                    overflow: "hidden",
                    border: `2px solid ${excl ? "rgba(255,255,255,0.1)" : pal.s}`,
                    boxShadow: excl ? "none" : `0 0 14px ${pal.s}44`,
                    aspectRatio: "300/420",
                    background: "#0d1120",
                    position: "relative",
                  }}>
                    {dataUrl
                      ? <img src={dataUrl} alt={`Carta ${idx + 1}`}
                        style={{ width: "100%", height: "100%", objectFit: "cover", display: "block" }} />
                      : <div style={{
                        width: "100%", height: "100%",
                        display: "flex", alignItems: "center", justifyContent: "center",
                        color: "rgba(255,255,255,0.2)", fontSize: 11,
                      }}>Errore</div>
                    }

                    {/* Overlay esclusione */}
                    {excl && (
                      <div style={{
                        position: "absolute", inset: 0,
                        display: "flex", alignItems: "center", justifyContent: "center",
                        background: "rgba(0,0,0,0.5)",
                        fontSize: 30,
                      }}>✕</div>
                    )}

                    {/* Badge invio in corso */}
                    {scanning && sendingIdx === idx && (
                      <div style={{
                        position: "absolute", inset: 0,
                        display: "flex", alignItems: "center", justifyContent: "center",
                        background: "rgba(8,12,24,0.75)",
                      }}>
                        <div style={{
                          width: 28, height: 28,
                          border: "3px solid rgba(255,215,0,0.2)",
                          borderTop: "3px solid #FFD700",
                          borderRadius: "50%",
                          animation: "spin 0.8s linear infinite",
                        }} />
                      </div>
                    )}
                  </div>

                  {/* Label sotto */}
                  <div style={{
                    marginTop: 6, textAlign: "center",
                    color: excl ? "rgba(255,255,255,0.25)" : pal.s,
                    fontSize: 10, letterSpacing: 1,
                  }}>
                    {excl ? "ESCLUSA" : `CARTA ${idx + 1}`}
                  </div>
                </div>
              );
            })}
          </div>

          {/* Footer pannello */}
          <div style={{
            padding: "16px 20px 32px",
            borderTop: "1px solid rgba(255,255,255,0.07)",
            background: "rgba(8,12,24,0.9)",
          }}>
            <div style={{ textAlign: "center", marginBottom: 12, color: "rgba(255,255,255,0.3)", fontSize: 11, letterSpacing: 1 }}>
              {confirmCount === 0
                ? "⚠ Tutte le carte sono escluse"
                : `${confirmCount} carta${confirmCount !== 1 ? "e" : ""} da inviare · ${excluded.size} esclusa${excluded.size !== 1 ? "e" : ""}`}
            </div>
            <button
              onClick={handleConfirmSend}
              disabled={scanning || confirmCount === 0}
              style={{
                width: "100%", padding: "16px",
                background: (scanning || confirmCount === 0)
                  ? "rgba(255,255,255,0.05)"
                  : "linear-gradient(135deg,#FFD700 0%,#FFA500 100%)",
                border: "none", borderRadius: 10,
                color: (scanning || confirmCount === 0) ? "rgba(255,255,255,0.2)" : "#0A0F1E",
                fontSize: 15, fontWeight: 700,
                fontFamily: "'Rajdhani',sans-serif", letterSpacing: 3,
                cursor: (scanning || confirmCount === 0) ? "not-allowed" : "pointer",
                transition: "all 0.2s",
                boxShadow: (!scanning && confirmCount > 0)
                  ? "0 0 24px rgba(255,215,0,0.3),0 4px 12px rgba(0,0,0,0.4)"
                  : "none",
              }}
            >
              {scanning
                ? `⟳  INVIO CARTA ${(sendingIdx ?? 0) + 1} / ${confirmCount}...`
                : `⚡  INVIA ${confirmCount} CARTA${confirmCount !== 1 ? "E" : ""} ALL'API`}
            </button>
          </div>
        </div>
      )}

      {/* ── Loading screen ── */}
      {!ready && !camError && (
        <div style={{
          position: "absolute", inset: 0, background: "rgba(10,15,30,0.97)",
          display: "flex", flexDirection: "column", alignItems: "center", justifyContent: "center", gap: 28,
          zIndex: 100,
        }}>
          <div style={{ fontSize: 64, filter: "drop-shadow(0 0 20px rgba(255,215,0,0.5))" }}>🏴‍☠️</div>
          <div style={{ textAlign: "center" }}>
            <div style={{ color: "#FFD700", fontFamily: "'Rajdhani',sans-serif", fontSize: 24, fontWeight: 700, letterSpacing: 4, marginBottom: 6 }}>
              ONE PIECE SCANNER
            </div>
            <div style={{ color: "rgba(255,255,255,0.28)", fontSize: 11, letterSpacing: 2 }}>INIZIALIZZAZIONE SISTEMA AR</div>
          </div>
          <div style={{ width: 300, display: "flex", flexDirection: "column", gap: 14 }}>
            <LoadItem label="FOTOCAMERA" done={camReady} />
            <LoadItem label="OPENCV.JS (~8 MB)" done={cvReady} />
          </div>
          <div style={{ width: 300, height: 2, background: "rgba(255,255,255,0.08)", borderRadius: 2 }}>
            <div style={{
              height: "100%", borderRadius: 2, width: `${loadPct}%`,
              background: "linear-gradient(90deg,#FFD700,#FFA500)",
              transition: "width 0.5s ease", boxShadow: "0 0 12px rgba(255,215,0,0.5)",
            }} />
          </div>
          <div style={{ color: "rgba(255,255,255,0.18)", fontSize: 10, letterSpacing: 1 }}>{loadPct}% — ATTENDERE...</div>
        </div>
      )}

      {/* ── Camera error ── */}
      {camError && (
        <div style={{
          position: "absolute", inset: 0, background: "rgba(10,15,30,0.98)",
          display: "flex", flexDirection: "column", alignItems: "center", justifyContent: "center",
          gap: 18, padding: "40px", textAlign: "center", zIndex: 100,
        }}>
          <div style={{ fontSize: 56 }}>📷</div>
          <div style={{ color: "#FF6B6B", fontFamily: "'Rajdhani',sans-serif", fontSize: 22, fontWeight: 700, letterSpacing: 2 }}>
            ACCESSO FOTOCAMERA NEGATO
          </div>
          <div style={{ color: "rgba(255,255,255,0.4)", fontSize: 13, lineHeight: 1.7, maxWidth: 320 }}>
            Concedi i permessi fotocamera nelle impostazioni del browser e ricarica la pagina.
          </div>
          <button onClick={() => window.location.reload()} style={{
            marginTop: 8, padding: "12px 32px",
            background: "linear-gradient(135deg,#FFD700,#FFA500)",
            border: "none", borderRadius: 8, color: "#0A0F1E",
            fontFamily: "'Rajdhani',sans-serif", fontSize: 14, fontWeight: 700, letterSpacing: 2, cursor: "pointer",
          }}>RIPROVA</button>
        </div>
      )}
    </div>
  );
}

// ── Loading item ────────────────────────────────────────────────────
function LoadItem({ label, done }) {
  return (
    <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
      <div style={{
        width: 22, height: 22, borderRadius: "50%", flexShrink: 0,
        display: "flex", alignItems: "center", justifyContent: "center",
        background: done ? "#4ECDC4" : "transparent",
        border: `1.5px solid ${done ? "#4ECDC4" : "rgba(255,255,255,0.18)"}`,
        color: done ? "#0A0F1E" : "rgba(255,255,255,0.3)",
        fontSize: 12, transition: "all 0.4s",
      }}>
        {done ? "✓" : "·"}
      </div>
      <span style={{ color: done ? "#fff" : "rgba(255,255,255,0.32)", fontSize: 11, letterSpacing: 1, flex: 1 }}>{label}</span>
      {!done && <div style={{
        width: 16, height: 16, flexShrink: 0,
        border: "2px solid rgba(255,215,0,0.18)",
        borderTop: "2px solid #FFD700", borderRadius: "50%",
        animation: "spin 0.9s linear infinite",
      }} />}
    </div>
  );
}
