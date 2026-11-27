// png-squeeze-01 entry v4 — lossless PNG re-encoder.
// v4 changes over v3: 5-beam Viterbi filter selection (level-6 scoring) on
// RGBA images where a non-zero filter won screening (measured i003 -2,186
// bytes under the optimal encoder; on RGB the beam gains only ~-550 bytes
// for +3.5 s, and on grey it LOSES bytes, so the beam runs only when
// bpp >= 4 and the greedy runs otherwise), and cost-based block splitting as
// an extra candidate alongside the equal splits (measured i002 -249, i003
// -755, i006 -1,568 bytes). Chain 2048 deliberately NOT taken (+9.8 pts for
// +7.1 s would push the runtime too close to the 60 s wall).
// Pure Node built-ins only. Deterministic: output is a pure function of the input bytes
// (no clock, no randomness, no environment reads beyond MAKEFUN_INPUT_DIR/OUTPUT_DIR).
// Strategy: colour-type reduction (palette / grey / RGB / RGBA), per-scanline filter
// choice screened by zlib-9 (fixed filters only), then — when a non-zero filter won
// screening — a greedy per-row filter selection scored by real DEFLATE cost
// (each candidate row compressed with the chosen history as the dictionary), then the
// winning filtered stream is re-encoded with an optimal-parse DEFLATE encoder
// (hash-chain LZ77 + shortest-path DP + optimal length-limited Huffman + block
// splitting), written from the DEFLATE spec (RFC 1951). Settings are tiered by
// filtered-stream size and by the winning stream's zlib-9 size so the 60 s wall is
// never at risk.
// png-squeeze-01 entry v1 — lossless PNG re-encoder.
// Pure Node built-ins only. Deterministic: output is a pure function of the input bytes
// (no clock, no randomness, no environment reads beyond MAKEFUN_INPUT_DIR/OUTPUT_DIR).
// Strategy: colour-type reduction (palette / grey / RGB / RGBA), per-scanline filter
// choice by minimum-sum-of-absolute-differences and by minimum-entropy, plus a fixed
// Paeth pass; each candidate compressed with zlib level 9 (memLevel 9), smallest wins.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { constants as zlibConstants, deflateSync, deflateRawSync, inflateSync } from 'node:zlib';
import { pathToFileURL } from 'node:url';

// ---------- CRC32 ----------
const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c >>> 0;
  }
  return t;
})();
export function crc32(buf) {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 255] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
export function chunk(type, data) {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, 'ascii');
  Buffer.from(data).copy(out, 8);
  out.writeUInt32BE(crc32(out.subarray(4, 8 + data.length)), 8 + data.length);
  return out;
}

// ---------- PNG decode (input: stored RGBA PNG; generic unfilter for safety) ----------
export function paeth(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  if (pb <= pc) return b;
  return c;
}
export function unfilterRow(f, cur, prev, bpp) {
  const n = cur.length;
  for (let i = 0; i < n; i++) {
    const left = i >= bpp ? cur[i - bpp] : 0;
    const up = prev ? prev[i] : 0;
    const upLeft = i >= bpp && prev ? prev[i - bpp] : 0;
    let pred;
    if (f === 0) pred = 0;
    else if (f === 1) pred = left;
    else if (f === 2) pred = up;
    else if (f === 3) pred = (left + up) >> 1;
    else pred = paeth(left, up, upLeft);
    cur[i] = (cur[i] + pred) & 255;
  }
}
export function decodePng(buf) {
  if (buf.length < 8 || buf.readUInt32BE(0) !== 0x89504e47 || buf.readUInt32BE(4) !== 0x0d0a1a0a) {
    throw new Error('not a PNG');
  }
  let off = 8;
  let width = 0;
  let height = 0;
  let bitDepth = 0;
  let colorType = 0;
  const idat = [];
  while (off + 8 <= buf.length) {
    const len = buf.readUInt32BE(off);
    const type = buf.toString('ascii', off + 4, off + 8);
    const data = buf.subarray(off + 8, off + 8 + len);
    if (type === 'IHDR') {
      width = data.readUInt32BE(0);
      height = data.readUInt32BE(4);
      bitDepth = data[8];
      colorType = data[9];
      if (bitDepth !== 8 || colorType !== 6 || data[12] !== 0) throw new Error('unsupported input PNG');
    } else if (type === 'IDAT') {
      idat.push(data);
    } else if (type === 'IEND') {
      break;
    }
    off += 12 + len;
  }
  const raw = inflateSync(Buffer.concat(idat));
  const rowBytes = width * 4;
  const rgba = new Uint8Array(width * height * 4);
  let prev = null;
  for (let y = 0; y < height; y++) {
    const f = raw[y * (rowBytes + 1)];
    const row = raw.subarray(y * (rowBytes + 1) + 1, (y + 1) * (rowBytes + 1));
    const out = rgba.subarray(y * rowBytes, (y + 1) * rowBytes);
    out.set(row);
    unfilterRow(f, out, prev, 4);
    prev = out;
  }
  return { width, height, rgba };
}

// ---------- PNG filters (encode side) ----------
export function filterRow(f, cur, prev, bpp, out) {
  const n = cur.length;
  if (f === 0) {
    out.set(cur);
    return;
  }
  for (let i = 0; i < n; i++) {
    const left = i >= bpp ? cur[i - bpp] : 0;
    const up = prev ? prev[i] : 0;
    const upLeft = i >= bpp && prev ? prev[i - bpp] : 0;
    let v;
    if (f === 1) v = cur[i] - left;
    else if (f === 2) v = cur[i] - up;
    else if (f === 3) v = cur[i] - ((left + up) >> 1);
    else v = cur[i] - paeth(left, up, upLeft);
    out[i] = v & 255;
  }
}
const ENT_CNT = new Uint32Array(256);
export function msad(line, len) {
  let s = 0;
  for (let i = 0; i < len; i++) {
    const v = line[i];
    s += v > 127 ? 256 - v : v;
  }
  return s;
}
export function entropyBits(line, len) {
  ENT_CNT.fill(0);
  for (let i = 0; i < len; i++) ENT_CNT[line[i]]++;
  const logLen = Math.log2(len);
  let bits = 0;
  for (let v = 0; v < 256; v++) {
    const c = ENT_CNT[v];
    if (c) bits += c * (logLen - Math.log2(c));
  }
  return bits;
}

// Compress one representation's pixel bytes with 3 filter strategies, zlib-9, smallest wins.
// Build a filtered stream with one fixed filter for every row.
export function buildFilteredFixed(px, w, h, bpp, f) {
  const rowBytes = w * bpp;
  const stride = rowBytes + 1;
  const out = new Uint8Array(h * stride);
  const row = new Uint8Array(rowBytes);
  let prev = null;
  for (let y = 0; y < h; y++) {
    const cur = px.subarray(y * rowBytes, (y + 1) * rowBytes);
    filterRow(f, cur, prev, bpp, row);
    const base = y * stride;
    out[base] = f;
    out.set(row, base + 1);
    prev = cur;
  }
  return out;
}
// Build a filtered stream with a per-row filter chosen by pick(filt, rowBytes).
export function buildFilteredAdaptive(px, w, h, bpp, pick) {
  const rowBytes = w * bpp;
  const stride = rowBytes + 1;
  const out = new Uint8Array(h * stride);
  const filt = [];
  for (let f = 0; f < 5; f++) filt.push(new Uint8Array(rowBytes));
  let prev = null;
  for (let y = 0; y < h; y++) {
    const cur = px.subarray(y * rowBytes, (y + 1) * rowBytes);
    for (let f = 0; f < 5; f++) filterRow(f, cur, prev, bpp, filt[f]);
    const p = pick(filt, rowBytes);
    const base = y * stride;
    out[base] = p;
    out.set(filt[p], base + 1);
    prev = cur;
  }
  return out;
}
export function pickMsad(filt, rowBytes) {
  let best = 0;
  let bc = Infinity;
  for (let f = 0; f < 5; f++) {
    const c = msad(filt[f], rowBytes);
    if (c < bc) {
      bc = c;
      best = f;
    }
  }
  return best;
}
export function pickEntropy(filt, rowBytes) {
  let best = 0;
  let bc = Infinity;
  for (let f = 0; f < 5; f++) {
    const c = entropyBits(filt[f], rowBytes);
    if (c < bc) {
      bc = c;
      best = f;
    }
  }
  return best;
}
// Compress one representation's pixel bytes: try the fixed filters, zlib-9,
// smallest wins; then retry the winning filtered stream with alternate zlib
// strategies. The MSAD/entropy adaptive candidates are dropped in v3: the greedy
// DEFLATE-cost filter selection (greedyFilterDeflate) replaces them where a
// non-zero filter wins, and it beats both adaptives on every image where
// filtering helps. Returns { z, stream, winFilter } so the caller can re-encode
// the winning stream optimally and decide whether to run the DP.
export function compressRep(px, w, h, bpp) {
  const fixedList = bpp >= 3 ? [0, 2, 4] : [0, 1, 2, 3, 4];
  let bestZ = null;
  let bestPlain = null;
  let bestStream = null;
  let winFilter = 0;
  for (const f of fixedList) {
    const stream = buildFilteredFixed(px, w, h, bpp, f);
    const z = deflateSync(stream, { level: 9, memLevel: 9 });
    if (!bestZ || z.length < bestZ.length) {
      bestZ = z;
      bestPlain = z.length;
      bestStream = stream;
      winFilter = f;
    }
  }
  // Alternate zlib strategies on the winning filtered stream.
  for (const strategy of [zlibConstants.Z_FILTERED, zlibConstants.Z_RLE]) {
    const z = deflateSync(bestStream, { level: 9, memLevel: 9, strategy });
    if (z.length < bestZ.length) bestZ = z;
  }
  return { z: bestZ, stream: bestStream, winFilter, plainZ: bestPlain };
}

// Greedy per-row filter selection scored by real DEFLATE cost (v3).
// For each row and each of the 5 filters, compress the row's bytes with
// deflateRawSync (level 9) using the last 32K of the already-chosen filtered
// stream as the dictionary; the compressed size is the cost. The cheapest filter
// wins the row. This is a true DEFLATE-aware cost (real parse + real Huffman),
// unlike the MSAD/entropy heuristics it replaces — and unlike a history-only
// greedy LZ77 model, the dictionary lets each row match the chosen history.
// Deterministic: no clock, no randomness. Runs only on the winning
// representation, and only when a non-zero filter won screening (see encodeImage).
export function greedyFilterDeflate(px, w, h, bpp) {
  const rowBytes = w * bpp;
  const stride = rowBytes + 1;
  const hist = new Uint8Array(h * stride);
  const filt = [];
  for (let f = 0; f < 5; f++) filt.push(new Uint8Array(rowBytes));
  const rowData = [];
  for (let f = 0; f < 5; f++) rowData.push(new Uint8Array(stride));
  const choices = new Uint8Array(h);
  let histLen = 0;
  let prev = null;
  for (let y = 0; y < h; y++) {
    const cur = px.subarray(y * rowBytes, (y + 1) * rowBytes);
    for (let f = 0; f < 5; f++) filterRow(f, cur, prev, bpp, filt[f]);
    const dict = hist.subarray(Math.max(0, histLen - 32768), histLen);
    let bestF = 0, bestCost = Infinity;
    for (let f = 0; f < 5; f++) {
      const rd = rowData[f];
      rd[0] = f;
      rd.set(filt[f], 1);
      const c = deflateRawSync(rd, { level: 9, dictionary: dict }).length;
      if (c < bestCost) { bestCost = c; bestF = f; }
    }
    choices[y] = bestF;
    hist.set(rowData[bestF], histLen);
    histLen += stride;
    prev = cur;
  }
  return { stream: hist.subarray(0, histLen), choices };
}

// Beam (Viterbi) per-row filter selection, scored by real DEFLATE cost (v4).
// Keeps up to 5 histories alive, one per last filter chosen, so a row's choice
// does not poison the dictionary for later rows (the greedy's known weakness).
// Each row, every beam x every filter is scored by deflateRawSync with that
// beam's last-32K history as the dictionary; per last filter the cheapest beam
// survives. Scoring uses level 6, not 9: it ranks filters the same way (the
// beam-6 stream measured equal-or-better than beam-9 under the optimal encoder
// on i003, and ~2.5x faster), and the final stream is adopted by plain
// zlib-9 like-for-like, so a misrank can only lose part of the gain, never
// correctness. Runs only on RGBA images (bpp >= 4): measured gains are
// i003 -2,186 bytes under the optimal encoder, while on RGB (i006) it gains
// only ~-550 bytes for +3.5 s and on grey (i004) it LOSES bytes (level 6:
// -15). Deterministic: no clock, no randomness; ties break by filter order
// (stable sort, insertion order).
export function beamFilterDeflate(px, w, h, bpp) {
  const rowBytes = w * bpp;
  const stride = rowBytes + 1;
  const filt = [];
  for (let f = 0; f < 5; f++) filt.push(new Uint8Array(rowBytes));
  const rowData = [];
  for (let f = 0; f < 5; f++) rowData.push(new Uint8Array(stride));
  let beams = [{ cost: 0, dict: Buffer.alloc(0), choices: new Uint8Array(h) }];
  let prev = null;
  for (let y = 0; y < h; y++) {
    const cur = px.subarray(y * rowBytes, (y + 1) * rowBytes);
    for (let f = 0; f < 5; f++) filterRow(f, cur, prev, bpp, filt[f]);
    const cand = [];
    for (let b = 0; b < beams.length; b++) {
      const beam = beams[b];
      for (let f = 0; f < 5; f++) {
        const rd = rowData[f];
        rd[0] = f;
        rd.set(filt[f], 1);
        const c = deflateRawSync(rd, { level: 6, dictionary: beam.dict }).length;
        cand.push({ cost: beam.cost + c, b, f });
      }
    }
    const byF = new Map();
    for (const c of cand) {
      const ex = byF.get(c.f);
      if (!ex || c.cost < ex.cost) byF.set(c.f, c);
    }
    const surv = [...byF.values()].sort((a, b) => a.cost - b.cost).slice(0, 5);
    const next = [];
    for (const s of surv) {
      const beam = beams[s.b];
      const rd = rowData[s.f];
      const combined = Buffer.concat([beam.dict, rd]);
      const nd = combined.length > 32768 ? combined.subarray(combined.length - 32768) : combined;
      const choices = new Uint8Array(beam.choices);
      choices[y] = s.f;
      next.push({ cost: s.cost, dict: nd, choices });
    }
    beams = next;
    prev = cur;
  }
  let best = beams[0];
  for (const b of beams) if (b.cost < best.cost) best = b;
  const stream = new Uint8Array(h * stride);
  prev = null;
  for (let y = 0; y < h; y++) {
    const cur = px.subarray(y * rowBytes, (y + 1) * rowBytes);
    const f = best.choices[y];
    const row = new Uint8Array(rowBytes);
    filterRow(f, cur, prev, bpp, row);
    stream[y * stride] = f;
    stream.set(row, y * stride + 1);
    prev = cur;
  }
  return { stream, choices: best.choices };
}

// ---------- image analysis ----------
export function analyze(rgba) {
  const n = rgba.length / 4;
  const seen = new Map();
  const order = [];
  let allOpaque = true;
  let allGrey = true;
  for (let i = 0; i < n; i++) {
    const r = rgba[i * 4];
    const g = rgba[i * 4 + 1];
    const b = rgba[i * 4 + 2];
    const a = rgba[i * 4 + 3];
    if (a !== 255) allOpaque = false;
    if (r !== g || g !== b) allGrey = false;
    if (seen.size <= 256) {
      const key = r * 16777216 + g * 65536 + b * 256 + a;
      if (!seen.has(key)) {
        seen.set(key, order.length);
        order.push([r, g, b, a]);
      }
    }
  }
  return { unique: seen.size, allOpaque, allGrey, order };
}
export function buildGrey(rgba, opaque) {
  const n = rgba.length / 4;
  const bpp = opaque ? 1 : 2;
  const px = new Uint8Array(n * bpp);
  for (let i = 0; i < n; i++) {
    px[i * bpp] = rgba[i * 4];
    if (!opaque) px[i * bpp + 1] = rgba[i * 4 + 3];
  }
  return px;
}
export function buildRGB(rgba, opaque) {
  const n = rgba.length / 4;
  const bpp = opaque ? 3 : 4;
  const px = new Uint8Array(n * bpp);
  for (let i = 0; i < n; i++) {
    px[i * bpp] = rgba[i * 4];
    px[i * bpp + 1] = rgba[i * 4 + 1];
    px[i * bpp + 2] = rgba[i * 4 + 2];
    if (!opaque) px[i * bpp + 3] = rgba[i * 4 + 3];
  }
  return px;
}
export function buildIndexed(rgba, palMap) {
  const n = rgba.length / 4;
  const px = new Uint8Array(n);
  for (let i = 0; i < n; i++) {
    const key = rgba[i * 4] * 16777216 + rgba[i * 4 + 1] * 65536 + rgba[i * 4 + 2] * 256 + rgba[i * 4 + 3];
    px[i] = palMap.get(key);
  }
  return px;
}
export function paletteOrders(order) {
  const lum = (c) => 0.299 * c[0] + 0.587 * c[1] + 0.114 * c[2];
  const byLum = order.slice().sort((a, b) => lum(a) - lum(b) || a[0] - b[0] || a[1] - b[1] || a[2] - b[2] || a[3] - b[3]);
  const byRGB = order.slice().sort((a, b) => a[0] - b[0] || a[1] - b[1] || a[2] - b[2] || a[3] - b[3]);
  const lists = [order, byLum, byRGB];
  // Deduplicate identical orders.
  const out = [];
  const sigs = new Set();
  for (const list of lists) {
    const sig = list.map((c) => c.join(',')).join(';');
    if (!sigs.has(sig)) {
      sigs.add(sig);
      out.push(list);
    }
  }
  return out;
}

// ---------- PNG assembly ----------
export function assemblePng(w, h, colorType, zlibStream, palette, trns) {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(w, 0);
  ihdr.writeUInt32BE(h, 4);
  ihdr[8] = 8;
  ihdr[9] = colorType;
  const parts = [Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]), chunk('IHDR', ihdr)];
  if (palette) {
    const plte = Buffer.alloc(palette.length * 3);
    for (let i = 0; i < palette.length; i++) {
      plte[i * 3] = palette[i][0];
      plte[i * 3 + 1] = palette[i][1];
      plte[i * 3 + 2] = palette[i][2];
    }
    parts.push(chunk('PLTE', plte));
    if (trns) parts.push(chunk('tRNS', trns));
  }
  parts.push(chunk('IDAT', zlibStream));
  parts.push(chunk('IEND', Buffer.alloc(0)));
  return Buffer.concat(parts);
}

export function encodeImage(rgba, w, h) {
  const an = analyze(rgba);
  let best = null;
  const consider = (colorType, px, bpp, palette, trns) => {
    const { z, stream, winFilter, plainZ } = compressRep(px, w, h, bpp);
    const png = assemblePng(w, h, colorType, z, palette, trns);
    if (!best || png.length < best.png.length) {
      best = { png, colorType, palette, trns, stream, streamZlib: z.length, plainZ, winFilter, px, bpp };
    }
  };
  if (an.allGrey) {
    consider(an.allOpaque ? 0 : 4, buildGrey(rgba, an.allOpaque), an.allOpaque ? 1 : 2, null, null);
  } else if (an.unique <= 256) {
    for (const list of paletteOrders(an.order)) {
      const palMap = new Map();
      for (let i = 0; i < list.length; i++) {
        palMap.set(list[i][0] * 16777216 + list[i][1] * 65536 + list[i][2] * 256 + list[i][3], i);
      }
      let trns = null;
      if (!an.allOpaque) {
        let last = list.length - 1;
        while (last > 0 && list[last][3] === 255) last--;
        trns = Buffer.from(list.slice(0, last + 1).map((c) => c[3]));
      }
      consider(3, buildIndexed(rgba, palMap), 1, list, trns);
    }
  } else {
    consider(an.allOpaque ? 2 : 6, buildRGB(rgba, an.allOpaque), an.allOpaque ? 3 : 4, null, null);
  }
  // Greedy DEFLATE-cost filter selection on the winning representation — but
  // only when a non-zero filter won screening, i.e. filtering demonstrably
  // helps this image. On images where filter 0 wins (flat/noisy screenshots),
  // any per-row choice breaks the long exact repeats and loses, so the DP is
  // skipped there. On RGBA images (bpp >= 4) the 5-beam Viterbi version
  // runs instead of the greedy: it keeps alternative histories alive and
  // measured -2,186 bytes (i003) under the optimal encoder; on RGB (i006)
  // it gains only ~-550 bytes for +3.5 s and on grey it loses bytes, so
  // those keep the greedy.
  // Adoption is by plain zlib-9, like-for-like: alternate zlib strategies
  // are NOT compared here, because Z_FILTERED favours single-filter streams
  // and would veto a DP stream that the optimal encoder compresses better
  // (i006's fixed4 gains 4,429 bytes from Z_FILTERED while the DP stream
  // gains almost nothing, yet the DP stream's optimal encoding is 1,798
  // bytes smaller). The fallback PNG stays the best zlib PNG across both
  // streams; the DP stream is the candidate for the optimal re-encode.
  if (best.winFilter !== 0) {
    const dp = best.bpp >= 4
      ? beamFilterDeflate(best.px, w, h, best.bpp)
      : greedyFilterDeflate(best.px, w, h, best.bpp);
    const dpPlain = deflateSync(dp.stream, { level: 9, memLevel: 9 });
    if (dpPlain.length <= best.plainZ) {
      let dpZ = dpPlain;
      for (const strategy of [zlibConstants.Z_FILTERED, zlibConstants.Z_RLE]) {
        const z = deflateSync(dp.stream, { level: 9, memLevel: 9, strategy });
        if (z.length < dpZ.length) dpZ = z;
      }
      const dpPng = assemblePng(w, h, best.colorType, dpZ, best.palette, best.trns);
      const png = dpPng.length < best.png.length ? dpPng : best.png;
      best = { ...best, png, stream: dp.stream, streamZlib: dpZ.length };
    }
  }
  return best;
}

// Optimal-parse settings, tiered by filtered-stream size and by the winning
// stream's zlib-9 size (a direct measure of compressibility), never by the
// clock. Small streams can afford a deep hash chain; large streams use a
// cheaper one so the 60 s wall is never at risk. A deeper chain pays only when
// there are many long matches to find, i.e. on highly compressible streams —
// hence the zlib-size split inside the medium/large tiers (practice-tuned:
// medium RGB at 52K zlib gains ~3% from chain 1024, at 183K it gains ~0.1%);
// the dense length set pays on the alpha-noisy large stream but costs on the
// smooth one, hence the same split there.
export function tieredOpts(n, zlibSize = Infinity) {
  const blocks = [1, 2, 4, 8, 16];
  if (n <= 1200000) return { chain: 1024, goodLen: 258, iterations: 1, skipMinLen: 0, lengthSet: LENGTH_SET_DENSE, blockCounts: blocks };
  if (n <= 3000000) return { chain: zlibSize <= 60000 ? 1024 : 256, goodLen: 258, iterations: 1, skipMinLen: 0, lengthSet: LENGTH_SET_DENSE, blockCounts: blocks };
  return { chain: 256, goodLen: 258, iterations: 1, skipMinLen: 0, lengthSet: zlibSize <= 70000 ? LENGTH_SET_DENSE : LENGTH_SET, blockCounts: blocks };
}

// ---------- main (runs only when executed directly, not when imported) ----------

// ---------- optimal-parse DEFLATE encoder (RFC 1951) ----------
// Optimal-parse DEFLATE encoder, written from RFC 1951 (DEFLATE spec).
// Pure Node built-ins only. Deterministic: output is a pure function of the input bytes.
// Components (all original work, no kit code):
//   - hash-chain LZ77 match finder (longest + nearest match per position)
//   - shortest-path DP parse with a configurable length set, iterated against
//     optimal Huffman costs (fixed costs first, then length-limited Huffman)
//   - length-limited Huffman via frequency clamping (Gallager bound) + heap tree
//   - dynamic-Huffman block emission (with fixed-block fallback), zlib wrapper

// ---------------- RFC 1951 length / distance tables ----------------
export const LEN_BASE = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
export const LEN_EXTRA = [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
export const DIST_BASE = [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
export const DIST_EXTRA = [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];

export function lenCodeOf(len) {
  // returns code index 0..28 (symbol 257+idx)
  if (len === 258) return 28;
  let lo = 0, hi = 28;
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (LEN_BASE[mid] <= len) lo = mid; else hi = mid - 1; }
  return lo;
}
export function distCodeOf(d) {
  let lo = 0, hi = 29;
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (DIST_BASE[mid] <= d) lo = mid; else hi = mid - 1; }
  return lo;
}
// Fixed Huffman code lengths (RFC 1951 section 3.2.6)
export function fixedLitLen() {
  const l = new Uint8Array(288);
  for (let i = 0; i < 144; i++) l[i] = 8;
  for (let i = 144; i < 256; i++) l[i] = 9;
  for (let i = 256; i < 280; i++) l[i] = 7;
  for (let i = 280; i < 288; i++) l[i] = 8;
  return l;
}
export function fixedDistLen() { return new Uint8Array(30).fill(5); }

// ---------------- Huffman lengths (heap tree + frequency clamp) ----------------
// Gallager bound: a symbol with probability p has Huffman length < log2(1/p)+1.
// Clamping every nonzero frequency to >= total/2^(maxBits-1) keeps every length
// <= maxBits. If the result is still invalid (should not happen), fall back to a
// balanced complete code (valid by construction).
export function balancedLengths(freqs, maxBits = 15) {
  const n = freqs.length;
  const lengths = new Uint8Array(n);
  const syms = [];
  for (let i = 0; i < n; i++) if (freqs[i] > 0) syms.push(i);
  const k = syms.length;
  if (k === 0) return lengths;
  if (k === 1) { lengths[syms[0]] = 1; return lengths; }
  const L = Math.ceil(Math.log2(k));
  if (L > maxBits) throw new Error('balancedLengths: too many symbols for maxBits');
  const a = (1 << L) - k; // codes of length L-1; the rest get length L
  syms.sort((x, y) => freqs[y] - freqs[x] || x - y); // most frequent first
  for (let i = 0; i < syms.length; i++) lengths[syms[i]] = i < a ? L - 1 : L;
  return lengths;
}

export function huffmanLengths(freqs, maxBits = 15) {
  const n = freqs.length;
  const lengths = new Uint8Array(n);
  const syms = [];
  let total = 0;
  for (let i = 0; i < n; i++) if (freqs[i] > 0) { syms.push(i); total += freqs[i]; }
  if (syms.length === 0) return lengths;
  if (syms.length === 1) { lengths[syms[0]] = 1; return lengths; }
  const minF = Math.max(1, Math.floor(total / (1 << (maxBits - 1))));
  // Heap of nodes: each node {w, sym (-1 = internal), left, right}
  const w = [], sym = [], left = [], right = [];
  const heap = [];
  const push = (idx) => {
    heap.push(idx);
    let c = heap.length - 1;
    while (c > 0) {
      const p = (c - 1) >> 1;
      if (w[heap[p]] <= w[heap[c]]) break;
      [heap[p], heap[c]] = [heap[c], heap[p]];
      c = p;
    }
  };
  const pop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      let p = 0;
      for (;;) {
        const l = p * 2 + 1, r = l + 1;
        let m = p;
        if (l < heap.length && w[heap[l]] < w[heap[m]]) m = l;
        if (r < heap.length && w[heap[r]] < w[heap[m]]) m = r;
        if (m === p) break;
        [heap[p], heap[m]] = [heap[m], heap[p]];
        p = m;
      }
    }
    return top;
  };
  for (const s of syms) {
    w.push(Math.max(freqs[s], minF)); sym.push(s); left.push(-1); right.push(-1);
    push(w.length - 1);
  }
  while (heap.length > 1) {
    const a = pop(), b = pop();
    w.push(w[a] + w[b]); sym.push(-1); left.push(a); right.push(b);
    push(w.length - 1);
  }
  const root = heap[0];
  // Depths by walking down from the root.
  const stack = [[root, 0]];
  while (stack.length) {
    const [node, d] = stack.pop();
    if (sym[node] >= 0) lengths[sym[node]] = d;
    else { stack.push([left[node], d + 1]); stack.push([right[node], d + 1]); }
  }
  // Validate: every length <= maxBits and the Kraft sum is exactly 1.
  // If the clamp ever fails to bound the tree, fall back to a balanced code.
  let kraft = 0, mx = 0;
  for (let i = 0; i < n; i++) if (lengths[i]) { kraft += 2 ** -lengths[i]; mx = Math.max(mx, lengths[i]); }
  if (mx > maxBits || Math.abs(kraft - 1) > 1e-9) return balancedLengths(freqs, maxBits);
  return lengths;
}

// Canonical codes: returns Uint16Array of bit-reversed codes ready for LSB-first writing.
export function canonicalCodes(lengths) {
  const n = lengths.length;
  const codes = new Uint16Array(n);
  const blCount = new Uint16Array(16);
  for (let i = 0; i < n; i++) blCount[lengths[i]]++;
  blCount[0] = 0;
  const nextCode = new Uint16Array(16);
  let code = 0;
  for (let bits = 1; bits < 16; bits++) {
    code = (code + blCount[bits - 1]) << 1;
    nextCode[bits] = code;
  }
  for (let i = 0; i < n; i++) {
    const len = lengths[i];
    if (len === 0) continue;
    const c = nextCode[len]++;
    // Reverse the bits of c (len bits) for LSB-first output.
    let r = 0;
    for (let b = 0; b < len; b++) r = (r << 1) | ((c >> b) & 1);
    codes[i] = r;
  }
  return codes;
}

// ---------------- bit writer ----------------
export class BitWriter {
  constructor() { this.out = []; this.acc = 0; this.nbits = 0; this.bits = 0; }
  write(val, count) {
    if (count === 0) return;
    this.acc |= (val & (count === 32 ? 0xffffffff : ((1 << count) - 1))) << this.nbits;
    this.nbits += count;
    this.bits += count;
    while (this.nbits >= 8) { this.out.push(this.acc & 255); this.acc >>>= 8; this.nbits -= 8; }
  }
  align() {
    if (this.nbits > 0) { this.out.push(this.acc & 255); this.acc = 0; this.nbits = 0; }
  }
  bytes() { return Buffer.from(this.out); }
}

export function adler32(data) {
  let a = 1, b = 0;
  const MOD = 65521;
  let i = 0;
  const n = data.length;
  while (i < n) {
    const end = Math.min(i + 5552, n);
    for (; i < end; i++) { a += data[i]; b += a; }
    a %= MOD; b %= MOD;
  }
  return ((b << 16) | a) >>> 0;
}

// ---------------- LZ77 hash-chain match finder ----------------
// Per position: longest match (length, dist) and nearest match (length, dist).
// `skip` is an optional Uint8Array: positions with skip[i]=1 are not searched
// (used by the long-match skip heuristic); they get length 0.
export function findMatches(data, chainLimit = 64, goodLen = 32) {
  const n = data.length;
  const HASH_BITS = 15, HASH_SIZE = 1 << HASH_BITS, HASH_MASK = HASH_SIZE - 1;
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  const Lmax = new Uint16Array(n);
  const Dmax = new Uint32Array(n);
  const Lnear = new Uint16Array(n);
  const Dnear = new Uint32Array(n);
  const hashAt = (i) => (((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) * 0x9E3779B1) >>> 17 & HASH_MASK;
  for (let i = 0; i + 2 < n; i++) {
    const h = hashAt(i);
    let cand = head[h];
    const limit = i > 32768 ? i - 32768 : 0;
    let bestLen = 0, bestDist = 0, nearLen = 0, nearDist = 0;
    let chain = 0;
    let maxChain = chainLimit;
    const maxLen = Math.min(258, n - i);
    while (cand >= limit && chain < maxChain) {
      // zlib's scan_end trick: a candidate can only beat bestLen if it matches at
      // positions bestLen and bestLen-1. Otherwise skip it with two byte compares.
      // (Only valid once bestLen >= 3, which is also when the nearest is already set.)
      if (bestLen >= 3) {
        if (data[cand + bestLen] !== data[i + bestLen] || data[cand + bestLen - 1] !== data[i + bestLen - 1]) {
          cand = prev[cand];
          chain++;
          continue;
        }
      }
      let len = 0;
      // Compare 4 bytes at a time (unrolled), then finish byte by byte.
      const max4 = maxLen - 3;
      while (len < max4 && data[cand + len] === data[i + len] && data[cand + len + 1] === data[i + len + 1] && data[cand + len + 2] === data[i + len + 2] && data[cand + len + 3] === data[i + len + 3]) len += 4;
      while (len < maxLen && data[cand + len] === data[i + len]) len++;
      if (len >= 3) {
        const dist = i - cand;
        if (nearDist === 0) { nearLen = len; nearDist = dist; }
        if (len > bestLen || (len === bestLen && dist < bestDist)) { bestLen = len; bestDist = dist; }
        if (bestLen >= maxLen) break;
        // A good match found: shrink the remaining search (zlib-style), since a
        // much longer match at a far larger distance rarely pays for its distance code.
        if (bestLen >= goodLen && maxChain === chainLimit) maxChain = Math.max(16, chainLimit >> 2);
      }
      cand = prev[cand];
      chain++;
    }
    prev[i] = head[h];
    head[h] = i;
    Lmax[i] = bestLen; Dmax[i] = bestDist; Lnear[i] = nearLen; Dnear[i] = nearDist;
  }
  return { Lmax, Dmax, Lnear, Dnear };
}

// Long-match skip mask: positions covered by a match of length >= minLen starting
// at an earlier position are marked (their own match search is skipped in the DP).
// Returns a Uint8Array mask; the DP treats masked positions as literal-only.
export function longMatchSkip(Lmax, minLen = 64) {
  const n = Lmax.length;
  const skip = new Uint8Array(n);
  let coverUntil = -1;
  for (let i = 0; i < n; i++) {
    if (i <= coverUntil) { skip[i] = 1; continue; }
    if (Lmax[i] >= minLen) coverUntil = i + Lmax[i] - 1;
  }
  return skip;
}

// ---------------- optimal parse (shortest-path DP) ----------------
// lengthSet: sorted ascending match lengths offered at each position (plus Lmax itself).
export const LENGTH_SET = [3,4,5,6,7,8,10,13,17,23,31,43,59,83,115,163,227,258];
// Dense: every length 3..32 plus the large boundaries (plus Lmax, always offered).
export const LENGTH_SET_DENSE = [3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,43,59,83,115,163,227,258];
const NEAR_SET = [3,4,5,6,8];

export function costTables(litLen, distLen) {
  const litCost = new Float64Array(256);
  for (let i = 0; i < 256; i++) litCost[i] = litLen[i];
  const lenCost = new Float64Array(259);
  for (let len = 3; len <= 258; len++) {
    const ci = lenCodeOf(len);
    lenCost[len] = litLen[257 + ci] + LEN_EXTRA[ci];
  }
  const distCost = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) {
    const ci = distCodeOf(d);
    distCost[d] = distLen[ci] + DIST_EXTRA[ci];
  }
  return { litCost, lenCost, distCost };
}

// One DP pass. Returns { symbols, litFreq, distFreq, bits } where symbols is an
// array of steps: {lit} or {len, dist}. `skip` (optional) marks literal-only positions.
export function optimalParse(data, matches, tables, lengthSet = LENGTH_SET, skip = null) {
  const n = data.length;
  const { litCost, lenCost, distCost } = tables;
  const { Lmax, Dmax, Lnear, Dnear } = matches;
  // Lookup: is a length in the offered set?
  const inSet = new Uint8Array(259);
  for (const L of lengthSet) inSet[L] = 1;
  const cost = new Float64Array(n + 1).fill(Infinity);
  const prevPos = new Int32Array(n + 1);
  const prevLen = new Uint16Array(n + 1);
  const prevDist = new Uint32Array(n + 1);
  cost[0] = 0;
  for (let i = 0; i < n; i++) {
    const c = cost[i];
    if (c === Infinity) continue;
    const di = data[i];
    const lc = c + litCost[di];
    if (lc < cost[i + 1]) { cost[i + 1] = lc; prevPos[i + 1] = i; prevLen[i + 1] = 0; prevDist[i + 1] = 0; }
    if (skip && skip[i]) continue;
    const lm = Lmax[i];
    if (lm >= 3) {
      const dc = distCost[Dmax[i]];
      const base = c + dc;
      for (let k = 0; k < lengthSet.length; k++) {
        const L = lengthSet[k];
        if (L > lm) break;
        const nc = base + lenCost[L];
        const j = i + L;
        if (nc < cost[j]) { cost[j] = nc; prevPos[j] = i; prevLen[j] = L; prevDist[j] = Dmax[i]; }
      }
      if (!inSet[lm]) {
        const nc = base + lenCost[lm];
        const j = i + lm;
        if (nc < cost[j]) { cost[j] = nc; prevPos[j] = i; prevLen[j] = lm; prevDist[j] = Dmax[i]; }
      }
    }
    const ln = Lnear[i];
    if (ln >= 3 && Dnear[i] !== Dmax[i]) {
      const dc = distCost[Dnear[i]];
      const base = c + dc;
      for (let k = 0; k < NEAR_SET.length; k++) {
        const L = NEAR_SET[k];
        if (L > ln) break;
        const nc = base + lenCost[L];
        const j = i + L;
        if (nc < cost[j]) { cost[j] = nc; prevPos[j] = i; prevLen[j] = L; prevDist[j] = Dnear[i]; }
      }
    }
  }
  // Backtrack.
  const symbols = [];
  const litFreq = new Uint32Array(288);
  const distFreq = new Uint32Array(30);
  let pos = n;
  let bits = 0;
  while (pos > 0) {
    const p = prevPos[pos];
    const L = prevLen[pos];
    if (L === 0) {
      const b = data[p];
      symbols.push({ lit: b });
      litFreq[b]++;
      bits += litCost[b];
    } else {
      const d = prevDist[pos];
      symbols.push({ len: L, dist: d });
      litFreq[257 + lenCodeOf(L)]++;
      distFreq[distCodeOf(d)]++;
      bits += lenCost[L] + distCost[d];
    }
    pos = p;
  }
  symbols.reverse();
  litFreq[256]++; // end of block
  return { symbols, litFreq, distFreq, bits };
}

// ---------------- block emission ----------------
const CL_ORDER = [16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];

// Encode the code lengths of one alphabet with run-length codes 16/17/18.
// Returns the sequence of (symbol, extraBits, extraVal) triples.
function rleLengths(lengths) {
  const out = [];
  let i = 0;
  const n = lengths.length;
  while (i < n) {
    const v = lengths[i];
    let run = 1;
    while (i + run < n && lengths[i + run] === v) run++;
    if (v === 0) {
      let left = run;
      while (left >= 11) {
        const take = Math.min(left, 138);
        out.push([18, 7, take - 11]);
        left -= take;
      }
      if (left >= 3) { out.push([17, 3, left - 3]); left = 0; }
      while (left-- > 0) out.push([0, 0, 0]);
    } else {
      out.push([v, 0, 0]);
      let left = run - 1;
      while (left >= 3) {
        const take = Math.min(left, 6);
        out.push([16, 2, take - 3]);
        left -= take;
      }
      while (left-- > 0) out.push([v, 0, 0]);
    }
    i += run;
  }
  return out;
}

// Write one block's symbols with the FIXED Huffman codes (plus end-of-block).
// Caller must already have written BFINAL + BTYPE=01.
function emitFixedData(bw, symbols) {
  const litLen = fixedLitLen();
  const distLen = fixedDistLen();
  const litCode = canonicalCodes(litLen);
  const distCode = canonicalCodes(distLen);
  writeSymbols(bw, symbols, litCode, litLen, distCode, distLen);
  bw.write(litCode[256], litLen[256]);
}

// Write one block's symbols with a DYNAMIC Huffman header + codes (plus end-of-block).
// Caller must already have written BFINAL + BTYPE=10. Requires >= 1 match in symbols.
function emitDynamicData(bw, symbols) {
  const litFreq = new Uint32Array(288);
  const distFreq = new Uint32Array(30);
  for (const s of symbols) {
    if (s.lit !== undefined) litFreq[s.lit]++;
    else { litFreq[257 + lenCodeOf(s.len)]++; distFreq[distCodeOf(s.dist)]++; }
  }
  litFreq[256]++;
  const litLen = huffmanLengths(litFreq);
  const distLen = huffmanLengths(distFreq);
  // Ensure the distance alphabet has at least two codes (inflate compat).
  let distUsed = 0;
  for (let i = 0; i < 30; i++) if (distLen[i] > 0) distUsed++;
  if (distUsed === 1) {
    // Add a dummy second distance code of length 1 next to the used one.
    const usedIdx = distLen.findIndex((l) => l > 0);
    distLen[usedIdx] = 1;
    for (let i = 0; i < 30; i++) if (i !== usedIdx && distLen[i] === 0) { distLen[i] = 1; break; }
  }
  let hlit = 288;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const rle = rleLengths([...litLen.subarray(0, hlit), ...distLen.subarray(0, hdist)]);
  const clFreq = new Uint32Array(19);
  for (const [s] of rle) clFreq[s]++;
  // The code-length code's own lengths are stored in 3 bits, so they must be <= 7.
  // Use a balanced complete code (always valid, max length ceil(log2(19)) = 5).
  let clLen = balancedLengths(clFreq, 7);
  let clUsed = 0;
  for (let i = 0; i < 19; i++) if (clLen[i] > 0) clUsed++;
  if (clUsed < 2) {
    const first = clFreq.findIndex((f) => f > 0);
    clLen = new Uint8Array(19);
    clLen[first] = 1;
    for (let i = 0; i < 19; i++) if (i !== first && clFreq[i] === 0) { clLen[i] = 1; break; }
  }
  const clCode = canonicalCodes(clLen);
  let hclen = 19;
  while (hclen > 4 && clLen[CL_ORDER[hclen - 1]] === 0) hclen--;
  bw.write(hlit - 257, 5);
  bw.write(hdist - 1, 5);
  bw.write(hclen - 4, 4);
  for (let i = 0; i < hclen; i++) bw.write(clLen[CL_ORDER[i]], 3);
  for (const [s, eb, ev] of rle) {
    bw.write(clCode[s], clLen[s]);
    if (eb) bw.write(ev, eb);
  }
  const litCode = canonicalCodes(litLen);
  const distCode = canonicalCodes(distLen);
  writeSymbols(bw, symbols, litCode, litLen, distCode, distLen);
  bw.write(litCode[256], litLen[256]);
}

// Write the symbol sequence with the given Huffman tables (no end-of-block).
function writeSymbols(bw, symbols, litCode, litLen, distCode, distLen) {
  for (const s of symbols) {
    if (s.lit !== undefined) {
      bw.write(litCode[s.lit], litLen[s.lit]);
    } else {
      const ci = lenCodeOf(s.len);
      bw.write(litCode[257 + ci], litLen[257 + ci]);
      if (LEN_EXTRA[ci]) bw.write(s.len - LEN_BASE[ci], LEN_EXTRA[ci]);
      const di = distCodeOf(s.dist);
      bw.write(distCode[di], distLen[di]);
      if (DIST_EXTRA[di]) bw.write(s.dist - DIST_BASE[di], DIST_EXTRA[di]);
    }
  }
}

// Write one block (BFINAL + BTYPE + data) into a shared BitWriter. Compressed blocks
// are NOT byte-aligned: the next block starts on the very next bit.
function emitBlockInto(bw, symbols, isFinal, useDynamic) {
  bw.write(isFinal ? 1 : 0, 1);
  bw.write(useDynamic ? 2 : 1, 2);
  if (useDynamic) emitDynamicData(bw, symbols);
  else emitFixedData(bw, symbols);
}

// Bit length of one block (without the trailing byte alignment).
function blockBitLength(symbols, isFinal, useDynamic) {
  const w = new BitWriter();
  emitBlockInto(w, symbols, isFinal, useDynamic);
  return w.bits;
}

// Emit a full zlib stream for one or more blocks of symbols (each block gets its own
// Huffman tree; dynamic vs fixed chosen per block by bit length). Pure function of
// the symbols. Blocks are packed contiguously; only the final byte is aligned.
function emitZlibBlocks(data, symbolBlocks) {
  const bw = new BitWriter();
  for (let b = 0; b < symbolBlocks.length; b++) {
    const isFinal = b === symbolBlocks.length - 1;
    const syms = symbolBlocks[b];
    const hasMatch = syms.some((s) => s.len !== undefined);
    let useDynamic = false;
    if (hasMatch) {
      useDynamic = blockBitLength(syms, isFinal, true) < blockBitLength(syms, isFinal, false);
    }
    emitBlockInto(bw, syms, isFinal, useDynamic);
  }
  bw.align();
  const body = bw.bytes();
  const out = Buffer.alloc(2 + body.length + 4);
  out[0] = 0x78; out[1] = 0xda;
  body.copy(out, 2);
  out.writeUInt32BE(adler32(data), 2 + body.length);
  return out;
}

// Emit a full zlib stream for one parsed symbol sequence (single block).
function emitZlib(data, symbols) {
  return emitZlibBlocks(data, [symbols]);
}

// Split a symbol sequence into k contiguous chunks of (nearly) equal symbol count.
function splitSymbols(symbols, k) {
  if (k <= 1) return [symbols];
  const chunks = [];
  const per = Math.ceil(symbols.length / k);
  for (let i = 0; i < symbols.length; i += per) chunks.push(symbols.slice(i, i + per));
  return chunks;
}

// ---------------- cost-based block splitting (v4) ----------------
// Chooses block split points by DP over 32 elementary symbol chunks: a
// segment's cost is the entropy estimate of its lit/len + dist frequencies
// plus a header estimate, so blocks land where the symbol distribution
// changes instead of at equal intervals. Measured on the practice set:
// i002 -249, i003 -755, i006 -1,568 bytes vs the best equal split. The
// estimate only ranks candidates — the chosen split set is verified by
// actual emission and kept only if it beats the best equal split, so it
// can never hurt. DP time is ~0.1 s per image. Deterministic.
function symIds(symbols) {
  const n = symbols.length;
  const lit = new Uint16Array(n);
  const dist = new Int16Array(n);
  for (let i = 0; i < n; i++) {
    const s = symbols[i];
    if (s.lit !== undefined) { lit[i] = s.lit; dist[i] = -1; }
    else { lit[i] = 257 + lenCodeOf(s.len); dist[i] = distCodeOf(s.dist); }
  }
  return { lit, dist };
}
function segCost(prefLit, prefDist, a, b) {
  let bits = 0;
  let nLit = 0;
  for (let s = 0; s < 288; s++) {
    const c = prefLit[b][s] - prefLit[a][s];
    if (c) nLit += c;
  }
  if (nLit === 0) return Infinity;
  for (let s = 0; s < 288; s++) {
    const c = prefLit[b][s] - prefLit[a][s];
    if (c) bits -= c * Math.log2(c / nLit);
  }
  let nDist = 0;
  for (let s = 0; s < 30; s++) {
    const c = prefDist[b][s] - prefDist[a][s];
    if (c) nDist += c;
  }
  if (nDist > 0) {
    for (let s = 0; s < 30; s++) {
      const c = prefDist[b][s] - prefDist[a][s];
      if (c) bits -= c * Math.log2(c / nDist);
    }
  }
  let distinct = 0;
  for (let s = 0; s < 288; s++) if (prefLit[b][s] - prefLit[a][s] > 0) distinct++;
  for (let s = 0; s < 30; s++) if (prefDist[b][s] - prefDist[a][s] > 0) distinct++;
  bits += 120 + 5 * distinct;
  return bits;
}
// Returns { bounds: symbol indices where blocks start (excluding 0), blocks }.
function costBasedSplits(symbols, maxBlocks = 16, chunks = 32) {
  const n = symbols.length;
  const { lit, dist } = symIds(symbols);
  const M = Math.min(chunks, Math.max(1, Math.floor(n / 2000)));
  const bounds = [];
  for (let i = 0; i <= M; i++) bounds.push(Math.round((i * n) / M));
  const prefLit = [new Uint32Array(288)];
  const prefDist = [new Uint32Array(30)];
  for (let c = 0; c < M; c++) {
    const pl = new Uint32Array(prefLit[c]);
    const pd = new Uint32Array(prefDist[c]);
    for (let i = bounds[c]; i < bounds[c + 1]; i++) {
      pl[lit[i]]++;
      if (dist[i] >= 0) pd[dist[i]]++;
    }
    prefLit.push(pl);
    prefDist.push(pd);
  }
  const INF = Infinity;
  const dp = Array.from({ length: maxBlocks + 1 }, () => new Float64Array(M + 1).fill(INF));
  const prev = Array.from({ length: maxBlocks + 1 }, () => new Int16Array(M + 1).fill(-1));
  dp[0][0] = 0;
  for (let b = 1; b <= maxBlocks; b++) {
    for (let j = 1; j <= M; j++) {
      for (let i = b - 1; i < j; i++) {
        if (dp[b - 1][i] === INF) continue;
        const c = dp[b - 1][i] + segCost(prefLit, prefDist, i, j);
        if (c < dp[b][j]) { dp[b][j] = c; prev[b][j] = i; }
      }
    }
  }
  let bestB = 1, bestC = dp[1][M];
  for (let b = 2; b <= maxBlocks; b++) if (dp[b][M] < bestC) { bestC = dp[b][M]; bestB = b; }
  const splits = [];
  let j = M;
  for (let b = bestB; b >= 1; b--) { splits.push(bounds[j]); j = prev[b][j]; }
  splits.reverse();
  return { bounds: splits.slice(0, -1), blocks: bestB };
}

// ---------------- top-level: compress one raw stream ----------------
// opts: { chain, goodLen, iterations, lengthSet, skipMinLen, blockCounts }
// Returns a Buffer (zlib stream). Deterministic.
export function deflateOptimal(data, opts = {}) {
  const chain = opts.chain ?? 64;
  const goodLen = opts.goodLen ?? 32;
  const iterations = opts.iterations ?? 2;
  const lengthSet = opts.lengthSet ?? LENGTH_SET;
  const blockCounts = opts.blockCounts ?? [1, 2, 4, 8];
  const matches = findMatches(data, chain, goodLen);
  const skip = opts.skipMinLen ? longMatchSkip(matches.Lmax, opts.skipMinLen) : null;
  let tables = costTables(fixedLitLen(), fixedDistLen());
  let bestSymbols = null, bestSingle = Infinity;
  for (let it = 0; it <= iterations; it++) {
    const parsed = optimalParse(data, matches, tables, lengthSet, skip);
    const stream = emitZlib(data, parsed.symbols);
    if (stream.length < bestSingle) { bestSingle = stream.length; bestSymbols = parsed.symbols; }
    if (it === iterations) break;
    const litLen = huffmanLengths(parsed.litFreq);
    const distLen = huffmanLengths(parsed.distFreq);
    tables = costTables(litLen, distLen);
  }
  // Block splitting on the best parse (per-block Huffman trees).
  let best = emitZlib(data, bestSymbols);
  for (const k of blockCounts) {
    if (k <= 1) continue;
    const stream = emitZlibBlocks(data, splitSymbols(bestSymbols, k));
    if (stream.length < best.length) best = stream;
  }
  // Cost-based split points as one more candidate (v4): verified by actual
  // emission, kept only if it beats the best equal split.
  if (bestSymbols.length >= 4000) {
    const cb = costBasedSplits(bestSymbols);
    if (cb.bounds.length > 0) {
      const blocks = [];
      let prevB = 0;
      for (const b of cb.bounds) { blocks.push(bestSymbols.slice(prevB, b)); prevB = b; }
      blocks.push(bestSymbols.slice(prevB));
      const stream = emitZlibBlocks(data, blocks);
      if (stream.length < best.length) best = stream;
    }
  }
  return best;
}


// ---------- main (runs only when executed directly, not when imported) ----------
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
  const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
  for (const id of readdirSync(I).sort()) {
    const input = readFileSync(join(I, id, 'image.png'));
    const img = decodePng(input);
    const res = encodeImage(img.rgba, img.width, img.height);
    // Optimal-parse DEFLATE re-encode of the winning filtered stream — except
    // for very large, highly compressible streams (v4): there the optimal
    // parse gains only ~1-2% (i007: 1,213 bytes on a 60,833-byte stream) for
    // ~5.6 s of the 60 s wall, so the zlib PNG is used instead and the time
    // is spent where it pays. Rule is by data size and compressibility
    // (stream > 3 MB and zlib-9 < 70,000), never by the clock.
    const skipOptimal = res.stream.length > 3000000 && res.streamZlib < 70000;
    const optZ = skipOptimal ? null : deflateOptimal(res.stream, tieredOpts(res.stream.length, res.streamZlib));
    const optPng = optZ ? assemblePng(img.width, img.height, res.colorType, optZ, res.palette, res.trns) : null;
    const png = optPng && optPng.length < res.png.length ? optPng : res.png;
    mkdirSync(join(O, id), { recursive: true });
    writeFileSync(join(O, id, 'image.png'), png);
    console.error(`${id}: ${input.length} -> ${png.length} bytes`);
  }
}
