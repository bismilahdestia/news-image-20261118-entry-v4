// THE WORLD TODAY — front page for Wednesday 18 November 2026.
// A newspaper front page drawn by this program alone (Node 22, standard
// library only): it decodes four fresh news photographs, lays them out in
// a 2x2 front-page grid under a masthead, sets every headline, kicker and
// caption with a small bitmap face drawn here, and writes the finished
// 1024x1024 PNG to /output/entry.png (or $MAKEFUN_OUTPUT_DIR).
//
// Run:  mkdir -p out && MAKEFUN_OUTPUT_DIR=out node main.ts
// The program is fully deterministic: same bytes on every run.

import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { inflateSync, deflateSync } from 'node:zlib';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

// ---------------------------------------------------------------- paper
const W = 1024;
const H = 1024;
const PAPER = [246, 241, 231];
const INK = [22, 21, 19];
const RED = [158, 17, 17];
const BAR = [22, 21, 19];
const WHITE = [250, 248, 243];

const canvas = Buffer.alloc(W * H * 3);
function paint(r, g, b) {
  for (let i = 0; i < W * H; i++) {
    canvas[i * 3] = r;
    canvas[i * 3 + 1] = g;
    canvas[i * 3 + 2] = b;
  }
}
function setPx(x, y, c) {
  if (x < 0 || y < 0 || x >= W || y >= H) return;
  const o = (y * W + x) * 3;
  canvas[o] = c[0];
  canvas[o + 1] = c[1];
  canvas[o + 2] = c[2];
}
function rect(x, y, w, h, c) {
  for (let j = y; j < y + h; j++) {
    for (let i = x; i < x + w; i++) setPx(i, j, c);
  }
}
function hline(x, y, w, c, t = 1) {
  rect(x, y, w, t, c);
}

// ------------------------------------------------------- PNG decode
// Minimal decoder: 8-bit, non-interlaced, colour types 2 (RGB) and 6 (RGBA).
function crc32(buf) {
  let table = crc32.table;
  if (!table) {
    table = crc32.table = new Int32Array(256);
    for (let n = 0; n < 256; n++) {
      let c = n;
      for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
      table[n] = c;
    }
  }
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = table[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function pngChunk(type, data) {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, 'ascii');
  data.copy(out, 8);
  out.writeUInt32BE(crc32(out.subarray(4, 8 + data.length)), 8 + data.length);
  return out;
}
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  if (pb <= pc) return b;
  return c;
}
function decodePng(buf) {
  if (buf.readUInt32BE(0) !== 0x89504e47 || buf.readUInt32BE(4) !== 0x0d0a1a0a) {
    throw new Error('not a PNG');
  }
  let pos = 8;
  let width = 0;
  let height = 0;
  let bitDepth = 0;
  let colorType = 0;
  let interlace = 0;
  const idat = [];
  while (pos < buf.length) {
    const len = buf.readUInt32BE(pos);
    const type = buf.toString('ascii', pos + 4, pos + 8);
    const data = buf.subarray(pos + 8, pos + 8 + len);
    if (type === 'IHDR') {
      width = data.readUInt32BE(0);
      height = data.readUInt32BE(4);
      bitDepth = data[8];
      colorType = data[9];
      interlace = data[12];
    } else if (type === 'IDAT') {
      idat.push(data);
    } else if (type === 'IEND') {
      break;
    }
    pos += 12 + len;
  }
  if (bitDepth !== 8 || interlace !== 0) throw new Error('unsupported PNG');
  const bpp = colorType === 2 ? 3 : colorType === 6 ? 4 : 0;
  if (!bpp) throw new Error('unsupported colour type ' + colorType);
  const raw = inflateSync(Buffer.concat(idat));
  const stride = width * bpp;
  const img = Buffer.alloc(width * height * 3);
  let prev = Buffer.alloc(stride);
  let p = 0;
  for (let y = 0; y < height; y++) {
    const filter = raw[p++];
    const row = raw.subarray(p, p + stride);
    p += stride;
    const cur = Buffer.alloc(stride);
    for (let i = 0; i < stride; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev[i];
      const c = i >= bpp ? prev[i - bpp] : 0;
      let v = row[i];
      if (filter === 1) v = (v + a) & 0xff;
      else if (filter === 2) v = (v + b) & 0xff;
      else if (filter === 3) v = (v + ((a + b) >> 1)) & 0xff;
      else if (filter === 4) v = (v + paeth(a, b, c)) & 0xff;
      cur[i] = v;
    }
    for (let x = 0; x < width; x++) {
      const s = x * bpp; // offset inside this row's buffer, not the image
      const d = (y * width + x) * 3;
      img[d] = cur[s];
      img[d + 1] = cur[s + 1];
      img[d + 2] = cur[s + 2];
    }
    prev = cur;
  }
  return { width, height, data: img };
}

// ------------------------------------------------- photo placement
// Bilinear blit: draw a source rectangle into a destination rectangle.
function blit(src, sx, sy, sw, sh, dx, dy, dw, dh) {
  for (let j = 0; j < dh; j++) {
    const fy = sy + ((j + 0.5) / dh) * sh - 0.5;
    const y0 = Math.max(0, Math.floor(fy));
    const y1 = Math.min(src.height - 1, y0 + 1);
    const ty = Math.max(0, Math.min(1, fy - y0));
    for (let i = 0; i < dw; i++) {
      const fx = sx + ((i + 0.5) / dw) * sw - 0.5;
      const x0 = Math.max(0, Math.floor(fx));
      const x1 = Math.min(src.width - 1, x0 + 1);
      const tx = Math.max(0, Math.min(1, fx - x0));
      const o00 = (y0 * src.width + x0) * 3;
      const o10 = (y0 * src.width + x1) * 3;
      const o01 = (y1 * src.width + x0) * 3;
      const o11 = (y1 * src.width + x1) * 3;
      const px = dx + i;
      const py = dy + j;
      const o = (py * W + px) * 3;
      for (let k = 0; k < 3; k++) {
        const top = src.data[o00 + k] * (1 - tx) + src.data[o10 + k] * tx;
        const bot = src.data[o01 + k] * (1 - tx) + src.data[o11 + k] * tx;
        canvas[o + k] = Math.round(top * (1 - ty) + bot * ty);
      }
    }
  }
}
// Cover-fit: crop the photo's middle to the slot's aspect, then scale.
function placePhoto(src, dx, dy, dw, dh) {
  const want = dw / dh;
  const have = src.width / src.height;
  let sx = 0;
  let sy = 0;
  let sw = src.width;
  let sh = src.height;
  if (have > want) {
    sw = Math.round(src.height * want);
    sx = Math.round((src.width - sw) / 2);
  } else {
    sh = Math.round(src.width / want);
    sy = Math.round((src.height - sh) / 2);
  }
  blit(src, sx, sy, sw, sh, dx, dy, dw, dh);
}

// ------------------------------------------------------- bitmap face
// A 5x7 face, drawn from scratch for this page. Each glyph is seven rows;
// bit 4 is the left column. Only capitals, digits and the marks the page
// uses: the paper is set in capitals throughout, like a broadsheet.
const GLYPHS = {
  A: [0x0e, 0x11, 0x11, 0x1f, 0x11, 0x11, 0x11],
  B: [0x1e, 0x11, 0x11, 0x1e, 0x11, 0x11, 0x1e],
  C: [0x0e, 0x11, 0x10, 0x10, 0x10, 0x11, 0x0e],
  D: [0x1e, 0x11, 0x11, 0x11, 0x11, 0x11, 0x1e],
  E: [0x1f, 0x10, 0x10, 0x1e, 0x10, 0x10, 0x1f],
  F: [0x1f, 0x10, 0x10, 0x1e, 0x10, 0x10, 0x10],
  G: [0x0e, 0x11, 0x10, 0x17, 0x11, 0x11, 0x0f],
  H: [0x11, 0x11, 0x11, 0x1f, 0x11, 0x11, 0x11],
  I: [0x0e, 0x04, 0x04, 0x04, 0x04, 0x04, 0x0e],
  J: [0x07, 0x02, 0x02, 0x02, 0x02, 0x12, 0x0c],
  K: [0x11, 0x12, 0x14, 0x18, 0x14, 0x12, 0x11],
  L: [0x10, 0x10, 0x10, 0x10, 0x10, 0x10, 0x1f],
  M: [0x11, 0x1b, 0x15, 0x15, 0x11, 0x11, 0x11],
  N: [0x11, 0x19, 0x15, 0x13, 0x11, 0x11, 0x11],
  O: [0x0e, 0x11, 0x11, 0x11, 0x11, 0x11, 0x0e],
  P: [0x1e, 0x11, 0x11, 0x1e, 0x10, 0x10, 0x10],
  Q: [0x0e, 0x11, 0x11, 0x11, 0x15, 0x12, 0x0d],
  R: [0x1e, 0x11, 0x11, 0x1e, 0x14, 0x12, 0x11],
  S: [0x0f, 0x10, 0x10, 0x0e, 0x01, 0x01, 0x1e],
  T: [0x1f, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04],
  U: [0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x0e],
  V: [0x11, 0x11, 0x11, 0x11, 0x11, 0x0a, 0x04],
  W: [0x11, 0x11, 0x11, 0x15, 0x15, 0x15, 0x0a],
  X: [0x11, 0x11, 0x0a, 0x04, 0x0a, 0x11, 0x11],
  Y: [0x11, 0x11, 0x0a, 0x04, 0x04, 0x04, 0x04],
  Z: [0x1f, 0x01, 0x02, 0x04, 0x08, 0x10, 0x1f],
  '0': [0x0e, 0x11, 0x13, 0x15, 0x19, 0x11, 0x0e],
  '1': [0x04, 0x0c, 0x04, 0x04, 0x04, 0x04, 0x0e],
  '2': [0x0e, 0x11, 0x01, 0x06, 0x08, 0x10, 0x1f],
  '3': [0x1f, 0x02, 0x04, 0x02, 0x01, 0x11, 0x0e],
  '4': [0x02, 0x06, 0x0a, 0x12, 0x1f, 0x02, 0x02],
  '5': [0x1f, 0x10, 0x1e, 0x01, 0x01, 0x11, 0x0e],
  '6': [0x06, 0x08, 0x10, 0x1e, 0x11, 0x11, 0x0e],
  '7': [0x1f, 0x01, 0x02, 0x04, 0x08, 0x08, 0x08],
  '8': [0x0e, 0x11, 0x11, 0x0e, 0x11, 0x11, 0x0e],
  '9': [0x0e, 0x11, 0x11, 0x0f, 0x01, 0x02, 0x0c],
  ' ': [0, 0, 0, 0, 0, 0, 0],
  ',': [0, 0, 0, 0, 0x04, 0x04, 0x08],
  '.': [0, 0, 0, 0, 0, 0x0c, 0x0c],
  '-': [0, 0, 0, 0x1f, 0, 0, 0],
  "'": [0x04, 0x04, 0x08, 0, 0, 0, 0],
  ':': [0, 0x0c, 0x0c, 0, 0x0c, 0x0c, 0],
  '!': [0x04, 0x04, 0x04, 0x04, 0x04, 0, 0x04],
  '?': [0x0e, 0x11, 0x01, 0x02, 0x04, 0, 0x04],
  '(': [0x02, 0x04, 0x08, 0x08, 0x08, 0x04, 0x02],
  ')': [0x08, 0x04, 0x02, 0x02, 0x02, 0x04, 0x08],
  '/': [0x01, 0x02, 0x02, 0x04, 0x08, 0x08, 0x10],
  '\u2022': [0, 0, 0x0e, 0x0e, 0x0e, 0, 0],
};
function textWidth(str, scale) {
  return str.length * 6 * scale;
}
function drawGlyph(ch, x, y, scale, color) {
  const g = GLYPHS[ch];
  if (!g) return;
  for (let r = 0; r < 7; r++) {
    for (let c = 0; c < 5; c++) {
      if (g[r] & (0x10 >> c)) rect(x + c * scale, y + r * scale, scale, scale, color);
    }
  }
}
function drawText(str, x, y, scale, color) {
  for (let i = 0; i < str.length; i++) {
    drawGlyph(str[i], x + i * 6 * scale, y, scale, color);
  }
}
function drawTextCentered(str, cx, y, scale, color) {
  drawText(str, Math.round(cx - textWidth(str, scale) / 2), y, scale, color);
}
// Greedy word wrap to a pixel width; returns the lines.
function wrapText(str, maxWidth, scale) {
  const words = str.split(' ');
  const lines = [];
  let line = '';
  for (const w of words) {
    const next = line ? line + ' ' + w : w;
    if (textWidth(next, scale) <= maxWidth || !line) line = next;
    else {
      lines.push(line);
      line = w;
    }
  }
  if (line) lines.push(line);
  return lines;
}

// ------------------------------------------------------- PNG encode
// One filter per row, chosen by smallest absolute residual sum.
// Before encoding, every channel is rounded to a multiple of 4: the flat
// paper and ink barely move, while photographic gradients lose two bits of
// noise and compress far smaller. Fully deterministic.
function quantizeCanvas() {
  for (let i = 0; i < canvas.length; i++) canvas[i] = (canvas[i] + 4) & ~7;
}
function encodePng() {
  quantizeCanvas();
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(W, 0);
  ihdr.writeUInt32BE(H, 4);
  ihdr[8] = 8; // bit depth
  ihdr[9] = 2; // colour type 2: RGB
  ihdr[10] = 0;
  ihdr[11] = 0;
  ihdr[12] = 0;
  const stride = W * 3;
  const raw = Buffer.alloc(H * (stride + 1));
  const prev = Buffer.alloc(stride);
  for (let y = 0; y < H; y++) {
    const row = canvas.subarray(y * stride, (y + 1) * stride);
    let bestFilter = 0;
    let bestScore = Infinity;
    let bestBuf = null;
    for (let f = 0; f <= 4; f++) {
      const out = Buffer.alloc(stride);
      let score = 0;
      for (let i = 0; i < stride; i++) {
        const a = i >= 3 ? row[i - 3] : 0;
        const b = prev[i];
        const c = i >= 3 ? prev[i - 3] : 0;
        let pred = 0;
        if (f === 1) pred = a;
        else if (f === 2) pred = b;
        else if (f === 3) pred = (a + b) >> 1;
        else if (f === 4) pred = paeth(a, b, c);
        const v = (row[i] - pred) & 0xff;
        out[i] = v;
        score += v < 128 ? v : 256 - v;
      }
      if (score < bestScore) {
        bestScore = score;
        bestFilter = f;
        bestBuf = out;
      }
    }
    raw[y * (stride + 1)] = bestFilter;
    bestBuf.copy(raw, y * (stride + 1) + 1);
    row.copy(prev);
  }
  const idat = deflateSync(raw, { level: 9 });
  const sig = Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);
  return Buffer.concat([
    sig,
    pngChunk('IHDR', ihdr),
    pngChunk('IDAT', idat),
    pngChunk('IEND', Buffer.alloc(0)),
  ]);
}

// ------------------------------------------------------------- page
const here = dirname(fileURLToPath(import.meta.url));
function loadPhoto(name) {
  return decodePng(readFileSync(join(here, 'panels', name)));
}

const STORIES = [
  {
    photo: 'manila.png',
    kicker: 'ASIA',
    headline: 'TRUMP LANDS IN MANILA',
    caption: 'THE US PRESIDENT ARRIVES FOR ASEAN SUMMIT TALKS',
  },
  {
    photo: 'bridge.png',
    kicker: 'EUROPE',
    headline: 'CRIMEAN BRIDGE HIT AGAIN',
    caption: 'ROAD SPAN FALLS INTO THE KERCH STRAIT',
  },
  {
    photo: 'bahrain.png',
    kicker: 'MIDDLE EAST',
    headline: 'DRONES OVER BAHRAIN',
    caption: 'UNMANNED AIRCRAFT SEEN NEAR RADAR SITES',
  },
  {
    photo: 'nvidia.png',
    kicker: 'MARKETS',
    headline: 'NVIDIA DOUBLES REVENUE',
    caption: 'AI CHIP DEMAND DRIVES A RECORD QUARTER',
  },
];

function buildPage() {
  paint(...PAPER);
  // Frame.
  rect(10, 10, W - 20, 4, INK);
  rect(10, H - 14, W - 20, 4, INK);
  rect(10, 10, 4, H - 20, INK);
  rect(W - 14, 10, 4, H - 20, INK);

  // Masthead: nameplate, dateline, double rule.
  drawTextCentered('THE WORLD TODAY', W / 2, 30, 7, INK);
  drawTextCentered('WEDNESDAY, 18 NOVEMBER 2026', W / 2, 92, 3, INK);
  hline(24, 124, W - 48, INK, 3);
  hline(24, 130, W - 48, INK, 1);

  // Front-page grid: two rows, two stories each.
  const margin = 24;
  const gutter = 16;
  const cellW = (W - margin * 2 - gutter) / 2;
  const rowTop = [144, 548];
  const photoH = 288; // taller photos: fills the column down to the ticker
  for (let s = 0; s < 4; s++) {
    const story = STORIES[s];
    const col = s % 2;
    const row = Math.floor(s / 2);
    const x = margin + col * (cellW + gutter);
    const y = rowTop[row];
    const photo = loadPhoto(story.photo);
    placePhoto(photo, x, y, cellW, photoH);
    // Thin rule under the photograph.
    hline(x, y + photoH + 2, cellW, INK, 2);
    // Region kicker in red, then headline, then caption.
    const ty = y + photoH + 12;
    rect(x, ty + 2, 10, 10, RED);
    drawText(story.kicker, x + 16, ty, 2, RED);
    drawText(story.headline, x, ty + 24, 3, INK);
    const lines = wrapText(story.caption, cellW, 2);
    lines.forEach((ln, i) => drawText(ln, x, ty + 54 + i * 18, 2, INK));
  }

  // Bottom ticker: black bar, two lines of the day's other news.
  const tickY = 952;
  rect(margin, tickY, W - margin * 2, 62, BAR);
  drawTextCentered(
    'ALSO TODAY: UK SANCTIONS \u2022 CANADA-CHINA TRADE \u2022 CYCLONE AKVAN',
    W / 2,
    tickY + 12,
    2,
    WHITE,
  );
  drawTextCentered(
    'DHONI RETIRES \u2022 GAZA CEASEFIRE WARNING',
    W / 2,
    tickY + 36,
    2,
    WHITE,
  );
}

buildPage();
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
mkdirSync(outDir, { recursive: true });
writeFileSync(join(outDir, 'entry.png'), encodePng());
