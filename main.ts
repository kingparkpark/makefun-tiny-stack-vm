import { mkdirSync as mk, readdirSync as rd, readFileSync as rf, writeFileSync as wf } from 'node:fs';
import { join as j } from 'node:path';
const I = new Int8Array(256).fill(-1), P = new Int8Array(256), Q = new Int8Array(256);
const D = (o, i, p, q) => { I[o] = i; P[o] = p; Q[o] = q; };
D(0, 0, 0, 0); D(1, 1, 0, 1); D(2, 4, 0, 1); D(3, 0, 1, 0); D(4, 0, 1, 2);
D(5, 0, 2, 2); D(6, 0, 2, 3); D(7, 0, 3, 3);
for (let o = 16; o <= 30; o++) D(o, 0, 2, 1);
D(23, 0, 1, 1); D(27, 0, 1, 1);
for (let o = 32; o <= 34; o++) D(o, 0, 2, 1);
D(48, 2, 0, 0); D(49, 2, 1, 0); D(50, 2, 1, 0); D(51, 2, 0, 0); D(52, 0, 0, 0);
D(64, 0, 1, 1); D(65, 0, 2, 0); D(80, 0, 1, 0); D(81, 0, 1, 0); D(82, 0, 0, 1); D(83, 0, 1, 0);
function X(g, n) {
  const S = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256), B = new Uint8Array(65536);
  let s = 0, d = 0, pc = 0, st = 0, u = 0, ia = 0, c = -1;
  while (c < 0) {
    if (st >= 1e6) { c = 10; break; }
    if (pc < 0 || pc >= g.length) { c = 9; break; }
    const o = g[pc], im = I[o];
    if (im < 0) { c = 5; break; }
    if (pc + im >= g.length) { c = 9; break; }
    st++;
    if (s < P[o]) { c = 2; break; }
    if (s - P[o] + Q[o] > 256) { c = 3; break; }
    const nx = pc + 1 + im;
    pc = nx;
    if (o >= 16 && o <= 34 && o !== 23 && o !== 27) {
      const b = S[s - 1], a = S[s - 2];
      let r = 0;
      if (o === 16) r = (a + b) | 0;
      else if (o === 17) r = (a - b) | 0;
      else if (o === 18) r = Math.imul(a, b);
      else if (o === 19) { if (b === 0) { c = 4; break; } r = a === -2147483648 && b === -1 ? a : Math.trunc(a / b); }
      else if (o === 20) { if (b === 0) { c = 4; break; } r = b === -1 ? 0 : a % b; }
      else if (o === 21) { if (b === 0) { c = 4; break; } const x = a >>> 0, y = b >>> 0; r = ((x - (x % y)) / y) | 0; }
      else if (o === 22) { if (b === 0) { c = 4; break; } r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (o === 24) r = a & b;
      else if (o === 25) r = a | b;
      else if (o === 26) r = a ^ b;
      else if (o === 28) r = a << (b & 31);
      else if (o === 29) r = a >> (b & 31);
      else if (o === 30) r = (a >>> (b & 31)) | 0;
      else if (o === 32) r = a === b ? 1 : 0;
      else if (o === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      S[s - 2] = r; s--; continue;
    }
    switch (o) {
      case 0: c = 0; break;
      case 1: { const v = g[nx - 1]; S[s++] = v < 128 ? v : v - 256; break; }
      case 2: S[s++] = g[nx - 4] | (g[nx - 3] << 8) | (g[nx - 2] << 16) | (g[nx - 1] << 24); break;
      case 3: s--; break;
      case 4: S[s] = S[s - 1]; s++; break;
      case 5: { const t = S[s - 1]; S[s - 1] = S[s - 2]; S[s - 2] = t; break; }
      case 6: S[s] = S[s - 2]; s++; break;
      case 7: { const a = S[s - 3]; S[s - 3] = S[s - 2]; S[s - 2] = S[s - 1]; S[s - 1] = a; break; }
      case 23: S[s - 1] = (-S[s - 1]) | 0; break;
      case 27: S[s - 1] = ~S[s - 1]; break;
      case 48: case 49: case 50: {
        const w = g[nx - 2] | (g[nx - 1] << 8), rel = w < 32768 ? w : w - 65536;
        let t = true;
        if (o !== 48) { const v = S[--s]; t = o === 49 ? v === 0 : v !== 0; }
        if (t) pc = nx + rel;
        break;
      }
      case 51:
        if (d >= 64) { c = 7; break; }
        C[d++] = nx; pc = g[nx - 2] | (g[nx - 1] << 8); break;
      case 52:
        if (d === 0) { c = 8; break; }
        pc = C[--d]; break;
      case 64: {
        const a = S[s - 1];
        if (a < 0 || a > 255) { c = 6; break; }
        S[s - 1] = M[a]; break;
      }
      case 65: {
        const a = S[s - 1];
        if (a < 0 || a > 255) { c = 6; break; }
        M[a] = S[s - 2]; s -= 2; break;
      }
      case 80: {
        const t = String(S[s - 1]);
        if (u + t.length > 65536) { c = 11; break; }
        s--;
        for (let i = 0; i < t.length; i++) B[u++] = t.charCodeAt(i);
        break;
      }
      case 81:
        if (u + 1 > 65536) { c = 11; break; }
        B[u++] = S[--s] & 255; break;
      case 82: S[s++] = ia < n.length ? n[ia++] : -1; break;
      case 83: c = S[s - 1] & 255; break;
    }
  }
  return { out: B.slice(0, u), code: c };
}
const inDir = process.env.MAKEFUN_INPUT_DIR ?? '/input', outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of rd(inDir).sort()) {
  const { out, code } = X(rf(j(inDir, id, 'program.bin')), rf(j(inDir, id, 'input.bin')));
  mk(j(outDir, id), { recursive: true });
  wf(j(outDir, id, 'stdout.bin'), out);
  wf(j(outDir, id, 'exit.txt'), `${code}\n`);
}
