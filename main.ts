// Tiny stack VM: a faithful interpreter of make.fun's ISA v1 (kit ISA.md + vm.mjs).
// One run answers a whole set of instances; deterministic, stdlib only.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function execute(P: Uint8Array, I: Uint8Array): { out: Uint8Array; code: number } {
  const n = P.length;
  // Two-operand handlers, indexed by opcode - 0x10; null where the slot holds
  // a unary op (NEG/NOT) or nothing at all. Division by zero is screened
  // before dispatch, so the four quotient handlers never see b == 0.
  const BIN: Array<((a: number, b: number) => number) | null> = [
    (a, b) => (a + b) | 0,
    (a, b) => (a - b) | 0,
    (a, b) => Math.imul(a, b),
    (a, b) => (a === -2147483648 && b === -1 ? a : (a / b) | 0),
    (a, b) => (b === -1 ? 0 : (a % b) | 0),
    (a, b) => Math.floor((a >>> 0) / (b >>> 0)) | 0,
    (a, b) => ((a >>> 0) % (b >>> 0)) | 0,
    null,
    (a, b) => a & b,
    (a, b) => a | b,
    (a, b) => a ^ b,
    null,
    (a, b) => a << (b & 31),
    (a, b) => a >> (b & 31),
    (a, b) => (a >>> (b & 31)) | 0,
    null,
    (a, b) => (a === b ? 1 : 0),
    (a, b) => (a < b ? 1 : 0),
    (a, b) => ((a >>> 0) < (b >>> 0) ? 1 : 0),
  ];
  const T = new Int32Array(256);
  let d = 0;
  const R = new Int32Array(64);
  let c = 0;
  const V = new Int32Array(256);
  const O = new Uint8Array(65536);
  let o = 0, q = 0, pc = 0, s = 0;
  const fin = (code: number): { out: Uint8Array; code: number } => ({ out: O.slice(0, o), code });
  while (true) {
    if (s === 1000000) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = P[pc];
    let im = 0, nd = 0, gv = 0, ok = true;
    if (op === 0x00 || op === 0x34) {}
    else if (op === 0x01) { im = 1; gv = 1; }
    else if (op === 0x02) { im = 4; gv = 1; }
    else if (op === 0x03) nd = 1;
    else if (op === 0x04) { nd = 1; gv = 2; }
    else if (op === 0x05) { nd = 2; gv = 2; }
    else if (op === 0x06) { nd = 2; gv = 3; }
    else if (op === 0x07) { nd = 3; gv = 3; }
    else if (op === 0x17 || op === 0x1b) { nd = 1; gv = 1; }
    else if ((op >= 0x10 && op <= 0x16) || (op >= 0x18 && op <= 0x1a) || (op >= 0x1c && op <= 0x1e) || (op >= 0x20 && op <= 0x22)) { nd = 2; gv = 1; }
    else if (op === 0x30 || op === 0x33) im = 2;
    else if (op === 0x31 || op === 0x32) { im = 2; nd = 1; }
    else if (op === 0x40) { nd = 1; gv = 1; }
    else if (op === 0x41) nd = 2;
    else if (op === 0x50 || op === 0x51 || op === 0x53) nd = 1;
    else if (op === 0x52) gv = 1;
    else ok = false;
    if (!ok) return fin(5);
    if (pc + im >= n) return fin(9);
    s++;
    const nx = pc + 1 + im;
    if (d < nd) return fin(2);
    if (d - nd + gv > 256) return fin(3);
    pc = nx;
    switch (op) {
      case 0x00: return fin(0);
      case 0x01: T[d++] = (P[nx - 1] << 24) >> 24; break;
      case 0x02: T[d++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); break;
      case 0x03: d--; break;
      case 0x04: T[d] = T[d - 1]; d++; break;
      case 0x05: { const t = T[d - 1]; T[d - 1] = T[d - 2]; T[d - 2] = t; break; }
      case 0x06: T[d] = T[d - 2]; d++; break;
      case 0x07: { const a = T[d - 3]; T[d - 3] = T[d - 2]; T[d - 2] = T[d - 1]; T[d - 1] = a; break; }
      case 0x17: T[d - 1] = (-T[d - 1]) | 0; break;
      case 0x1b: T[d - 1] = ~T[d - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = T[d - 1], a = T[d - 2];
        if (op >= 0x13 && op <= 0x16 && b === 0) return fin(4);
        const h = BIN[op - 0x10];
        d -= 2; T[d++] = h ? h(a, b) : 0; break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const x = T[--d]; take = op === 0x31 ? x === 0 : x !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (c === 64) return fin(7);
        R[c++] = nx; pc = P[nx - 2] | (P[nx - 1] << 8); break;
      case 0x34:
        if (c === 0) return fin(8);
        pc = R[--c]; break;
      case 0x40: {
        const a = T[d - 1];
        if (a < 0 || a >= 256) return fin(6);
        T[d - 1] = V[a]; break;
      }
      case 0x41: {
        const a = T[d - 1], v = T[d - 2];
        if (a < 0 || a >= 256) return fin(6);
        d -= 2; V[a] = v; break;
      }
      case 0x50: {
        const w = new TextEncoder().encode(String(T[d - 1]));
        if (o + w.length > 65536) return fin(11);
        d--; O.set(w, o); o += w.length; break;
      }
      case 0x51:
        if (o + 1 > 65536) return fin(11);
        O[o++] = T[--d] & 255; break;
      case 0x52: T[d++] = q < I.length ? I[q++] : -1; break;
      case 0x53: return fin(T[--d] & 255);
    }
  }
}

const ID = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OD = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(ID, { withFileTypes: true }).filter((e) => e.isDirectory()).map((e) => e.name).sort()) {
  const r = execute(new Uint8Array(readFileSync(join(ID, id, 'program.bin'))), new Uint8Array(readFileSync(join(ID, id, 'input.bin'))));
  mkdirSync(join(OD, id), { recursive: true });
  writeFileSync(join(OD, id, 'stdout.bin'), r.out);
  writeFileSync(join(OD, id, 'exit.txt'), `${r.code}\n`);
}
