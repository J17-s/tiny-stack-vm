// A tiny stack VM for make.fun's tiny-stack-vm-01: the full ISA from the kit's ISA.md, traps and limits included.
// One run answers every instance under the input dir: /output/<id>/stdout.bin and /output/<id>/exit.txt.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode tables, indexed by opcode byte: immediate byte count (-1: no such opcode), values popped, values pushed.
const IM = new Int8Array(256).fill(-1);
const NEED = new Int8Array(256);
const GIVE = new Int8Array(256);
const def = (op, im, need, give) => { IM[op] = im; NEED[op] = need; GIVE[op] = give; };
def(0x00, 0, 0, 0); // HALT
def(0x01, 1, 0, 1); // PUSH8
def(0x02, 4, 0, 1); // PUSH32
def(0x03, 0, 1, 0); // POP
def(0x04, 0, 1, 2); // DUP
def(0x05, 0, 2, 2); // SWAP
def(0x06, 0, 2, 3); // OVER
def(0x07, 0, 3, 3); // ROT
for (let o = 0x10; o <= 0x22; o++) if (o !== 0x17 && o !== 0x1b && o !== 0x1f) def(o, 0, 2, 1); // binary ops
def(0x17, 0, 1, 1); // NEG
def(0x1b, 0, 1, 1); // NOT
def(0x30, 2, 0, 0); // JMP
def(0x31, 2, 1, 0); // JZ
def(0x32, 2, 1, 0); // JNZ
def(0x33, 2, 0, 0); // CALL
def(0x34, 0, 0, 0); // RET
def(0x40, 0, 1, 1); // LOAD
def(0x41, 0, 2, 0); // STORE
def(0x50, 0, 1, 0); // PRINT
def(0x51, 0, 1, 0); // PUTC
def(0x52, 0, 0, 1); // IN
def(0x53, 0, 1, 0); // EXIT

// Runs one program to its end; returns the bytes it wrote and its exit code (a trap's code when it traps).
function run(P, IN) {
  const n = P.length;
  const S = new Int32Array(256); // data stack
  const CS = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory words
  const out = [];
  let sp = 0, cp = 0, pc = 0, steps = 0, ip = 0;
  const end = (code) => ({ out, code });
  for (;;) {
    // One step, checks in the ISA's order: step limit, pc in range, opcode known, immediate fits, stack room.
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = P[pc];
    const im = IM[op];
    if (im < 0) return end(5);
    if (pc + im >= n) return end(9);
    steps++;
    if (sp < NEED[op]) return end(2);
    if (sp - NEED[op] + GIVE[op] > 256) return end(3);
    const nx = pc + 1 + im;
    pc = nx;
    switch (op) {
      case 0x00: return end(0); // HALT
      case 0x01: S[sp++] = (P[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: S[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: S[sp] = S[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; } // SWAP
      case 0x06: S[sp] = S[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; } // ROT
      case 0x17: S[sp - 1] = -S[sp - 1] | 0; break; // NEG
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = S[sp - 1], a = S[sp - 2];
        let r;
        if (op === 0x10) r = a + b | 0;
        else if (op === 0x11) r = a - b | 0;
        else if (op === 0x12) r = Math.imul(a, b); // exact low 32 bits
        else if (op === 0x13) { if (!b) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (!b) return end(4); r = b === -1 ? 0 : a % b | 0; }
        else if (op === 0x15) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (!b) return end(4); r = (a >>> 0) % (b >>> 0) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp--;
        S[sp - 1] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ: target is next instruction + signed offset
        const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) { const v = S[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33: // CALL: immediate is the absolute target
        if (cp === 64) return end(7);
        CS[cp++] = nx;
        pc = P[nx - 2] | (P[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return end(8);
        pc = CS[--cp];
        break;
      case 0x40: { // LOAD
        const ad = S[sp - 1];
        if (ad < 0 || ad > 255) return end(6);
        S[sp - 1] = M[ad];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const ad = S[sp - 1];
        if (ad < 0 || ad > 255) return end(6);
        M[ad] = S[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII; a print that would pass the output limit writes nothing
        const s = String(S[sp - 1]);
        if (out.length + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
        break;
      }
      case 0x51: // PUTC
        if (out.length === 65536) return end(11);
        out.push(S[--sp] & 255);
        break;
      case 0x52: // IN: -1 once the input is used up
        S[sp++] = ip < IN.length ? IN[ip++] : -1;
        break;
      case 0x53: return end(S[--sp] & 255); // EXIT
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), Uint8Array.from(r.out));
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}
