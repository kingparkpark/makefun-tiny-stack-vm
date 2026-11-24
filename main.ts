// tiny-stack-vm: an interpreter for make.fun's tiny stack ISA (v1), from ISA.md.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode facts by opcode byte; immOf = -1 marks a byte naming no
// instruction. pop/push drive the underflow/overflow checks, ordered by
// the ISA before an instruction's own traps.
const immOf = new Int8Array(256).fill(-1);
const popOf = new Int8Array(256);
const pushOf = new Int8Array(256);
function def(op: number, imm: number, pop: number, push: number): void {
  immOf[op] = imm; popOf[op] = pop; pushOf[op] = push;
}
def(0x00, 0, 0, 0); // HALT
def(0x01, 1, 0, 1); // PUSH8
def(0x02, 4, 0, 1); // PUSH32
def(0x03, 0, 1, 0); // POP
def(0x04, 0, 1, 2); // DUP
def(0x05, 0, 2, 2); // SWAP
def(0x06, 0, 2, 3); // OVER
def(0x07, 0, 3, 3); // ROT
for (let op = 0x10; op <= 0x1e; op++) def(op, 0, 2, 1); // binary arithmetic
def(0x17, 0, 1, 1); // NEG (corrects range row)
def(0x1b, 0, 1, 1); // NOT (corrects range row)
for (let op = 0x20; op <= 0x22; op++) def(op, 0, 2, 1); // EQ LT LTU
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

const STEP_CAP = 1_000_000;
const OUT_CAP = 65_536;

// Runs one program to its end; a trap sets the exit code to its number.
function execute(prog: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const stack = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const buf = new Uint8Array(OUT_CAP);
  let sp = 0, depth = 0, pc = 0, steps = 0, used = 0, inAt = 0, code = -1;

  while (code < 0) {
    if (steps >= STEP_CAP) { code = 10; break; }
    if (pc < 0 || pc >= prog.length) { code = 9; break; }
    const op = prog[pc];
    const imm = immOf[op];
    if (imm < 0) { code = 5; break; }
    if (pc + imm >= prog.length) { code = 9; break; }
    steps++;
    if (sp < popOf[op]) { code = 2; break; }
    if (sp - popOf[op] + pushOf[op] > 256) { code = 3; break; }
    const next = pc + 1 + imm;
    pc = next;

    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      // Binary ops: the top of the stack is the right operand.
      const b = stack[sp - 1];
      const a = stack[sp - 2];
      let r = 0;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { // DIV, truncated toward zero
        if (b === 0) { code = 4; break; }
        r = a === -2147483648 && b === -1 ? a : Math.trunc(a / b);
      } else if (op === 0x14) { // MOD, sign of the dividend
        if (b === 0) { code = 4; break; }
        r = b === -1 ? 0 : a % b;
      } else if (op === 0x15) { // DIVU, operands read unsigned
        if (b === 0) { code = 4; break; }
        const au = a >>> 0, bu = b >>> 0;
        r = ((au - (au % bu)) / bu) | 0;
      } else if (op === 0x16) { // MODU
        if (b === 0) { code = 4; break; }
        r = ((a >>> 0) % (b >>> 0)) | 0;
      } else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
      stack[sp - 2] = r;
      sp--;
      continue;
    }

    switch (op) {
      case 0x00: code = 0; break; // HALT
      case 0x01: { // PUSH8, sign-extended
        const byte = prog[next - 1];
        stack[sp++] = byte < 128 ? byte : byte - 256;
        break;
      }
      case 0x02: // PUSH32, little-endian
        stack[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: stack[sp] = stack[sp - 1]; sp++; break; // DUP
      case 0x05: { // SWAP
        const t = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t;
        break;
      }
      case 0x06: stack[sp] = stack[sp - 2]; sp++; break; // OVER
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a;
        break;
      }
      case 0x17: stack[sp - 1] = (-stack[sp - 1]) | 0; break; // NEG, wraps
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]; break; // NOT
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
        const raw = prog[next - 2] | (prog[next - 1] << 8);
        const rel = raw < 32768 ? raw : raw - 65536;
        let take = true;
        if (op !== 0x30) {
          const v = stack[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: unsigned absolute target
        if (depth >= 64) { code = 7; break; }
        calls[depth++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34: // RET
        if (depth === 0) { code = 8; break; }
        pc = calls[--depth];
        break;
      case 0x40: { // LOAD
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) { code = 6; break; }
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) { code = 6; break; }
        mem[addr] = stack[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal, all of it or none
        const text = String(stack[sp - 1]);
        if (used + text.length > OUT_CAP) { code = 11; break; }
        sp--;
        for (let i = 0; i < text.length; i++) buf[used++] = text.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC
        if (used + 1 > OUT_CAP) { code = 11; break; }
        buf[used++] = stack[--sp] & 255;
        break;
      case 0x52: // IN: -1 at and past the end of input
        stack[sp++] = inAt < inp.length ? inp[inAt++] : -1;
        break;
      case 0x53: code = stack[sp - 1] & 255; break; // EXIT: low byte
    }
  }
  return { out: buf.slice(0, used), code };
}

const inDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(inDir).sort()) {
  const prog = readFileSync(join(inDir, id, 'program.bin'));
  const inp = readFileSync(join(inDir, id, 'input.bin'));
  const { out, code } = execute(prog, inp);
  mkdirSync(join(outDir, id), { recursive: true });
  writeFileSync(join(outDir, id, 'stdout.bin'), out);
  writeFileSync(join(outDir, id, 'exit.txt'), `${code}\n`);
}
