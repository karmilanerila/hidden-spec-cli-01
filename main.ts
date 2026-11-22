// mend: one patch tool for every AI edit format, per SPEC.md v1.
// Reads unified diffs, SEARCH/REPLACE blocks, V4A patches and JSON tool calls,
// finds the lines an edit names even when their whitespace drifted, and
// changes every file or none. Node 22, standard library only.
// Run as `node main.ts [--format=NAME] [--check] [--strict] [PATCH]`.
// When MAKEFUN_ENV_URL is set, hands over to runner.ts for a trial.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';
const rstrip = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};
const byteCmp = (a: string, b: string): number => Buffer.compare(Buffer.from(a), Buffer.from(b));

/** A patch's lines: split at \n, one trailing \r removed, no empty piece after a final \n. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file as lines: its line break, its lines, whether it ends with a line break. */
interface FileText {
  br: string;
  lines: string[];
  fin: boolean;
}
function parseFile(text: string): FileText {
  if (text === '') return { br: '\n', lines: [], fin: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const fin = text.endsWith(br);
  if (fin) parts.pop();
  return { br, lines: parts, fin };
}
function serialise(f: FileText): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.fin ? f.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** Per-run context shared by the parsers: strict matching and the moves that succeeded. */
interface Ctx {
  strict: boolean;
  moves: [string, string][];
}

/** Old lines O replaced by new lines N; nCtx[j] is the index in O of N's j-th line when it is a context line. */
interface Lines {
  o: string[];
  n: string[];
  nCtx: (number | null)[];
}

/** Tier equality for one line: 0 exact, 1 trailing spaces/tabs ignored, 2 both ends ignored. */
function tierEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return rstrip(a) === rstrip(b);
  return trimWs(a) === trimWs(b);
}
function occursAt(lines: string[], o: string[], pos: number, tier: number): boolean {
  if (pos < 0 || pos + o.length > lines.length) return false;
  for (let j = 0; j < o.length; j++) {
    if (!tierEq(lines[pos + j]!, o[j]!, tier)) return false;
  }
  return true;
}
function findOcc(lines: string[], o: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  for (let i = Math.max(0, from); i + o.length <= lines.length; i++) {
    if (occursAt(lines, o, i, tier)) out.push(i);
  }
  return out;
}
/** First tier (0, then 1, then 2; only 0 when strict) at which O occurs at or after `from`. */
function findTier(lines: string[], o: string[], strict: boolean, from = 0): { tier: number; pos: number[] } | null {
  const top = strict ? 0 : 2;
  for (let t = 0; t <= top; t++) {
    const pos = findOcc(lines, o, t, from);
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

/** N as written over the matched lines: context lines are the file's own, tier-2 lines re-indented. */
function mapNew(ln: Lines, file: string[], pos: number, tier: number): string[] {
  const out: string[] = [];
  const p = ln.o.length > 0 ? leadWs(ln.o[0]!) : '';
  const f = ln.o.length > 0 ? leadWs(file[pos]!) : '';
  for (let j = 0; j < ln.n.length; j++) {
    const c = ln.nCtx[j]!;
    if (c !== null) {
      out.push(file[pos + c]!);
      continue;
    }
    let s = ln.n[j]!;
    if (tier === 2 && s !== '' && s.trim() !== '' && s.startsWith(p)) s = f + s.slice(p.length);
    out.push(s);
  }
  return out;
}
function applyAt(file: string[], ln: Lines, pos: number, tier: number): string[] {
  return [...file.slice(0, pos), ...mapNew(ln, file, pos, tier), ...file.slice(pos + ln.o.length)];
}

/** Old/new lines from body items: 'c' context, 'o' old-only, 'n' new-only. */
interface BodyItem {
  k: 'c' | 'o' | 'n';
  t: string;
}
function linesFromBody(items: BodyItem[]): Lines {
  const ln: Lines = { o: [], n: [], nCtx: [] };
  for (const it of items) {
    if (it.k === 'c') {
      ln.o.push(it.t);
      ln.n.push(it.t);
      ln.nCtx.push(ln.o.length - 1);
    } else if (it.k === 'o') {
      ln.o.push(it.t);
    } else {
      ln.n.push(it.t);
      ln.nCtx.push(null);
    }
  }
  return ln;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const f = parseFile(before);
      if (line < 0 || line > f.lines.length) throw new Fail('no-match', p);
      f.lines.splice(line, 0, ...add);
      tree.now.set(p, serialise(f));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ---- Unified diffs (SPEC.md section 6) ---- */

interface Hunk {
  a: number;
  ln: Lines;
  noEol: boolean;
  noEolPlus: boolean;
  plus: string[];
}

function buildHunk(a: number, raw: string[]): Hunk {
  const items: BodyItem[] = [];
  const kinds: string[] = [];
  for (const b of raw) {
    if (b.startsWith(' ')) {
      items.push({ k: 'c', t: b.slice(1) });
      kinds.push('c');
    } else if (b.startsWith('-')) {
      items.push({ k: 'o', t: b.slice(1) });
      kinds.push('o');
    } else if (b.startsWith('+')) {
      items.push({ k: 'n', t: b.slice(1) });
      kinds.push('n');
    } else if (b.startsWith('\\')) {
      kinds.push('b');
    } else {
      items.push({ k: 'c', t: '' });
      kinds.push('c');
    }
  }
  let noEol = false;
  for (let k = kinds.length - 1; k >= 0; k--) {
    if (kinds[k] === 'c' || kinds[k] === 'n') {
      noEol = kinds[k + 1] === 'b';
      break;
    }
  }
  let noEolPlus = false;
  for (let k = kinds.length - 1; k >= 0; k--) {
    if (kinds[k] === 'n') {
      noEolPlus = kinds[k + 1] === 'b';
      break;
    }
  }
  const ln = linesFromBody(items);
  const plus: string[] = [];
  for (const it of items) if (it.k === 'n') plus.push(it.t);
  return { a, ln, noEol, noEolPlus, plus };
}

interface Section {
  hdrOld: string | null | undefined;
  hdrNew: string | null | undefined;
  renOld: string | undefined;
  renNew: string | undefined;
  diffOld: string;
  diffNew: string;
  create: boolean;
  del: boolean;
  hunks: Hunk[];
}

/** A --- / +++ path: text after the four characters, up to the first tab, spaces removed; null is /dev/null. */
function diffPath(raw: string): string | null {
  const t = raw.split('\t')[0]!.trim();
  if (t === '/dev/null') return null;
  if (t.startsWith('a/') || t.startsWith('b/')) return t.slice(2);
  return t;
}

function unifiedEdits(lines: string[], ctx: Ctx): Edit[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let inHeader = false;
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(l);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = { hdrOld: undefined, hdrNew: undefined, renOld: undefined, renNew: undefined, diffOld: m[1]!, diffNew: m[2]!, create: false, del: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      i += 1;
      continue;
    }
    if (l.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@( .*)?$/.exec(l);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const raw: string[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const b = lines[j]!;
        if (b.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (b.startsWith(' ') || b.startsWith('-') || b.startsWith('+') || b.startsWith('\\') || b === '') {
          raw.push(b);
          j += 1;
        } else break;
      }
      while (raw.length > 0 && raw[raw.length - 1] === '') raw.pop();
      cur.hunks.push(buildHunk(parseInt(m[1]!, 10), raw));
      inHeader = false;
      i = j;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const o = diffPath(l.slice(4));
      const n = diffPath(lines[i + 1]!.slice(4));
      if (cur !== null && inHeader) {
        cur.hdrOld = o;
        cur.hdrNew = n;
      } else {
        cur = { hdrOld: o, hdrNew: n, renOld: undefined, renNew: undefined, diffOld: '', diffNew: '', create: false, del: false, hunks: [] };
        sections.push(cur);
      }
      inHeader = true;
      i += 2;
      continue;
    }
    if (cur !== null && inHeader) {
      if (l.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (l.startsWith('rename from ')) cur.renOld = l.slice(12).trim();
      else if (l.startsWith('rename to ')) cur.renNew = l.slice(10).trim();
      else if (l.startsWith('new file mode')) cur.create = true;
      else if (l.startsWith('deleted file mode')) cur.del = true;
      i += 1;
      continue;
    }
    i += 1;
  }
  return sections.map((sec) => unifiedEdit(sec, ctx));
}

function unifiedEdit(sec: Section, ctx: Ctx): Edit {
  const oldP = sec.hdrOld !== undefined ? sec.hdrOld : sec.renOld !== undefined ? sec.renOld : sec.diffOld !== '' ? sec.diffOld : null;
  const newP = sec.hdrNew !== undefined ? sec.hdrNew : sec.renNew !== undefined ? sec.renNew : sec.diffNew !== '' ? sec.diffNew : null;
  const isCreate = sec.create || oldP === null;
  const isDelete = !isCreate && (sec.del || newP === null);
  const isMove = !isCreate && !isDelete && oldP !== null && newP !== null && oldP !== newP;
  return (tree) => {
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && newP !== oldP && !safe(newP)) throw new Fail('unsafe', newP);
    if (isCreate) {
      if (newP === null) throw new Fail('unsafe', '');
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const out: string[] = [];
      let totalPlus = 0;
      for (const h of sec.hunks) totalPlus += h.plus.length;
      let lastNoEol = false;
      for (const h of sec.hunks) {
        for (const t of h.plus) {
          out.push(t);
          totalPlus -= 1;
          if (totalPlus === 0) lastNoEol = h.noEolPlus;
        }
      }
      tree.now.set(newP, out.length === 0 ? '' : out.join('\n') + (lastNoEol ? '' : '\n'));
      return;
    }
    if (isDelete) {
      if (oldP === null || tree.get(oldP) === null) throw new Fail('missing', oldP ?? '');
      tree.now.set(oldP, null);
      return;
    }
    const path = oldP!;
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    if (isMove && tree.get(newP!) !== null) throw new Fail('exists', newP!);
    const f = parseFile(cur);
    let d = 0;
    for (const h of sec.hunks) {
      if (h.ln.o.length > 0) {
        const found = findTier(f.lines, h.ln.o, ctx.strict);
        if (found === null) throw new Fail('no-match', path);
        const target = h.a - 1 + d;
        let best = found.pos[0]!;
        let bd = Math.abs(best - target);
        for (const p of found.pos) {
          const dd = Math.abs(p - target);
          if (dd < bd) {
            bd = dd;
            best = p;
          }
        }
        const runsEnd = best + h.ln.o.length === f.lines.length;
        f.lines = applyAt(f.lines, h.ln, best, found.tier);
        if (runsEnd) f.fin = !h.noEol;
      } else {
        const ins = Math.max(0, Math.min(h.a + d, f.lines.length));
        const atEnd = ins === f.lines.length;
        f.lines = [...f.lines.slice(0, ins), ...h.ln.n, ...f.lines.slice(ins)];
        if (atEnd) f.fin = !h.noEol;
      }
      d += h.ln.n.length - h.ln.o.length;
    }
    const text = serialise(f);
    if (isMove) {
      tree.now.set(path, null);
      tree.now.set(newP!, text);
      ctx.moves.push([path, newP!]);
    } else {
      tree.now.set(path, text);
    }
  };
}

/* ---- SEARCH/REPLACE blocks (SPEC.md section 7) ---- */

function srEdits(lines: string[], ctx: Ctx): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchLine = i + 1;
    let eq = -1;
    for (let j = i + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    let rep = -1;
    if (eq >= 0) {
      for (let j = eq + 1; j < lines.length; j++) {
        if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
          rep = j;
          break;
        }
      }
    }
    if (eq < 0 || rep < 0) throw new Exit2(`error: parse ${searchLine}`);
    const oldLines = lines.slice(i + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    let path: string | null = null;
    for (let k = i - 1; k >= prevEnd; k--) {
      const t = lines[k]!.trim();
      if (t !== '' && !t.startsWith('```')) {
        path = t;
        break;
      }
    }
    if (path === null) {
      if (prevPath !== null) path = prevPath;
      else throw new Exit2(`error: parse ${searchLine}`);
    }
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
    const p = path;
    const ln: Lines = { o: oldLines, n: newLines, nCtx: newLines.map(() => null) };
    edits.push((tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (ln.o.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, ln.n.length === 0 ? '' : ln.n.join('\n') + '\n');
        return;
      }
      const cur = tree.get(p);
      if (cur === null) throw new Fail('missing', p);
      const f = parseFile(cur);
      const found = findTier(f.lines, ln.o, ctx.strict);
      if (found === null) throw new Fail('no-match', p);
      if (found.pos.length > 1) throw new Fail('ambiguous', p);
      f.lines = applyAt(f.lines, ln, found.pos[0]!, found.tier);
      tree.now.set(p, serialise(f));
    });
  }
  return edits;
}

/* ---- V4A patches (SPEC.md section 8) ---- */

interface VChunk {
  anchor: string | null;
  ln: Lines;
  eof: boolean;
}
interface VRaw {
  text: string;
  line: number;
}

function v4aEdits(lines: string[], ctx: Ctx): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  interface RawSec {
    kind: 'add' | 'del' | 'upd';
    path: string;
    headerLine: number;
    raw: VRaw[];
  }
  const secs: RawSec[] = [];
  let cur: RawSec | null = null;
  for (let i = first + 1; i < last; i++) {
    const l = lines[i]!;
    if (l.startsWith('*** Add File:') || l.startsWith('*** Delete File:') || l.startsWith('*** Update File:')) {
      const kind = l.startsWith('*** Add File:') ? 'add' : l.startsWith('*** Delete File:') ? 'del' : 'upd';
      const cut = kind === 'add' ? 14 : 17;
      cur = { kind, path: l.slice(cut).trim(), headerLine: i + 1, raw: [] };
      secs.push(cur);
      continue;
    }
    if (cur === null) {
      if (!blank(l)) throw new Exit2(`error: parse ${i + 1}`);
      continue;
    }
    cur.raw.push({ text: l, line: i + 1 });
  }
  const edits: Edit[] = [];
  for (const sec of secs) {
    while (sec.raw.length > 0 && blank(sec.raw[sec.raw.length - 1]!.text)) sec.raw.pop();
    if (sec.kind === 'add') {
      const addLines: string[] = [];
      for (const r of sec.raw) {
        if (r.text === '') addLines.push('');
        else if (r.text.startsWith('+')) addLines.push(r.text.slice(1));
        else throw new Exit2(`error: parse ${r.line}`);
      }
      const p = sec.path;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, addLines.length === 0 ? '' : addLines.join('\n') + '\n');
      });
      continue;
    }
    if (sec.kind === 'del') {
      if (sec.raw.length > 0) throw new Exit2(`error: parse ${sec.raw[0]!.line}`);
      const p = sec.path;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
      continue;
    }
    const raw = sec.raw;
    let idx = 0;
    let moveTo: string | null = null;
    if (raw.length > 0 && raw[0]!.text.startsWith('*** Move to:')) {
      moveTo = raw[0]!.text.slice(13).trim();
      idx = 1;
    }
    const chunks: VChunk[] = [];
    let curCh: { anchor: string | null; items: BodyItem[]; eof: boolean } | null = null;
    const closeChunk = (): void => {
      if (curCh !== null) {
        chunks.push({ anchor: curCh.anchor, ln: linesFromBody(curCh.items), eof: curCh.eof });
        curCh = null;
      }
    };
    for (let j = idx; j < raw.length; j++) {
      const { text, line } = raw[j]!;
      if (text.startsWith('@@')) {
        closeChunk();
        const a = text.slice(2).trim();
        curCh = { anchor: a === '' ? null : a, items: [], eof: false };
        continue;
      }
      if (text === '*** End of File') {
        if (curCh === null) throw new Exit2(`error: parse ${line}`);
        curCh.eof = true;
        closeChunk();
        continue;
      }
      if (text.startsWith('***')) throw new Exit2(`error: parse ${line}`);
      if (text.startsWith(' ') || text.startsWith('-') || text.startsWith('+') || text === '') {
        if (curCh === null) {
          if (chunks.length > 0) throw new Exit2(`error: parse ${line}`);
          curCh = { anchor: null, items: [], eof: false };
        }
        const k = text === '' || text[0] === ' ' ? 'c' : text[0] === '-' ? 'o' : 'n';
        curCh.items.push({ k, t: text === '' ? '' : text.slice(1) });
        continue;
      }
      throw new Exit2(`error: parse ${line}`);
    }
    closeChunk();
    if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${sec.headerLine}`);
    const p = sec.path;
    const mt = moveTo;
    const chs = chunks;
    edits.push((tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (mt !== null && !safe(mt)) throw new Fail('unsafe', mt);
      const curText = tree.get(p);
      if (curText === null) throw new Fail('missing', p);
      if (mt !== null && tree.get(mt) !== null) throw new Fail('exists', mt);
      const f = parseFile(curText);
      let cursor = 0;
      for (const ch of chs) {
        if (ch.anchor !== null) {
          const found = findTier(f.lines, [ch.anchor], ctx.strict, cursor);
          if (found === null) throw new Fail('no-match', p);
          cursor = found.pos[0]! + 1;
        }
        if (ch.ln.o.length > 0) {
          const found = findTier(f.lines, ch.ln.o, ctx.strict, cursor);
          if (found === null) throw new Fail('no-match', p);
          let pos = found.pos[0]!;
          if (ch.eof) {
            const endPos = f.lines.length - ch.ln.o.length;
            if (endPos < cursor || !found.pos.includes(endPos)) throw new Fail('no-match', p);
            pos = endPos;
          }
          f.lines = applyAt(f.lines, ch.ln, pos, found.tier);
          cursor = pos + ch.ln.n.length;
        } else {
          const ins = ch.eof ? f.lines.length : cursor;
          f.lines = [...f.lines.slice(0, ins), ...ch.ln.n, ...f.lines.slice(ins)];
          cursor = ins + ch.ln.n.length;
        }
      }
      const text = serialise(f);
      if (mt !== null) {
        tree.now.set(p, null);
        tree.now.set(mt, text);
        ctx.moves.push([p, mt]);
      } else {
        tree.now.set(p, text);
      }
    });
  }
  return edits;
}

/* ---- Invocation, output and exit codes (SPEC.md sections 1, 2 and 10) ---- */

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  const ctx: Ctx = { strict, moves: [] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, ctx)
          : kind === 'search-replace'
            ? srEdits(lines, ctx)
            : v4aEdits(lines, ctx);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  }
  const rowMap = new Map<string, { key: string; text: string }>();
  for (const p of [...tree.now.keys()].sort(byteCmp)) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rowMap.set(p, { key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const [o, n] of ctx.moves) {
    const dRow = rowMap.get(o);
    const aRow = rowMap.get(n);
    if (dRow !== undefined && aRow !== undefined && dRow.text.startsWith('D ') && aRow.text.startsWith('A ')) {
      rowMap.delete(o);
      rowMap.delete(n);
      rowMap.set(`\u0000${n}`, { key: n, text: `R ${o} -> ${n}` });
    }
  }
  const rows = [...rowMap.values()].sort((a, b) => byteCmp(a.key, b.key)).map((r) => r.text);
  if (!check) {
    const changed = [...tree.now.keys()].filter((p) => tree.original(p) !== tree.now.get(p));
    for (const p of changed) if (tree.now.get(p) === null) rmSync(p, { force: true });
    for (const p of changed) {
      const now = tree.now.get(p)!;
      if (now !== null) {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
