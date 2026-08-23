// Line-based scan of pretty-printed output for Monaco outline,
// jump-to-definition, and find-all-references. No scope walk: naming
// already suffixes collisions with `_N`, so name → first definition
// is enough.

export type DefKind =
  | 'validator'
  | 'purpose'
  | 'fn'
  | 'const'
  | 'let'
  | 'param'
  | 'pattern';

export interface Range {
  startLine: number; // 1-based, Monaco convention
  startCol: number; // 1-based
  endLine: number;
  endCol: number;
}

export interface Definition {
  name: string;
  kind: DefKind;
  /** Range of the full declaration (e.g. the entire `let` line, or the
   * `validator NAME { ... }` block). */
  range: Range;
  /** Range of just the name token — what Ctrl+click highlights. */
  nameRange: Range;
  /** Nested child definitions (purpose handlers under a validator, let
   * bindings inside a function body, etc.). */
  children: Definition[];
}

export interface Reference {
  name: string;
  range: Range;
}

export interface SymbolIndex {
  /** Top-level definitions in declaration order. */
  definitions: Definition[];
  /** All identifier occurrences that resolve to one of the definitions. */
  references: Reference[];
  /** name → its primary definition (first occurrence) for jump-to-def. */
  defByName: Map<string, Definition>;
  /** name → all reference ranges for find-all-references. */
  refsByName: Map<string, Reference[]>;
}

const KEYWORDS = new Set([
  'fn',
  'let',
  'when',
  'is',
  'if',
  'else',
  'expect',
  'rec',
  'trace',
  'delay',
  'force',
  'seq',
  'fail',
  'and',
  'or',
  'const',
  'validator',
  'pub',
  'type',
  'use',
  'as',
  'in',
  'todo',
]);

const BUILTIN_QUALIFIERS = new Set(['builtin', 'Data', 'List', 'Pair', 'ByteArray', 'Map']);

interface MutableDef extends Definition {
  children: MutableDef[];
}

/** A literal-stripped copy of the source line — string / hex literals and
 * line comments are replaced with spaces of the same width so identifier
 * offsets stay aligned with the original. */
function stripLiterals(line: string): string {
  let out = '';
  let i = 0;
  while (i < line.length) {
    const ch = line[i];

    // Line comment
    if (ch === '/' && line[i + 1] === '/') {
      out += ' '.repeat(line.length - i);
      return out;
    }

    // String at: @"..."
    if (ch === '@' && line[i + 1] === '"') {
      const end = line.indexOf('"', i + 2);
      const stop = end === -1 ? line.length : end + 1;
      out += ' '.repeat(stop - i);
      i = stop;
      continue;
    }

    // Regular string "..."
    if (ch === '"') {
      const end = line.indexOf('"', i + 1);
      const stop = end === -1 ? line.length : end + 1;
      out += ' '.repeat(stop - i);
      i = stop;
      continue;
    }

    // Hex byte array #"..."
    if (ch === '#' && line[i + 1] === '"') {
      const end = line.indexOf('"', i + 2);
      const stop = end === -1 ? line.length : end + 1;
      out += ' '.repeat(stop - i);
      i = stop;
      continue;
    }

    out += ch;
    i++;
  }
  return out;
}

/** Iterate all identifier tokens in a (literal-stripped) line. Returns
 * 0-based column offsets within the line. */
function* identifierTokens(line: string): Generator<{ name: string; col: number }> {
  // Identifiers NOT preceded by `.`, so `script_context.redeemer` yields
  // only `script_context`. A qualified name like `Data.un_int` yields
  // `Data`, which `looksLikeConstructorOrType` filters out later.
  const re = /(?<![.\w])[A-Za-z_]\w*/g;
  let m: RegExpExecArray | null;
  while ((m = re.exec(line)) !== null) {
    yield { name: m[0], col: m.index };
  }
}

function isCapitalized(name: string): boolean {
  const ch = name.charCodeAt(0);
  return ch >= 65 && ch <= 90;
}

/** Heuristic: does this name read as a constructor or a type? */
function looksLikeConstructorOrType(name: string): boolean {
  // Capitalized identifiers are constructors or types; `Constr<N>`
  // placeholders include `<` and never match an identifier token.
  return isCapitalized(name) || BUILTIN_QUALIFIERS.has(name);
}

/** Number literal detection: the identifier regex requires a leading
 * letter or `_`, so this only guards against `_42`. */
function looksLikeNumber(name: string): boolean {
  return /^_?\d+$/.test(name);
}

function range(
  startLine: number,
  startCol: number,
  endLine: number,
  endCol: number
): Range {
  return { startLine, startCol, endLine, endCol };
}

function pushDef(
  list: MutableDef[],
  name: string,
  kind: DefKind,
  line: number,
  nameStart: number,
  nameEnd: number,
  declStart: number = nameStart,
  declEnd: number = nameEnd
): MutableDef {
  const def: MutableDef = {
    name,
    kind,
    range: range(line, declStart + 1, line, declEnd + 1),
    nameRange: range(line, nameStart + 1, line, nameEnd + 1),
    children: [],
  };
  list.push(def);
  return def;
}

export function scanSymbols(code: string): SymbolIndex {
  const lines = code.split('\n');
  const stripped = lines.map(stripLiterals);

  // Top-level definitions in declaration order. Nested definitions are
  // attached to their enclosing parent's `children`.
  const topLevel: MutableDef[] = [];

  // Definition stack. Each entry notes the brace depth at which the
  // definition opened; it pops when the depth falls back to it.
  interface StackEntry {
    def: MutableDef;
    openDepth: number;
  }
  const stack: StackEntry[] = [];
  let braceDepth = 0;

  const defByName = new Map<string, Definition>();

  // Every definition discovered. `defByName` keeps the first
  // occurrence of each name as its primary def.
  const allDefs: MutableDef[] = [];

  // Attach a def to the current parent (or top level) and index it.
  function register(d: MutableDef) {
    if (stack.length > 0) {
      stack[stack.length - 1].def.children.push(d);
    } else {
      topLevel.push(d);
    }
    allDefs.push(d);
    if (!defByName.has(d.name)) {
      defByName.set(d.name, d);
    }
  }

  // Attaches the param to the parent's children (so the outline nests
  // it under the function) and indexes the name so refs resolve.
  function registerParam(parent: MutableDef, p: MutableDef) {
    parent.children.push(p);
    allDefs.push(p);
    if (!defByName.has(p.name)) {
      defByName.set(p.name, p);
    }
  }

  // Definition patterns. The ones that open a `{` on this or the next
  // line push a scope, popped later by brace depth.
  const validatorRe = /^(\s*)validator\s+(\w+)(?:\s*\(([^)]*)\))?\s*\{?/;
  const purposeRe = /^(\s*)(spend|mint|withdraw|certificate|publish|vote|propose|certify|else)\s*\(([^)]*)\)\s*\{?/;
  const fnNamedRe = /^(\s*)(?:rec\s+)?fn\s+(\w+)\s*\(([^)]*)\)\s*\{?/;
  const constRe = /^(\s*)const\s+(\w+)\s*=/;
  // Inline `let NAME[: Type] = …` — does not open a brace scope, but is
  // a definition.
  const letRe = /^(\s*)let\s+(\w+)(?:\s*:\s*[^=]+?)?\s*=/;
  // Anonymous fn opening a lambda scope: `fn(p1, p2) {` — the params
  // are local bindings; the `{` must be on the same line.
  const lambdaRe = /(?:^|[^a-zA-Z_])fn\s*\(([^)]*)\)\s*\{/;

  for (let lineIdx = 0; lineIdx < stripped.length; lineIdx++) {
    const raw = lines[lineIdx];
    const s = stripped[lineIdx];
    const lineNo = lineIdx + 1;

    // --- Definitions on this line ---
    let m: RegExpExecArray | null;

    if ((m = validatorRe.exec(s)) !== null) {
      const indent = m[1].length;
      const name = m[2];
      const paramsStr = m[3] ?? '';
      const nameStart = indent + 'validator '.length;
      const def = pushDef(
        [],
        name,
        'validator',
        lineNo,
        nameStart,
        nameStart + name.length,
        indent,
        s.length
      );
      register(def);
      if (paramsStr) {
        addParams(def, lineNo, raw, paramsStr, registerParam);
      }
      if (s.includes('{')) {
        stack.push({ def, openDepth: braceDepth });
        braceDepth = countBraces(s, braceDepth);
        continue;
      }
    } else if ((m = purposeRe.exec(s)) !== null) {
      const indent = m[1].length;
      const name = m[2];
      const paramsStr = m[3] ?? '';
      const nameStart = indent;
      const def = pushDef(
        [],
        name,
        'purpose',
        lineNo,
        nameStart,
        nameStart + name.length,
        indent,
        s.length
      );
      register(def);
      if (paramsStr) {
        addParams(def, lineNo, raw, paramsStr, registerParam);
      }
      if (s.includes('{')) {
        stack.push({ def, openDepth: braceDepth });
        braceDepth = countBraces(s, braceDepth);
        continue;
      }
    } else if ((m = fnNamedRe.exec(s)) !== null) {
      const indent = m[1].length;
      const name = m[2];
      const paramsStr = m[3] ?? '';
      const nameStartInLine = s.indexOf(name, indent);
      const def = pushDef(
        [],
        name,
        'fn',
        lineNo,
        nameStartInLine,
        nameStartInLine + name.length,
        indent,
        s.length
      );
      register(def);
      if (paramsStr) {
        addParams(def, lineNo, raw, paramsStr, registerParam);
      }
      if (s.includes('{')) {
        stack.push({ def, openDepth: braceDepth });
        braceDepth = countBraces(s, braceDepth);
        continue;
      }
    } else if ((m = constRe.exec(s)) !== null) {
      const indent = m[1].length;
      const name = m[2];
      const nameStart = indent + 'const '.length;
      const def = pushDef(
        [],
        name,
        'const',
        lineNo,
        nameStart,
        nameStart + name.length,
        indent,
        s.length
      );
      register(def);
      // No scope is pushed: the body may open `{` on a later line
      // (`const x = rec fn …`); the inner `rec fn` pushes its own.
    } else if ((m = letRe.exec(s)) !== null) {
      const indent = m[1].length;
      const name = m[2];
      const nameStart = indent + 'let '.length;
      const def = pushDef(
        [],
        name,
        'let',
        lineNo,
        nameStart,
        nameStart + name.length,
        indent,
        s.length
      );
      register(def);
    }

    // Anonymous lambda: no named definition, but its params become
    // bindings registered under the enclosing scope.
    const lambdaMatch = lambdaRe.exec(s);
    if (lambdaMatch && lambdaMatch[1]) {
      const paramStart = (lambdaMatch.index ?? 0) + lambdaMatch[0].indexOf('(') + 1;
      const enclosing = stack[stack.length - 1]?.def;
      if (enclosing) {
        addParamsAt(enclosing, lineNo, raw, lambdaMatch[1], paramStart, registerParam);
      }
    }

    braceDepth = countBraces(s, braceDepth);

    // Pop any stack entries whose scope has closed.
    while (stack.length > 0 && braceDepth <= stack[stack.length - 1].openDepth) {
      stack.pop();
    }
  }

  // Build references: identifier tokens matching a known definition
  // name, minus keywords, constructors, numbers and qualified tails.
  const references: Reference[] = [];
  const refsByName = new Map<string, Reference[]>();

  for (let lineIdx = 0; lineIdx < stripped.length; lineIdx++) {
    const s = stripped[lineIdx];
    const lineNo = lineIdx + 1;
    for (const tok of identifierTokens(s)) {
      if (KEYWORDS.has(tok.name)) continue;
      if (looksLikeConstructorOrType(tok.name)) continue;
      if (looksLikeNumber(tok.name)) continue;
      if (!defByName.has(tok.name)) continue;
      const ref: Reference = {
        name: tok.name,
        range: range(lineNo, tok.col + 1, lineNo, tok.col + 1 + tok.name.length),
      };
      references.push(ref);
      const list = refsByName.get(tok.name);
      if (list) list.push(ref);
      else refsByName.set(tok.name, [ref]);
    }
  }

  return {
    definitions: topLevel,
    references,
    defByName,
    refsByName,
  };
}

function countBraces(line: string, depth: number): number {
  let d = depth;
  for (const c of line) {
    if (c === '{') d++;
    else if (c === '}') d--;
  }
  return d;
}

/** Add comma-separated params from a paren'd list to a definition's
 * children. `paramsStr` is the raw content between `(` and `)`. */
function addParams(
  parent: MutableDef,
  lineNo: number,
  rawLine: string,
  paramsStr: string,
  registerFn: (parent: MutableDef, p: MutableDef) => void
) {
  // The `(` in the raw line anchors each param's column.
  const openIdx = rawLine.indexOf('(');
  if (openIdx < 0) return;
  addParamsAt(parent, lineNo, rawLine, paramsStr, openIdx + 1, registerFn);
}

function addParamsAt(
  parent: MutableDef,
  lineNo: number,
  rawLine: string,
  paramsStr: string,
  baseCol: number,
  registerFn: (parent: MutableDef, p: MutableDef) => void
) {
  void rawLine; // baseCol is already absolute; rawLine kept for symmetry
  let offset = 0;
  for (const piece of paramsStr.split(',')) {
    const trimmedLeft = piece.replace(/^\s+/, '');
    const lead = piece.length - trimmedLeft.length;
    // Strip optional `: Type` suffix
    const nameMatch = /^[A-Za-z_]\w*/.exec(trimmedLeft);
    if (nameMatch) {
      const name = nameMatch[0];
      if (name !== '_' && !KEYWORDS.has(name)) {
        const col = baseCol + offset + lead;
        const p: MutableDef = {
          name,
          kind: 'param',
          range: range(lineNo, col + 1, lineNo, col + 1 + name.length),
          nameRange: range(lineNo, col + 1, lineNo, col + 1 + name.length),
          children: [],
        };
        registerFn(parent, p);
      }
    }
    offset += piece.length + 1; // +1 for the comma
  }
}
