/* Wire types for `GET /api/options`. The crate owns the option list;
 * this file must not name a field, restate a default, or enumerate a
 * choice. Read `path` as segments and `value` as the serde tag — never
 * recover either from a label. */

/** Choice that writes `{ [key]: N }` instead of a bare tag. */
export interface ChoicePayload {
  type: 'count';
  /** The JSON key to write the count under — declared by the wire. */
  key: string;
  min: number;
  default: number;
}

export interface OptionChoice {
  /** The serde tag. This is what gets POSTed — never the label. */
  value: string;
  label: string;
  summary: string;
  /** Present when picking this choice writes an object, not a string. */
  payload?: ChoicePayload | null;
}

export type OptionKind =
  | { type: 'toggle' }
  | {
      type: 'choice';
      /** Label for the "not set" entry, or null if the field can't be unset. */
      unset: string | null;
      choices: OptionChoice[];
    };

export interface OptionDescriptor {
  /**
   * JSON path segments into the options object — a nested option
   * arrives as a multi-segment array, so nothing ever needs splitting.
   */
  path: string[];
  field: string;
  label: string;
  summary: string;
  /** Prose paragraphs; "" entries are deliberate blank lines. */
  detail: string[];
  cliFlag?: string | null;
  kind: OptionKind;
}

export interface OptionGroup {
  id: string;
  title: string;
  summary: string;
  detail: string[];
  /**
   * Path of the object backing this group, or null when the group has
   * no master switch. Used to IDENTIFY the group — never to compute its
   * contents (that would reintroduce a second list).
   */
  masterPath: string[] | null;
  options: OptionDescriptor[];
}

export interface OptionCatalogue {
  version: number;
  groups: OptionGroup[];
  /** A complete, POSTable options object: the server's own defaults. */
  defaults: OptionsObject;
}

/**
 * An options object, opaque by design: the panel reaches into it only
 * through the catalogue's `path` arrays.
 */
export type OptionsObject = Record<string, unknown>;

/**
 * Guard the wire shape before render. A 200 with valid JSON of the
 * wrong shape (proxy page, stale build) would TypeError out of the
 * panel and unmount the root. Shallow on purpose: structure only —
 * listing options here would be a second catalogue.
 */
function assertCatalogue(json: unknown): asserts json is OptionCatalogue {
  const bad = (why: string): never => {
    throw new Error(`Malformed options catalogue: ${why}`);
  };
  if (json == null || typeof json !== 'object') bad('response is not an object');
  const cat = json as Record<string, unknown>;
  if (!Array.isArray(cat.groups)) bad('`groups` is missing or not an array');
  if (cat.defaults == null || typeof cat.defaults !== 'object') {
    bad('`defaults` is missing or not an object');
  }
  for (const [i, g] of (cat.groups as unknown[]).entries()) {
    if (g == null || typeof g !== 'object') bad(`group ${i} is not an object`);
    const group = g as Record<string, unknown>;
    if (!Array.isArray(group.options)) {
      bad(`group ${i} has no \`options\` array`);
    }
    for (const [j, o] of (group.options as unknown[]).entries()) {
      if (o == null || typeof o !== 'object') bad(`group ${i} option ${j} is not an object`);
      const desc = o as Record<string, unknown>;
      if (!Array.isArray(desc.path)) bad(`group ${i} option ${j} has no \`path\` array`);
      const kind = desc.kind as Record<string, unknown> | null | undefined;
      if (kind == null || typeof kind !== 'object' || typeof kind.type !== 'string') {
        bad(`group ${i} option ${j} has no \`kind.type\``);
      }
    }
  }
}

export async function fetchOptions(): Promise<OptionCatalogue> {
  const res = await fetch('/api/options');
  if (!res.ok) {
    throw new Error(`Failed to load options catalogue (HTTP ${res.status})`);
  }
  let json: unknown;
  try {
    json = await res.json();
  } catch {
    throw new Error('Malformed options catalogue: response is not JSON');
  }
  assertCatalogue(json);
  return json;
}

/* The only two frontend helpers that treat an options object as structured. */

/** Read the value at `path`, or undefined if any segment is missing. */
export function getAtPath(obj: OptionsObject, path: string[]): unknown {
  let cur: unknown = obj;
  for (const seg of path) {
    if (cur == null || typeof cur !== 'object') return undefined;
    cur = (cur as Record<string, unknown>)[seg];
  }
  return cur;
}

/** New root with `value` at `path`; clone the spine so React sees each level change. */
export function setAtPath(
  obj: OptionsObject,
  path: string[],
  value: unknown
): OptionsObject {
  if (path.length === 0) return obj;
  const [head, ...rest] = path;
  const child = obj[head];
  return {
    ...obj,
    [head]:
      rest.length === 0
        ? value
        : setAtPath(
            (child != null && typeof child === 'object'
              ? child
              : {}) as OptionsObject,
            rest,
            value
          ),
  };
}

export interface DecompileResult {
  code: string;
  elapsed_ms: number;
}

export interface DecompileError {
  error: string;
  error_code: string;
}

/**
 * Omit `options` (null/undefined) to get server defaults — same as
 * posting the catalogue `defaults`, so decompile can run before load.
 */
export async function decompile(
  hexCode: string,
  options?: OptionsObject | null
): Promise<DecompileResult> {
  const res = await fetch('/api/decompile', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(
      options == null ? { hex_code: hexCode } : { hex_code: hexCode, options }
    ),
  });

  const data = await res.json();

  if (!res.ok) {
    throw new Error((data as DecompileError).error || 'Unknown error');
  }

  return data as DecompileResult;
}
