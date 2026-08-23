import { useRef, useCallback, useEffect, useMemo, useState } from 'react';
import Editor, { type OnMount } from '@monaco-editor/react';
import type { editor as MonacoEditor, languages, IDisposable, IPosition } from 'monaco-editor';

type ITextModel = MonacoEditor.ITextModel;
import { Copy, Download, ListTree } from 'lucide-react';
import { dehoskLanguage, dehoskTheme } from '../lib/dehosk-language';
import { scanSymbols, type Definition, type SymbolIndex } from '../lib/dehosk-symbols';

interface OutputEditorProps {
  code: string;
  elapsedMs: number | null;
}

const LANG_ID = 'dehosk';
const THEME_ID = 'dehosk-dark';

export function OutputEditor({ code, elapsedMs }: OutputEditorProps) {
  const editorRef = useRef<MonacoEditor.IStandaloneCodeEditor | null>(null);
  const symbolsRef = useRef<SymbolIndex | null>(null);
  const providersRef = useRef<IDisposable[]>([]);
  const [showOutline, setShowOutline] = useState(true);

  // The Monaco provider closures are registered once at mount, so they
  // read the latest index through a ref rather than re-registering.
  const index = useMemo<SymbolIndex>(() => scanSymbols(code), [code]);
  useEffect(() => {
    symbolsRef.current = index;
  }, [index]);

  const handleMount: OnMount = useCallback((editor, monaco) => {
    editorRef.current = editor;

    // Register the dehosk Monaco language (idempotent — already registered ⇒ no-op).
    const known = monaco.languages
      .getLanguages()
      .some((l: { id: string }) => l.id === LANG_ID);
    if (!known) {
      monaco.languages.register({ id: LANG_ID });
      monaco.languages.setMonarchTokensProvider(LANG_ID, dehoskLanguage);
      monaco.editor.defineTheme(THEME_ID, dehoskTheme);
    }
    monaco.editor.setTheme(THEME_ID);

    // Tear down any providers from a previous mount before re-registering.
    providersRef.current.forEach((d) => d.dispose());
    providersRef.current = [];

    // --- Document symbols (powers Cmd+Shift+O outline + breadcrumbs) ---
    providersRef.current.push(
      monaco.languages.registerDocumentSymbolProvider(LANG_ID, {
        provideDocumentSymbols: (_model: ITextModel) => {
          const sym = symbolsRef.current;
          if (!sym) return [];
          return sym.definitions.map((d) => toMonacoSymbol(d, monaco));
        },
      })
    );

    // --- Definition (Ctrl+click / F12 jump) ---
    providersRef.current.push(
      monaco.languages.registerDefinitionProvider(LANG_ID, {
        provideDefinition: (model: ITextModel, position: IPosition) => {
          const sym = symbolsRef.current;
          if (!sym) return null;
          const word = model.getWordAtPosition(position);
          if (!word) return null;
          const def = sym.defByName.get(word.word);
          if (!def) return null;
          return {
            uri: model.uri,
            range: {
              startLineNumber: def.nameRange.startLine,
              startColumn: def.nameRange.startCol,
              endLineNumber: def.nameRange.endLine,
              endColumn: def.nameRange.endCol,
            },
          };
        },
      })
    );

    // --- References (Shift+F12 / right-click → Find All References) ---
    providersRef.current.push(
      monaco.languages.registerReferenceProvider(LANG_ID, {
        provideReferences: (
          model: ITextModel,
          position: IPosition,
          context: languages.ReferenceContext
        ) => {
          const sym = symbolsRef.current;
          if (!sym) return [];
          const word = model.getWordAtPosition(position);
          if (!word) return [];
          const name = word.word;
          const locations: languages.Location[] = [];

          if (context.includeDeclaration) {
            const def = sym.defByName.get(name);
            if (def) {
              locations.push({
                uri: model.uri,
                range: {
                  startLineNumber: def.nameRange.startLine,
                  startColumn: def.nameRange.startCol,
                  endLineNumber: def.nameRange.endLine,
                  endColumn: def.nameRange.endCol,
                },
              });
            }
          }

          for (const ref of sym.refsByName.get(name) ?? []) {
            locations.push({
              uri: model.uri,
              range: {
                startLineNumber: ref.range.startLine,
                startColumn: ref.range.startCol,
                endLineNumber: ref.range.endLine,
                endColumn: ref.range.endCol,
              },
            });
          }
          return locations;
        },
      })
    );
  }, []);

  useEffect(() => {
    return () => {
      providersRef.current.forEach((d) => d.dispose());
      providersRef.current = [];
    };
  }, []);

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(code);
    } catch {
      // Clipboard not available
    }
  };

  const handleDownload = () => {
    const blob = new Blob([code], { type: 'text/plain' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = 'decompiled.dehosk';
    a.click();
    URL.revokeObjectURL(url);
  };

  const handleJumpTo = useCallback((def: Definition) => {
    const editor = editorRef.current;
    if (!editor) return;
    const range = {
      startLineNumber: def.nameRange.startLine,
      startColumn: def.nameRange.startCol,
      endLineNumber: def.nameRange.endLine,
      endColumn: def.nameRange.endCol,
    };
    editor.revealRangeInCenter(range);
    editor.setSelection(range);
    editor.focus();
  }, []);

  return (
    <div className="flex flex-col h-full">
      <div className="flex items-center justify-between px-1 pb-2">
        <div className="flex items-center gap-2">
          <span className="text-sm font-medium text-zinc-300">Output</span>
          {elapsedMs !== null && (
            <span className="text-xs text-zinc-500">
              {elapsedMs.toFixed(1)}ms
            </span>
          )}
        </div>
        {code && (
          <div className="flex gap-1">
            <button
              onClick={() => setShowOutline((v) => !v)}
              className={`flex items-center gap-1.5 px-2 py-1 rounded-md text-xs transition-colors ${
                showOutline
                  ? 'bg-zinc-700 text-zinc-100'
                  : 'bg-zinc-800 hover:bg-zinc-700 text-zinc-400 hover:text-zinc-200'
              }`}
              title={
                showOutline
                  ? 'Hide outline'
                  : 'Show outline (top-level definitions)'
              }
            >
              <ListTree size={12} />
              Outline
            </button>
            <button
              onClick={handleCopy}
              className="flex items-center gap-1.5 px-2 py-1 rounded-md text-xs bg-zinc-800 hover:bg-zinc-700 text-zinc-400 hover:text-zinc-200 transition-colors"
              title="Copy to clipboard"
            >
              <Copy size={12} />
              Copy
            </button>
            <button
              onClick={handleDownload}
              className="flex items-center gap-1.5 px-2 py-1 rounded-md text-xs bg-zinc-800 hover:bg-zinc-700 text-zinc-400 hover:text-zinc-200 transition-colors"
              title="Download decompiled output"
            >
              <Download size={12} />
              Save
            </button>
          </div>
        )}
      </div>
      <div className="flex-1 flex gap-2 min-h-0">
        <div className="flex-1 rounded-lg overflow-hidden border border-zinc-800">
          <Editor
            height="100%"
            language={LANG_ID}
            theme={THEME_ID}
            value={code}
            onMount={handleMount}
            options={{
              readOnly: true,
              minimap: { enabled: false },
              fontSize: 13,
              lineNumbers: 'on',
              scrollBeyondLastLine: false,
              // NEVER wrap: deeply-indented output would break a token
              // like `[(lam i_42` across lines. Scroll horizontally instead.
              wordWrap: 'off',
              // Drop indentation / bracket-pair guides: on deeply-nested,
              // read-only output they render as a noisy vertical grid.
              guides: {
                indentation: false,
                highlightActiveIndentation: false,
                bracketPairs: false,
                bracketPairsHorizontal: false,
              },
              padding: { top: 12 },
              renderLineHighlight: 'none',
              overviewRulerLanes: 0,
              hideCursorInOverviewRuler: true,
              overviewRulerBorder: false,
              scrollbar: {
                verticalScrollbarSize: 8,
                horizontalScrollbarSize: 8,
              },
            }}
          />
        </div>
        {showOutline && code && (
          <OutlinePanel definitions={index.definitions} onJump={handleJumpTo} />
        )}
      </div>
      <KeyHints visible={code.length > 0} />
    </div>
  );
}

function KeyHints({ visible }: { visible: boolean }) {
  if (!visible) return null;
  return (
    <div className="flex items-center gap-3 pt-1.5 text-[10px] text-zinc-500">
      <span><kbd className="px-1 py-0.5 bg-zinc-800 rounded">⌘</kbd>+click — jump to definition</span>
      <span><kbd className="px-1 py-0.5 bg-zinc-800 rounded">⇧F12</kbd> — find references</span>
      <span><kbd className="px-1 py-0.5 bg-zinc-800 rounded">⌘⇧O</kbd> — go to symbol</span>
    </div>
  );
}

interface OutlinePanelProps {
  definitions: Definition[];
  onJump: (def: Definition) => void;
}

function OutlinePanel({ definitions, onJump }: OutlinePanelProps) {
  if (definitions.length === 0) {
    return (
      <div className="w-64 rounded-lg border border-zinc-800 bg-zinc-950/40 p-3 text-xs text-zinc-500">
        No top-level definitions detected.
      </div>
    );
  }
  return (
    <div className="w-64 rounded-lg border border-zinc-800 bg-zinc-950/40 overflow-y-auto">
      <div className="sticky top-0 px-3 py-2 text-[11px] uppercase tracking-wider text-zinc-500 bg-zinc-950/80 border-b border-zinc-800">
        Outline
      </div>
      <ul className="py-1">
        {definitions.map((def, i) => (
          <OutlineNode key={i} def={def} depth={0} onJump={onJump} />
        ))}
      </ul>
    </div>
  );
}

function OutlineNode({
  def,
  depth,
  onJump,
}: {
  def: Definition;
  depth: number;
  onJump: (def: Definition) => void;
}) {
  return (
    <li>
      <button
        onClick={() => onJump(def)}
        className="w-full flex items-center gap-2 px-3 py-1 text-left text-xs hover:bg-zinc-800/60 text-zinc-300"
        style={{ paddingLeft: `${12 + depth * 12}px` }}
      >
        <KindBadge kind={def.kind} />
        <span className="truncate">{def.name}</span>
        <span className="ml-auto text-[10px] text-zinc-600">{def.nameRange.startLine}</span>
      </button>
      {def.children.length > 0 && (
        <ul>
          {def.children.map((c, i) => (
            <OutlineNode key={i} def={c} depth={depth + 1} onJump={onJump} />
          ))}
        </ul>
      )}
    </li>
  );
}

function KindBadge({ kind }: { kind: Definition['kind'] }) {
  const cfg: Record<Definition['kind'], { label: string; color: string }> = {
    validator: { label: 'V', color: 'text-emerald-400 bg-emerald-500/10' },
    purpose: { label: 'P', color: 'text-sky-400 bg-sky-500/10' },
    fn: { label: 'fn', color: 'text-violet-400 bg-violet-500/10' },
    const: { label: 'c', color: 'text-amber-400 bg-amber-500/10' },
    let: { label: 'l', color: 'text-zinc-400 bg-zinc-500/10' },
    param: { label: 'p', color: 'text-zinc-500 bg-zinc-700/30' },
    pattern: { label: 'pat', color: 'text-rose-400 bg-rose-500/10' },
  };
  const { label, color } = cfg[kind];
  return (
    <span
      className={`inline-flex items-center justify-center min-w-[18px] h-4 px-1 rounded text-[9px] font-mono ${color}`}
    >
      {label}
    </span>
  );
}

function toMonacoSymbol(def: Definition, monaco: typeof import('monaco-editor')): languages.DocumentSymbol {
  const kindMap: Record<Definition['kind'], languages.SymbolKind> = {
    validator: monaco.languages.SymbolKind.Class,
    purpose: monaco.languages.SymbolKind.Method,
    fn: monaco.languages.SymbolKind.Function,
    const: monaco.languages.SymbolKind.Constant,
    let: monaco.languages.SymbolKind.Variable,
    param: monaco.languages.SymbolKind.Variable,
    pattern: monaco.languages.SymbolKind.Variable,
  };
  return {
    name: def.name,
    detail: def.kind,
    kind: kindMap[def.kind],
    tags: [],
    range: {
      startLineNumber: def.range.startLine,
      startColumn: def.range.startCol,
      endLineNumber: def.range.endLine,
      endColumn: def.range.endCol,
    },
    selectionRange: {
      startLineNumber: def.nameRange.startLine,
      startColumn: def.nameRange.startCol,
      endLineNumber: def.nameRange.endLine,
      endColumn: def.nameRange.endCol,
    },
    children: def.children.map((c) => toMonacoSymbol(c, monaco)),
  };
}
