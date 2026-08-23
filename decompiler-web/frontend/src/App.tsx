import { useState, useCallback, useEffect } from 'react';
import { Loader2, Play } from 'lucide-react';
import { HexInput } from './components/HexInput';
import { OptionsPanel } from './components/OptionsPanel';
import { OutputEditor } from './components/OutputEditor';
import {
  decompile,
  fetchOptions,
  type OptionCatalogue,
  type OptionsObject,
} from './lib/api';


function App() {
  const [hexInput, setHexInput] = useState('');
  // Catalogue is the only option list and the only source of defaults.
  const [catalogue, setCatalogue] = useState<OptionCatalogue | null>(null);
  const [options, setOptions] = useState<OptionsObject | null>(null);
  const [optionsError, setOptionsError] = useState<string | null>(null);
  const [catalogueReload, setCatalogueReload] = useState(0);
  const [code, setCode] = useState('');
  const [elapsedMs, setElapsedMs] = useState<number | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [loading, setLoading] = useState(false);

  useEffect(() => {
    let cancelled = false;
    setOptionsError(null);
    fetchOptions()
      .then((cat) => {
        if (cancelled) return;
        setCatalogue(cat);
        // Server defaults == posting no options at all.
        setOptions(structuredClone(cat.defaults));
      })
      .catch((e: unknown) => {
        if (cancelled) return;
        setCatalogue(null);
        setOptions(null);
        setOptionsError(e instanceof Error ? e.message : 'Unknown error');
      });
    return () => {
      cancelled = true;
    };
  }, [catalogueReload]);

  const handleDecompile = useCallback(async () => {
    const hex = hexInput.trim();
    if (!hex) return;

    setLoading(true);
    setError(null);

    try {
      const result = await decompile(hex, options);
      setCode(result.code);
      setElapsedMs(result.elapsed_ms);
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Unknown error');
      setCode('');
      setElapsedMs(null);
    } finally {
      setLoading(false);
    }
  }, [hexInput, options]);

  const handleKeyDown = useCallback(
    (e: React.KeyboardEvent) => {
      if ((e.metaKey || e.ctrlKey) && e.key === 'Enter') {
        e.preventDefault();
        handleDecompile();
      }
    },
    [handleDecompile]
  );

  return (
    <div className="h-screen flex flex-col" onKeyDown={handleKeyDown}>
      <header className="flex items-center justify-between px-6 py-3 border-b border-zinc-800">
        <div className="flex items-center gap-3">
          <h1 className="text-lg font-semibold text-white">
            dehosk
          </h1>
          <span className="text-xs px-2 py-0.5 rounded-full bg-emerald-500/10 text-emerald-400 border border-emerald-500/20">
            UPLC to pseudocode
          </span>
        </div>
        <a
          href="https://github.com/nicholasgasior/aiken"
          target="_blank"
          rel="noopener noreferrer"
          className="text-xs text-zinc-500 hover:text-zinc-300 transition-colors"
        >
          GitHub
        </a>
      </header>

      <div className="flex-1 flex min-h-0">
        <div className="w-[420px] shrink-0 flex flex-col gap-4 p-4 border-r border-zinc-800 overflow-y-auto">
          <HexInput value={hexInput} onChange={setHexInput} />

          <button
            onClick={handleDecompile}
            disabled={loading || !hexInput.trim()}
            className="flex items-center justify-center gap-2 w-full py-2.5 rounded-lg text-sm font-medium transition-colors disabled:opacity-50 disabled:cursor-not-allowed bg-emerald-600 hover:bg-emerald-500 text-white"
          >
            {loading ? (
              <>
                <Loader2 size={16} className="animate-spin" />
                Decompiling...
              </>
            ) : (
              <>
                <Play size={16} />
                Decompile
                <kbd className="ml-1 text-[10px] px-1 py-0.5 rounded bg-emerald-700/50 text-emerald-200">
                  {navigator.platform?.includes('Mac') ? 'Cmd' : 'Ctrl'}+Enter
                </kbd>
              </>
            )}
          </button>

          {error && (
            <div className="px-3 py-2 rounded-lg bg-red-500/10 border border-red-500/20 text-sm text-red-400">
              {error}
            </div>
          )}

          <OptionsPanel
            catalogue={catalogue}
            options={options}
            onChange={setOptions}
            loadError={optionsError}
            onRetry={() => setCatalogueReload((n) => n + 1)}
          />
        </div>

        <div className="flex-1 p-4 min-w-0">
          <OutputEditor code={code} elapsedMs={elapsedMs} />
        </div>
      </div>

    </div>
  );
}


export default App;
