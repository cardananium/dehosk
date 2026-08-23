import { ClipboardPaste, X } from 'lucide-react';

interface HexInputProps {
  value: string;
  onChange: (value: string) => void;
}

export function HexInput({ value, onChange }: HexInputProps) {
  const byteCount = Math.floor(value.replace(/\s/g, '').length / 2);

  const handlePaste = async () => {
    try {
      const text = await navigator.clipboard.readText();
      onChange(text.trim());
    } catch {
      // Clipboard not available
    }
  };

  return (
    <div className="flex flex-col gap-2">
      <div className="flex items-center justify-between">
        <label className="text-sm font-medium text-zinc-300">
          UPLC Hex Bytecode
        </label>
        <span className="text-xs text-zinc-500">
          {byteCount > 0 ? `${byteCount.toLocaleString()} bytes` : ''}
        </span>
      </div>
      <div className="relative">
        <textarea
          value={value}
          onChange={(e) => onChange(e.target.value)}
          placeholder="Paste hex-encoded UPLC bytecode here (e.g. 46010000200101)"
          className="w-full h-48 px-3 py-2 bg-zinc-900 border border-zinc-700 rounded-lg text-sm font-mono text-zinc-200 placeholder:text-zinc-600 resize-none focus:outline-none focus:ring-2 focus:ring-emerald-500/50 focus:border-emerald-500/50"
          spellCheck={false}
        />
        <div className="absolute top-2 right-2 flex gap-1">
          <button
            onClick={handlePaste}
            className="p-1.5 rounded-md bg-zinc-800 hover:bg-zinc-700 text-zinc-400 hover:text-zinc-200 transition-colors"
            title="Paste from clipboard"
          >
            <ClipboardPaste size={14} />
          </button>
          {value && (
            <button
              onClick={() => onChange('')}
              className="p-1.5 rounded-md bg-zinc-800 hover:bg-zinc-700 text-zinc-400 hover:text-zinc-200 transition-colors"
              title="Clear"
            >
              <X size={14} />
            </button>
          )}
        </div>
      </div>
    </div>
  );
}
