import { useState } from 'react';
import { ChevronRight, RotateCcw, HelpCircle, Loader2, AlertTriangle } from 'lucide-react';
import {
  getAtPath,
  setAtPath,
  type OptionCatalogue,
  type OptionChoice,
  type OptionDescriptor,
  type OptionGroup,
  type OptionsObject,
} from '../lib/api';

/**
 * Renders entirely from `GET /api/options`. Controls come from
 * `catalogue.groups[].options[]` in wire order; a crate-side option
 * appears here with no component change.
 *
 * Structure is `path` + choice `value` (the serde tag). Never recover
 * identity by splitting a label or matching a title.
 */
interface OptionsPanelProps {
  /** null while the catalogue is still loading. */
  catalogue: OptionCatalogue | null;
  /** null until the catalogue has seeded it. */
  options: OptionsObject | null;
  onChange: (options: OptionsObject) => void;
  /** Non-null when the catalogue fetch failed. */
  loadError: string | null;
  onRetry: () => void;
}

function HelpHint({ hint }: { hint: string }) {
  return (
    <span
      className="inline-flex shrink-0 text-zinc-500 hover:text-zinc-300 cursor-help transition-colors"
      title={hint}
      aria-label="More info"
    >
      <HelpCircle size={12} />
    </span>
  );
}

/** Catalogue prose to tooltip text. "" entries are deliberate blank lines. */
function hintOf(detail: string[]): string | undefined {
  const text = detail.join('\n').trim();
  return text.length > 0 ? text : undefined;
}

function Toggle({
  path,
  label,
  description,
  hint,
  checked,
  onChange,
  size = 'normal',
}: {
  path: string;
  label: string;
  description?: string;
  hint?: string;
  checked: boolean;
  onChange: (checked: boolean) => void;
  size?: 'normal' | 'small';
}) {
  return (
    <label
      data-option-path={path}
      data-option-kind="toggle"
      className="flex items-center justify-between gap-3 cursor-pointer group"
    >
      <div className="flex flex-col min-w-0">
        <span
          className={`${size === 'small' ? 'text-xs' : 'text-sm'} text-zinc-200 group-hover:text-white transition-colors inline-flex items-center gap-1.5`}
        >
          {label}
          {hint && <HelpHint hint={hint} />}
        </span>
        {description && (
          <span className="text-[11px] text-zinc-500 leading-snug">{description}</span>
        )}
      </div>
      <button
        role="switch"
        aria-checked={checked}
        onClick={() => onChange(!checked)}
        className={`relative inline-flex h-5 w-9 shrink-0 cursor-pointer rounded-full border-2 border-transparent transition-colors ${
          checked ? 'bg-emerald-500' : 'bg-zinc-700'
        }`}
      >
        <span
          className={`pointer-events-none block h-4 w-4 rounded-full bg-white shadow-lg ring-0 transition-transform ${
            checked ? 'translate-x-4' : 'translate-x-0'
          }`}
        />
      </button>
    </label>
  );
}

/**
 * Selected `<option>` from the current value. A choice may write an
 * object, not a string: match that object by its payload key so this
 * file never names the choice or the key.
 */
function selectedValue(desc: OptionDescriptor, current: unknown): string {
  if (desc.kind.type !== 'choice') return '';
  if (current == null) return '';
  if (typeof current === 'string') return current;
  if (typeof current === 'object') {
    const match = desc.kind.choices.find(
      (c) =>
        c.payload != null &&
        Object.prototype.hasOwnProperty.call(current, c.payload.key)
    );
    return match ? match.value : '';
  }
  return '';
}

function valueForChoice(choice: OptionChoice): unknown {
  if (choice.payload == null) return choice.value;
  return { [choice.payload.key]: choice.payload.default };
}

function ChoiceControl({
  desc,
  options,
  onChange,
  size = 'normal',
}: {
  desc: OptionDescriptor;
  options: OptionsObject;
  onChange: (next: OptionsObject) => void;
  size?: 'normal' | 'small';
}) {
  if (desc.kind.type !== 'choice') return null;
  const kind = desc.kind;

  const current = getAtPath(options, desc.path);
  const selected = selectedValue(desc, current);
  const selectedChoice = kind.choices.find((c) => c.value === selected);
  const payload = selectedChoice?.payload ?? null;

  const countValue =
    payload != null &&
    current != null &&
    typeof current === 'object' &&
    typeof (current as Record<string, unknown>)[payload.key] === 'number'
      ? ((current as Record<string, unknown>)[payload.key] as number)
      : (payload?.default ?? 0);

  return (
    <label
      data-option-path={desc.path.join('.')}
      data-option-kind="choice"
      className="flex flex-col gap-1.5"
    >
      <span
        className={`${size === 'small' ? 'text-xs' : 'text-sm'} text-zinc-200 inline-flex items-center gap-1.5`}
      >
        {desc.label}
        {hintOf(desc.detail) && <HelpHint hint={hintOf(desc.detail)!} />}
      </span>
      {desc.summary && <span className="text-xs text-zinc-500">{desc.summary}</span>}
      <select
        value={selected}
        onChange={(e) => {
          const picked = e.target.value;
          if (picked === '') {
            onChange(setAtPath(options, desc.path, null));
            return;
          }
          // Recover the descriptor by identity — never by parsing text.
          const choice = kind.choices.find((c) => c.value === picked);
          if (!choice) return;
          onChange(setAtPath(options, desc.path, valueForChoice(choice)));
        }}
        className="w-full px-2.5 py-1.5 bg-zinc-800 border border-zinc-700 rounded-md text-sm text-zinc-200 focus:outline-none focus:ring-2 focus:ring-emerald-500/50"
      >
        {kind.unset !== null && <option value="">{kind.unset}</option>}
        {kind.choices.map((c) => (
          <option key={c.value} value={c.value}>
            {c.label}
          </option>
        ))}
      </select>
      {selectedChoice?.summary && (
        <span className="text-[11px] text-zinc-500 leading-snug">
          {selectedChoice.summary}
        </span>
      )}
      {payload != null && (
        <span className="flex items-center gap-2 mt-1">
          <span className="text-xs text-zinc-400 whitespace-nowrap">
            {payload.key.replace(/_/g, ' ')}:
          </span>
          <input
            type="number"
            min={payload.min}
            value={countValue}
            onChange={(e) =>
              onChange(
                setAtPath(options, desc.path, {
                  [payload.key]: Math.max(
                    payload.min,
                    parseInt(e.target.value, 10) || 0
                  ),
                })
              )
            }
            className="w-20 px-2 py-1 bg-zinc-800 border border-zinc-700 rounded-md text-sm text-zinc-200 focus:outline-none focus:ring-2 focus:ring-emerald-500/50"
          />
        </span>
      )}
    </label>
  );
}

function Control({
  desc,
  options,
  onChange,
  size,
}: {
  desc: OptionDescriptor;
  options: OptionsObject;
  onChange: (next: OptionsObject) => void;
  size: 'normal' | 'small';
}) {
  if (desc.kind.type === 'toggle') {
    return (
      <Toggle
        size={size}
        path={desc.path.join('.')}
        label={desc.label}
        description={desc.summary}
        hint={hintOf(desc.detail)}
        checked={getAtPath(options, desc.path) === true}
        onChange={(v) => onChange(setAtPath(options, desc.path, v))}
      />
    );
  }
  if (desc.kind.type === 'choice') {
    return (
      <ChoiceControl desc={desc} options={options} onChange={onChange} size={size} />
    );
  }
  // TS calls this unreachable; `kind.type` is whatever the server sent.
  // A newer crate kind must render as a named gap, not vanish.
  return (
    <UnsupportedControl desc={desc} />
  );
}

function UnsupportedControl({ desc }: { desc: OptionDescriptor }) {
  return (
    <div
      data-option-path={desc.path.join('.')}
      data-option-kind="unsupported"
      className="flex flex-col gap-0.5 px-2 py-1.5 rounded-md bg-amber-500/10 border border-amber-500/20"
    >
      <span className="text-xs text-amber-300 inline-flex items-center gap-1.5">
        <AlertTriangle size={12} />
        {desc.label}
      </span>
      <span className="text-[11px] text-amber-200/70 leading-snug">
        This build can't render a “{desc.kind.type}” control. Set{' '}
        <code>{desc.path.join('.')}</code> another way, or update the UI.
      </span>
    </div>
  );
}

/**
 * A group whose members are backed by one object: collapsible, with a
 * tri-state master switch. Membership comes from the catalogue, so the
 * master can never disagree with what the group renders.
 *
 * The master folds over the group's OWN member paths. It deliberately
 * does NOT write a locally-built all-on object at `masterPath` — that
 * would be a second list of exactly the kind this panel exists to
 * delete. Only toggles participate: writing a boolean at a future
 * choice-valued member would be wrong.
 */
function MasteredGroup({
  group,
  options,
  onChange,
}: {
  group: OptionGroup;
  options: OptionsObject;
  onChange: (next: OptionsObject) => void;
}) {
  const [open, setOpen] = useState(false);

  const toggles = group.options.filter((o) => o.kind.type === 'toggle');
  const all = toggles.length > 0 && toggles.every((o) => getAtPath(options, o.path) === true);
  const any = toggles.some((o) => getAtPath(options, o.path) === true);

  const setMaster = (v: boolean) => {
    onChange(toggles.reduce((acc, o) => setAtPath(acc, o.path, v), options));
  };

  const stateLabel = all ? 'all on' : any ? 'partial' : 'all off';
  const groupHint = hintOf(group.detail);

  return (
    <div data-option-group={group.id} className="bg-zinc-900/50 rounded-lg border border-zinc-800">
      <div className="flex items-center justify-between gap-3 p-2.5">
        <button
          onClick={() => setOpen(!open)}
          className="flex items-center gap-1.5 text-left min-w-0 flex-1 group"
        >
          <ChevronRight
            size={14}
            className={`text-zinc-500 transition-transform ${open ? 'rotate-90' : ''}`}
          />
          <div className="flex flex-col min-w-0">
            <span className="text-sm font-medium text-zinc-200 group-hover:text-white transition-colors inline-flex items-center gap-1.5">
              {group.title}
              {groupHint && <HelpHint hint={groupHint} />}
            </span>
            <span className="text-[11px] text-zinc-500">
              {group.summary} · {stateLabel}
            </span>
          </div>
        </button>
        <button
          role="switch"
          data-group-master={group.id}
          aria-checked={all}
          onClick={() => setMaster(!all)}
          className={`relative inline-flex h-5 w-9 shrink-0 cursor-pointer rounded-full border-2 border-transparent transition-colors ${
            all ? 'bg-emerald-500' : any ? 'bg-amber-600' : 'bg-zinc-700'
          }`}
          title={
            all
              ? 'Click to disable all'
              : any
                ? 'Partial — click to enable all'
                : 'Click to enable all'
          }
        >
          <span
            className={`pointer-events-none block h-4 w-4 rounded-full bg-white shadow-lg ring-0 transition-transform ${
              all ? 'translate-x-4' : 'translate-x-0'
            }`}
          />
        </button>
      </div>

      {/* CSS-hidden, not unmounted: find-in-page still reaches collapsed options. */}
      <div
        className={
          open
            ? 'flex flex-col gap-2 px-3 pb-3 pt-1 border-t border-zinc-800/60'
            : 'hidden'
        }
      >
        {group.options.map((desc) => (
          <Control
            key={desc.path.join('.')}
            desc={desc}
            options={options}
            onChange={onChange}
            size="small"
          />
        ))}
      </div>
    </div>
  );
}

function PlainGroup({
  group,
  options,
  onChange,
}: {
  group: OptionGroup;
  options: OptionsObject;
  onChange: (next: OptionsObject) => void;
}) {
  const groupHint = hintOf(group.detail);
  return (
    <div
      data-option-group={group.id}
      className="flex flex-col gap-2.5 p-3 bg-zinc-900/50 rounded-lg border border-zinc-800"
    >
      <div className="flex flex-col min-w-0 border-b border-zinc-800 pb-2">
        <span className="text-sm font-medium text-zinc-200 inline-flex items-center gap-1.5">
          {group.title}
          {groupHint && <HelpHint hint={groupHint} />}
        </span>
        {group.summary && (
          <span className="text-[11px] text-zinc-500 leading-snug">{group.summary}</span>
        )}
      </div>
      {group.options.map((desc) => (
        <Control
          key={desc.path.join('.')}
          desc={desc}
          options={options}
          onChange={onChange}
          size="normal"
        />
      ))}
    </div>
  );
}

export function OptionsPanel({
  catalogue,
  options,
  onChange,
  loadError,
  onRetry,
}: OptionsPanelProps) {
  // Empty panel reads as "no options", not "server unreachable".
  if (loadError !== null) {
    return (
      <div className="flex flex-col gap-2">
        <span className="text-sm font-medium text-zinc-300">Options</span>
        <div className="flex flex-col gap-2 px-3 py-3 rounded-lg bg-amber-500/10 border border-amber-500/20">
          <span className="inline-flex items-center gap-1.5 text-sm text-amber-300">
            <AlertTriangle size={14} />
            Options unavailable
          </span>
          <span className="text-[11px] text-amber-200/70 leading-snug">
            {loadError}
          </span>
          <span className="text-[11px] text-zinc-400 leading-snug">
            Decompiling still works — the server applies its own defaults when no
            options are sent.
          </span>
          <button
            onClick={onRetry}
            className="self-start mt-1 flex items-center gap-1 text-xs text-zinc-300 hover:text-white transition-colors"
          >
            <RotateCcw size={12} />
            Retry
          </button>
        </div>
      </div>
    );
  }

  // `== null`: missing `defaults` seeds `undefined`, and `=== null`
  // would show a header + Reset over zero controls. Second lock after
  // `fetchOptions` rejecting that shape.
  if (catalogue == null || options == null) {
    return (
      <div className="flex flex-col gap-2">
        <span className="text-sm font-medium text-zinc-300">Options</span>
        <div className="flex items-center gap-2 px-3 py-3 rounded-lg bg-zinc-900/50 border border-zinc-800">
          <Loader2 size={14} className="animate-spin text-zinc-500" />
          <span className="text-xs text-zinc-500">Loading options…</span>
        </div>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-3">
      <div className="flex items-center justify-between">
        <span className="text-sm font-medium text-zinc-300">Options</span>
        <button
          onClick={() => onChange(structuredClone(catalogue.defaults))}
          className="flex items-center gap-1 text-xs text-zinc-500 hover:text-zinc-300 transition-colors"
          title="Reset to defaults"
        >
          <RotateCcw size={12} />
          Reset
        </button>
      </div>

      {catalogue.groups.map((group) =>
        group.masterPath === null ? (
          <PlainGroup
            key={group.id}
            group={group}
            options={options}
            onChange={onChange}
          />
        ) : (
          <MasteredGroup
            key={group.id}
            group={group}
            options={options}
            onChange={onChange}
          />
        )
      )}
    </div>
  );
}
