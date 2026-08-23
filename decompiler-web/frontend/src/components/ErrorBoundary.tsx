import { Component, type ErrorInfo, type ReactNode } from 'react';

/**
 * Last-resort render guard. An uncaught render error otherwise unmounts
 * the React root to a blank page. The options panel's stated-error path
 * covers expected catalogue failures; this catches the unexpected ones.
 */
interface Props {
  children: ReactNode;
}

interface State {
  error: Error | null;
}

export class ErrorBoundary extends Component<Props, State> {
  state: State = { error: null };

  static getDerivedStateFromError(error: Error): State {
    return { error };
  }

  componentDidCatch(error: Error, info: ErrorInfo) {
    console.error('Unhandled render error:', error, info.componentStack);
  }

  render() {
    const { error } = this.state;
    if (error === null) return this.props.children;

    return (
      <div className="h-screen flex items-center justify-center p-6 bg-zinc-950">
        <div className="max-w-lg flex flex-col gap-3 px-5 py-4 rounded-lg bg-red-500/10 border border-red-500/20">
          <span className="text-sm font-medium text-red-300">
            Something went wrong
          </span>
          <span className="text-xs text-red-200/80 leading-snug break-words">
            {error.message || String(error)}
          </span>
          <button
            onClick={() => this.setState({ error: null })}
            className="self-start px-3 py-1.5 rounded-md text-xs font-medium bg-zinc-800 text-zinc-200 hover:bg-zinc-700 transition-colors"
          >
            Try again
          </button>
        </div>
      </div>
    );
  }
}
