import type { languages, editor } from 'monaco-editor';

export const dehoskLanguage: languages.IMonarchLanguage = {
  keywords: [
    'fn', 'let', 'when', 'is', 'if', 'else', 'expect', 'rec', 'trace',
    'delay', 'force', 'seq', 'fail', 'and', 'or',
  ],
  constructors: [
    'True', 'False', 'Some', 'None',
    'Minting', 'Spending', 'Rewarding', 'Certifying', 'Voting', 'Proposing',
    'VerificationKey', 'Script',
    'NoDatum', 'DatumHash', 'InlineDatum',
    'NegativeInfinity', 'Finite', 'PositiveInfinity',
  ],
  tokenizer: {
    root: [
      // Hex byte arrays: #"..."
      [/#"[0-9a-fA-F]*"/, 'string.hex'],
      // Byte-string literals: @"..."
      [/@"/, 'string', '@string_at'],
      // Regular strings
      [/"/, 'string', '@string_dq'],
      // Constructors: Constr<N> or named
      [/Constr<\d+>/, 'type.constructor'],
      [/[A-Z]\w*/, {
        cases: {
          '@constructors': 'type.constructor',
          '@default': 'type',
        },
      }],
      // Builtin calls
      [/Data\.\w+/, 'support.function'],
      [/List\.\w+/, 'support.function'],
      [/Pair\.\w+/, 'support.function'],
      [/[a-z_]\w*/, {
        cases: {
          '@keywords': 'keyword',
          '@default': 'identifier',
        },
      }],
      [/-?\d+/, 'number'],
      // Field access
      [/\.fields/, 'keyword.operator'],
      [/\.tag/, 'keyword.operator'],
      [/[=!<>]=?/, 'operator'],
      [/[&|]{2}/, 'operator'],
      [/[+\-*/%]/, 'operator'],
      [/\?/, 'operator'],
      [/->/, 'operator'],
      [/\.\./, 'operator'],
      [/[{}()\[\]]/, 'bracket'],
      [/\/\/.*$/, 'comment'],
      [/\s+/, 'white'],
    ],
    string_at: [
      [/[^"]+/, 'string'],
      [/"/, 'string', '@pop'],
    ],
    string_dq: [
      [/[^"\\]+/, 'string'],
      [/\\./, 'string.escape'],
      [/"/, 'string', '@pop'],
    ],
  },
};

export const dehoskTheme: editor.IStandaloneThemeData = {
  base: 'vs-dark',
  inherit: true,
  rules: [
    { token: 'keyword', foreground: 'c586c0' },
    { token: 'type', foreground: '4ec9b0' },
    { token: 'type.constructor', foreground: '4ec9b0', fontStyle: 'bold' },
    { token: 'support.function', foreground: 'dcdcaa' },
    { token: 'string', foreground: 'ce9178' },
    { token: 'string.hex', foreground: 'd7ba7d' },
    { token: 'number', foreground: 'b5cea8' },
    { token: 'operator', foreground: 'd4d4d4' },
    { token: 'identifier', foreground: '9cdcfe' },
    { token: 'comment', foreground: '6a9955' },
    { token: 'bracket', foreground: 'ffd700' },
    { token: 'keyword.operator', foreground: '569cd6' },
  ],
  colors: {
    'editor.background': '#0a0a0a',
    'editor.foreground': '#d4d4d4',
  },
};
