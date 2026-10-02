#!/usr/bin/env python3
from pathlib import Path
import re, sys

ROOT = Path(__file__).resolve().parents[1]
TOKEN = re.compile(r'\b(sorry|admit)\b')

def project_lean_files() -> list[Path]:
    """Return project sources without vendored Lake dependencies."""
    return sorted(
        path for path in ROOT.rglob('*.lean')
        if '.lake' not in path.parts and '.git' not in path.parts
    )

FILES = project_lean_files()

def strip_noncode(s: str) -> str:
    out = []
    i = 0
    block = 0
    in_string = False
    esc = False
    while i < len(s):
        if block:
            if s.startswith('/-', i):
                block += 1; out.extend('  '); i += 2
            elif s.startswith('-/', i):
                block -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if s[i] == '\n' else ' '); i += 1
            continue
        if in_string:
            c = s[i]
            out.append('\n' if c == '\n' else ' ')
            if esc:
                esc = False
            elif c == '\\':
                esc = True
            elif c == '"':
                in_string = False
            i += 1
            continue
        if s.startswith('--', i):
            j = s.find('\n', i)
            if j < 0:
                out.extend(' ' * (len(s) - i)); break
            out.extend(' ' * (j - i)); out.append('\n'); i = j + 1
        elif s.startswith('/-', i):
            block = 1; out.extend('  '); i += 2
        elif s[i] == '"':
            in_string = True; out.append(' '); i += 1
        else:
            out.append(s[i]); i += 1
    return ''.join(out)

bad = []
for path in FILES:
    text = path.read_text(encoding='utf-8')
    code = strip_noncode(text)
    for m in TOKEN.finditer(code):
        line = code.count('\n', 0, m.start()) + 1
        bad.append((path.relative_to(ROOT), line, m.group(1)))

if bad:
    for p, line, tok in bad:
        print(f'{p}:{line}: forbidden placeholder `{tok}`', file=sys.stderr)
    raise SystemExit(1)
print(f'placeholder check OK: {len(FILES)} Lean files, no code-level sorry/admit')
