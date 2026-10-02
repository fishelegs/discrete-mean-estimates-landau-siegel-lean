#!/usr/bin/env python3
"""Conservative lexical structure check for all Lean source files.

This is intentionally only a pre-kernel sanity check.  It ignores delimiters inside
line comments, nested block comments, and string literals, and checks (), [], {}.
It does not claim Lean parsing or type checking; `lake env lean` remains authoritative.
"""
from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

PAIRS = {')': '(', ']': '[', '}': '{'}
OPEN = set(PAIRS.values())
CLOSE = set(PAIRS)


def project_lean_files() -> list[Path]:
    """Return project sources without vendored Lake dependencies."""
    return sorted(
        path for path in ROOT.rglob('*.lean')
        if '.lake' not in path.parts and '.git' not in path.parts
    )


def check_file(path: Path) -> list[str]:
    text = path.read_text(encoding='utf-8')
    stack: list[tuple[str, int, int]] = []
    errors: list[str] = []
    i = 0
    line = 1
    col = 1
    block_depth = 0
    in_string = False

    lines = text.splitlines()
    for import_line, line_text in enumerate(lines, start=1):
        if line_text.startswith('import '):
            prefix = '\n'.join(lines[:import_line - 1])
            if '/-!' in prefix:
                errors.append(
                    f"{import_line}:1: import must precede the module doc comment"
                )
            break

    def advance(ch: str) -> None:
        nonlocal line, col
        if ch == '\n':
            line += 1
            col = 1
        else:
            col += 1

    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ''

        if block_depth:
            if ch == '/' and nxt == '-':
                block_depth += 1
                advance(ch); advance(nxt); i += 2
                continue
            if ch == '-' and nxt == '/':
                block_depth -= 1
                advance(ch); advance(nxt); i += 2
                continue
            advance(ch); i += 1
            continue

        if in_string:
            if ch == '\\':
                advance(ch); i += 1
                if i < len(text):
                    advance(text[i]); i += 1
                continue
            if ch == '"':
                in_string = False
            advance(ch); i += 1
            continue

        if ch == '-' and nxt == '-':
            # Skip to (but not including) newline.
            while i < len(text) and text[i] != '\n':
                advance(text[i]); i += 1
            continue
        if ch == '/' and nxt == '-':
            block_depth = 1
            advance(ch); advance(nxt); i += 2
            continue
        if ch == '"':
            in_string = True
            advance(ch); i += 1
            continue

        if ch in OPEN:
            stack.append((ch, line, col))
        elif ch in CLOSE:
            if not stack:
                errors.append(f"{line}:{col}: unmatched closing {ch}")
            else:
                opening, ol, oc = stack.pop()
                if opening != PAIRS[ch]:
                    errors.append(
                        f"{line}:{col}: closing {ch} mismatches {opening} opened at {ol}:{oc}"
                    )
        advance(ch); i += 1

    if block_depth:
        errors.append(f"EOF: unterminated block comment (depth {block_depth})")
    if in_string:
        errors.append("EOF: unterminated string literal")
    for opening, ol, oc in reversed(stack):
        errors.append(f"{ol}:{oc}: unmatched opening {opening}")
    return errors


def main() -> int:
    files = project_lean_files()
    failures = 0
    for path in files:
        errs = check_file(path)
        if errs:
            failures += 1
            rel = path.relative_to(ROOT)
            print(f"FAIL {rel}")
            for err in errs:
                print(f"  {err}")
    print(f"Lean source structure: {len(files)} files; failures={failures}")
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
