#!/usr/bin/env python3
"""Static audit for common proof-surrogate patterns in the ZhangLS Lean tree.

Findings are review candidates, not a proof that a theorem is mathematically wrong.
The scanner removes comments and string literals before matching so policy words in
comments do not become false positives.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "ZhangLS"

PATTERNS = [
    ("sorry/admit", re.compile(r"\b(sorry|admit)\b"), "HIGH"),
    ("direct exact hypothesis", re.compile(r"^\s*exact\s+h[_A-Za-z0-9']*\s*$", re.M), "HIGH"),
    ("arbitrary residual", re.compile(r"\buse\s*\([^\n]*-\s*[^\n]*\)"), "HIGH"),
]


def mask_noncode(src: str) -> str:
    """Replace Lean comments and strings by spaces while preserving newlines."""
    out = list(src)
    i, n, depth = 0, len(src), 0
    in_string = False
    while i < n:
        if depth:
            if src.startswith('/-', i):
                out[i:i+2] = '  '
                depth += 1
                i += 2
            elif src.startswith('-/', i):
                out[i:i+2] = '  '
                depth -= 1
                i += 2
            else:
                if src[i] != '\n': out[i] = ' '
                i += 1
        elif in_string:
            if src[i] == '\\' and i + 1 < n:
                if src[i] != '\n': out[i] = ' '
                if src[i+1] != '\n': out[i+1] = ' '
                i += 2
            elif src[i] == '"':
                out[i] = ' '
                in_string = False
                i += 1
            else:
                if src[i] != '\n': out[i] = ' '
                i += 1
        elif src.startswith('/-', i):
            out[i:i+2] = '  '
            depth = 1
            i += 2
        elif src.startswith('--', i):
            j = src.find('\n', i)
            if j < 0: j = n
            for k in range(i, j): out[k] = ' '
            i = j
        elif src[i] == '"':
            out[i] = ' '
            in_string = True
            i += 1
        else:
            i += 1
    return ''.join(out)


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def scan_file(path: pathlib.Path):
    raw = path.read_text(encoding="utf-8", errors="replace")
    code = mask_noncode(raw)
    for name, rx, severity in PATTERNS:
        for m in rx.finditer(code):
            line = line_of(code, m.start())
            excerpt = raw.splitlines()[line - 1].strip()[:140]
            yield severity, name, line, excerpt

    # Trusted SPEC policy: no theorem-level Float at all.
    if path.is_relative_to(LEAN_ROOT / "Spec") and re.search(r"\bFloat\b", code):
        for m in re.finditer(r"\bFloat\b", code):
            line = line_of(code, m.start())
            yield "HIGH", "Float in trusted SPEC", line, raw.splitlines()[line - 1].strip()[:140]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true")
    args = ap.parse_args()

    findings = []
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        for finding in scan_file(path):
            findings.append((path.relative_to(ROOT),) + finding)

    high = 0
    for path, severity, name, line, excerpt in findings:
        if severity == "HIGH": high += 1
        print(f"{severity:6} {path}:{line}: {name}: {excerpt}")

    print(f"\n{len(findings)} findings; {high} high-risk review candidates")
    return 1 if args.strict and high else 0


if __name__ == "__main__":
    sys.exit(main())
