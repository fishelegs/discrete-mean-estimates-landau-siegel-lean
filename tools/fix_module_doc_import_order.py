#!/usr/bin/env python3
"""Move an initial Lean module doc comment below the import block."""
from __future__ import annotations

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def project_lean_files() -> list[Path]:
    return sorted(
        path for path in ROOT.rglob('*.lean')
        if '.lake' not in path.parts and '.git' not in path.parts
    )


def initial_module_doc_end(text: str, start: int) -> int | None:
    depth = 0
    index = start
    while index + 1 < len(text):
        pair = text[index:index + 2]
        if pair == '/-':
            depth += 1
            index += 2
            continue
        if pair == '-/':
            depth -= 1
            index += 2
            if depth == 0:
                return index
            continue
        index += 1
    return None


def repaired_text(text: str) -> str | None:
    start = len(text) - len(text.lstrip('\ufeff \t\r\n'))
    if not text.startswith('/-!', start):
        return None
    end = initial_module_doc_end(text, start)
    if end is None:
        return None

    after_lines = text[end:].splitlines(keepends=True)
    index = 0
    while index < len(after_lines) and not after_lines[index].strip():
        index += 1
    import_start = index
    while index < len(after_lines) and after_lines[index].startswith('import '):
        index += 1
    if index == import_start:
        return None

    imports = ''.join(after_lines[import_start:index]).rstrip('\r\n')
    module_doc = text[start:end]
    remainder = ''.join(after_lines[index:]).lstrip('\r\n')
    leading = text[:start]
    return f"{leading}{imports}\n\n{module_doc}\n\n{remainder}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--write', action='store_true',
        help='rewrite files; otherwise only report files needing migration',
    )
    args = parser.parse_args()

    pending: list[Path] = []
    for path in project_lean_files():
        text = path.read_text(encoding='utf-8')
        repaired = repaired_text(text)
        if repaired is None or repaired == text:
            continue
        pending.append(path)
        if args.write:
            path.write_text(repaired, encoding='utf-8')

    action = 'repaired' if args.write else 'need repair'
    for path in pending:
        print(f"{path.relative_to(ROOT)}: {action}")
    print(f"module-doc import-order files: {len(pending)}")
    return 0 if args.write or not pending else 1


if __name__ == '__main__':
    raise SystemExit(main())
