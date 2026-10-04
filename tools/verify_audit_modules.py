#!/usr/bin/env python3
"""Kernel-check root audit/*.lean in dependency order, with private temporary objects.

Run through ``lake env python3 tools/verify_audit_modules.py`` after the project
build. Nested audit directories contain archived sources, not build targets.
Only ordinary dotted module names are supported in audit import headers; reject
other spellings rather than silently omitting a local dependency.
"""

import heapq
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def imports(source: Path) -> list[str]:
    """Read the import header, skipping nested block comments and line comments.

    Stop at the first body command, so strings and quoted syntax in inventories
    cannot create spurious dependencies. Lean still checks the complete source.
    """
    text = source.read_text(encoding="utf-8-sig")
    position = 0

    def token() -> str:
        nonlocal position
        while position < len(text):
            if text[position].isspace():
                position += 1
            elif text.startswith("--", position):
                end = text.find("\n", position)
                position = len(text) if end < 0 else end + 1
            elif text.startswith("/-", position):
                position += 2
                depth = 1
                while position < len(text) and depth:
                    if text.startswith("/-", position):
                        depth += 1
                        position += 2
                    elif text.startswith("-/", position):
                        depth -= 1
                        position += 2
                    else:
                        position += 1
                if depth:
                    raise ValueError(f"{source}: unterminated import-header comment")
            else:
                break
        start = position
        while position < len(text) and not text[position].isspace():
            if text.startswith(("--", "/-"), position):
                break
            position += 1
        return text[start:position]

    current = token()
    if current == "module":
        current = token()
    if current == "prelude":
        current = token()
    result = []
    while True:
        if current == "public":
            current = token()
        if current == "meta":
            current = token()
        if current != "import":
            return result
        name = token()
        if name == "all":
            name = token()
        if not MODULE_NAME.fullmatch(name):
            raise ValueError(f"{source}: unsupported import module {name!r}")
        result.append(name)
        current = token()
        # Lean 4.30 accepts one module per import. Diagnose a trailing local
        # module explicitly instead of mistaking it for the first body command.
        if current == "audit" or current.startswith("audit."):
            raise ValueError(f"{source}: each import must name exactly one module; "
                             f"unexpected trailing module {current}")


def audit_order(root: Path) -> list[Path]:
    """Resolve only immediate audit files; reject missing or nested local imports."""
    sources = {
        f"audit.{source.stem}": source
        for source in sorted((root / "audit").glob("*.lean"))
        if source.is_file() and not source.is_symlink()
    }
    dependencies = {}
    dependents: dict[str, list[str]] = {name: [] for name in sources}
    for name, source in sources.items():
        if not MODULE_NAME.fullmatch(name) or "." in source.stem:
            raise ValueError(f"unsupported root audit module filename: {source}")
        local = {item for item in imports(source)
                 if item == "audit" or item.startswith("audit.")}
        for dependency in sorted(local):
            if dependency not in sources:
                raise ValueError(
                    f"{source.relative_to(root)}: unknown local audit dependency "
                    f"{dependency}; only root audit/*.lean modules are allowed"
                )
            dependents[dependency].append(name)
        dependencies[name] = len(local)

    ready = [name for name, count in dependencies.items() if count == 0]
    heapq.heapify(ready)
    result = []
    while ready:
        name = heapq.heappop(ready)
        result.append(sources[name])
        for dependent in dependents[name]:
            dependencies[dependent] -= 1
            if dependencies[dependent] == 0:
                heapq.heappush(ready, dependent)
    if len(result) != len(sources):
        blocked = sorted(name for name, count in dependencies.items() if count)
        raise ValueError("audit import cycle blocks: " + ", ".join(blocked))
    return result


def verify(root: Path) -> int:
    # Validate the whole graph before compiling anything. Never add nested
    # semantic-review snapshots to the graph, even to satisfy an import.
    sources = audit_order(root)
    with tempfile.TemporaryDirectory(prefix="zhangls-audit-") as temporary:
        output = Path(temporary)
        (output / "audit").mkdir()
        environment = os.environ.copy()
        old_path = environment.get("LEAN_PATH", "")
        environment["LEAN_PATH"] = str(output) + (os.pathsep + old_path if old_path else "")
        for source in sources:
            relative = source.relative_to(root)
            print(f"Checking {relative}", flush=True)
            checked = subprocess.run(
                ["lean", "-R", str(root), "-o",
                 str((output / relative).with_suffix(".olean")), str(source)],
                cwd=root, env=environment,
            )
            if checked.returncode:
                print(f"ERROR: audit regression failed: {relative}", file=sys.stderr)
                return checked.returncode if checked.returncode > 0 else 1
    print(f"Audit kernel checks passed: {len(sources)} root modules", flush=True)
    return 0


def main() -> int:
    try:
        return verify(Path(__file__).resolve().parents[1])
    except (OSError, ValueError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
