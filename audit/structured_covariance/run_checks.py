#!/usr/bin/env python3
"""Portable integrity and finite-check runner. No downloads or file writes."""
from pathlib import Path
from urllib.parse import unquote, urlsplit
import argparse
import hashlib
import importlib.metadata
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def verify_bundle():
    manifest = ROOT / "SHA256SUMS"
    entries = {}
    for line in manifest.read_text(encoding="utf-8").splitlines():
        digest, name = line.split("  ", 1)
        assert re.fullmatch(r"[0-9a-f]{64}", digest), "Invalid digest"
        relative = Path(name)
        assert not relative.is_absolute() and ".." not in relative.parts
        assert name not in entries, "Duplicate manifest entry"
        target = ROOT / relative
        assert target.is_file() and not target.is_symlink(), f"Missing regular file: {name}"
        assert hashlib.sha256(target.read_bytes()).hexdigest() == digest, f"Hash mismatch: {name}"
        entries[name] = digest
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*") if p.is_file()}
    assert actual == set(entries) | {"SHA256SUMS"}, "Manifest inventory mismatch"
    for path in ROOT.rglob("*.md"):
        content = path.read_text(encoding="utf-8")
        for destination in re.findall(r"\[[^\]]+\]\(([^)]+)\)", content):
            parsed = urlsplit(destination)
            if parsed.scheme:
                assert parsed.scheme == "https", "Unexpected link scheme"
                continue
            target = (path.parent / unquote(parsed.path)).resolve()
            assert target.is_relative_to(ROOT), "Link leaves bundle"
            assert target.is_file(), f"Broken local link in {path.name}"
            assert not parsed.fragment, "Local fragments require a separate anchor check"
    # Match machine locations without placing literal locations in this package.
    forbidden = re.compile(r"/(?:tm[p]|workspac[e]|roo[t]|hom[e])/")
    for path in ROOT.rglob("*"):
        if path.is_file():
            assert not forbidden.search(path.read_text(encoding="utf-8")), f"Machine-specific reference: {path.name}"
    print("Bundle hashes, inventory, local links, and portable references verified")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    verify_bundle()
    if args.verify_only:
        return
    assert sys.version_info >= (3, 9), "Python 3.9 or later is required"
    for package, expected in [("mpmath", "1.3.0"), ("sympy", "1.14.0")]:
        found = importlib.metadata.version(package)
        assert found == expected, f"Use pinned {package} version {expected}; found {found}"
    print("Required mpmath and SymPy versions verified")
    for script, result in [("check_algebra.py", "algebra.txt"), ("check_independent.py", "independent.txt")]:
        completed = subprocess.run(
            [sys.executable, str(ROOT / "checks" / script)],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        assert completed.returncode == 0, f"{script} failed: {completed.stderr}"
        assert not completed.stderr, f"Unexpected stderr from {script}"
        expected = (ROOT / "results" / result).read_text(encoding="utf-8")
        assert completed.stdout == expected, f"Saved output differs for {script}"
        print(f"PASS {script}: output exactly matches results/{result}")
    print("ALL CHECKS PASSED. Finite checks are not an analytic or Lean proof.")

if __name__ == "__main__":
    main()
