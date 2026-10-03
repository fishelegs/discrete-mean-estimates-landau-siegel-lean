#!/usr/bin/env python3
"""Verify all package file hashes, manifest coverage, and relative links."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
entries = manifest['files']
actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()}
expected = {row['path'] for row in entries} | {'MANIFEST.json', 'SHA256SUMS'}
if actual != expected:
    raise SystemExit('Manifest coverage mismatch: ' + repr(sorted(actual ^ expected)))
for row in entries:
    p = ROOT / row['path']
    if p.is_symlink() or p.resolve().is_relative_to(ROOT) is False:
        raise SystemExit('Invalid path in manifest: ' + row['path'])
    data = p.read_bytes()
    if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
        raise SystemExit('Hash or size mismatch: ' + row['path'])
checksum_paths = set()
for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
    digest, relative = line.split('  ', 1)
    if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != digest:
        raise SystemExit('Checksum mismatch: ' + relative)
    checksum_paths.add(relative)
if checksum_paths != actual - {'SHA256SUMS'}:
    raise SystemExit('SHA256SUMS coverage mismatch')
link_count = 0
for p in ROOT.rglob('*.md'):
    for target in re.findall(r'\]\(([^)]+)\)', p.read_text()):
        if '://' in target or target.startswith('#'):
            continue
        dest = (p.parent / target.split('#', 1)[0]).resolve()
        if not dest.is_relative_to(ROOT) or not dest.exists():
            raise SystemExit('Broken local link: ' + p.name + ' -> ' + target)
        link_count += 1
summary = json.loads((ROOT / 'results/check-summary.json').read_text())
if not summary['all_passed'] or len(summary['checks']) != 9:
    raise SystemExit('Missing successful nine-check run')
print('PASS: all file hashes and sizes, complete manifest, ' + str(link_count) +
      ' local links, and nine successful check records')
