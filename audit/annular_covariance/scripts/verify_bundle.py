#!/usr/bin/env python3
"""Verify all listed bytes, relative Markdown file links, and public path hygiene."""
from pathlib import Path
import hashlib
import re
from urllib.parse import unquote, urlsplit

root=Path(__file__).resolve().parents[1]
manifest=root/'SHA256SUMS'
lines=manifest.read_text().splitlines()
expected={}
for line in lines:
    h,name=line.split('  ',1)
    assert re.fullmatch('[0-9a-f]{64}',h), 'Malformed digest'
    p=Path(name)
    assert not p.is_absolute() and '..' not in p.parts, 'Nonportable manifest path'
    assert name not in expected, 'Duplicate manifest entry'
    expected[name]=h
actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p.name!='SHA256SUMS'}
assert actual==set(expected), 'Manifest does not cover exactly the bundle files'
for name,h in expected.items():
    p=root/name
    assert not p.is_symlink(), 'Symlink not allowed'
    assert hashlib.sha256(p.read_bytes()).hexdigest()==h, 'Hash mismatch: '+name
    text=p.read_text()
    assert not re.search(r'(?<![A-Za-z0-9])/(?:tmp|workspace|home|root)/',text), 'Private absolute path: '+name
    assert '__pycache__' not in p.parts
links=0
for doc in root.rglob('*.md'):
    for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)',doc.read_text()):
        u=urlsplit(target)
        if u.scheme or target.startswith('#'): continue
        path=(doc.parent/unquote(u.path)).resolve()
        assert path.is_relative_to(root) and path.is_file(), 'Broken relative link in '+doc.name+': '+target
        links+=1
print('PASS: complete SHA256 manifest ('+str(len(expected))+' files)')
print('PASS: relative Markdown file links ('+str(links)+' links)')
print('PASS: no private absolute paths, symlinks, or caches')
