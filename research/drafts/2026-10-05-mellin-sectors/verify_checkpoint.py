#!/usr/bin/env python3
"""Read-only checkpoint integrity and exact exponent diagnostics."""
from pathlib import Path
from fractions import Fraction
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/'PUBLICATION_MANIFEST.json').read_text())
for entry in manifest['files']:
    p=root/entry['path']
    assert p.is_file(), entry['path']
    b=p.read_bytes()
    assert len(b)==entry['bytes'], entry['path']
    assert hashlib.sha256(b).hexdigest()==entry['sha256'], entry['path']
actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
expected={entry['path'] for entry in manifest['files']}|{'PUBLICATION_MANIFEST.json'}
assert actual==expected,(actual-expected,expected-actual)
assert Fraction(928,15)+2==Fraction(958,15)
assert Fraction(958,15)+Fraction(1,15)==Fraction(959,15)<64
assert Fraction(32,5)+2==Fraction(42,5)
assert Fraction(32,5)+4==Fraction(52,5)
assert 5+14==19 and 5+8==13
assert -2022+2+9==-2011 and -2022+2+1==-2019
assert -Fraction(2019,2)+8+288==-Fraction(1427,2)
assert (52-Fraction(1427,2))/2==-Fraction(1323,4)
assert 730-400-Fraction(1323,4)==-Fraction(3,4)
assert 1113-400-Fraction(1427,2)==-Fraction(1,2)
print(json.dumps({'integrity':'PASS','listed_files':len(manifest['files']),'exact_exponents':'PASS','analytic_or_Lean_certification':False},indent=2))
