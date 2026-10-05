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
# Fixed-profile smooth-target bounds and exact exponent budgets.
assert Fraction(1,2)+Fraction(1,37)-Fraction(1,37)==Fraction(1,2)
assert 4+Fraction(1,2)-5==-Fraction(1,2)
assert 5-12==-7
assert 2076*12+324-400==24836
assert (24836-76)//2==12380
assert 3-2*12==-21 and 9*12==108
assert 12+24*9==228
assert -Fraction(1,2)+Fraction(1,4)==-Fraction(1,4)
# Existing proof documents retain their precise earlier publication bytes.
for name,sha in manifest['preserved_proof_document_hashes'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==sha,name
pins=json.loads((root/'SOURCE_PINS.json').read_text())
new=next(x for x in pins['proof_sources'] if x['id']=='smooth_balanced_diagonal')
assert new['original_mathematical_source']['sha256']=='c1d3d2dcfcb63d9a64d7b58964553468241589910bb95d6a49a9bae00c89ef74'
assert new['frozen_author_manifest_identity']['sha256']=='dc79ca254e3a19e6a309558c2a589d7d58f07c184ed7eeaacf09766ee937a065'
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/smooth_balanced_diagonal/checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/smooth_balanced_diagonal/EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_WITH_SCOPE_LIMITS_NOT_LEAN'
assert new['independent_review_identity']['sha256']=='6c38ba4d36b11f2d90ff33cde06348051ca287b0515f00d0dda3a95b7c4a619c'
assert new['review_acceptance_record_identity']['sha256']=='d3556eae84917185fb3f3448c370679c9b537b7288b5d9ba239a31a5710e6793'
assert new['independent_review_manifest_identity']['sha256']=='9531dad501111667c39b525a3c737650174b93a30c33ef75af1c44aa1bd6ad2a'
assert new['final_acceptance_record_identity']['sha256']=='e2b6b3b6bbda7a4aa6b75b1ad3c7886ba248574a4774d8b8997fa90d2c65ad2a'
# Gaussian principal contour and support reserve exponent checks.
assert -8+Fraction(1,2)+6==-Fraction(3,2)
assert 13-14+Fraction(1,2)==-Fraction(1,2)
assert -8-14+1==-21
assert Fraction(1,2)-Fraction(1,4)==Fraction(1,4)
assert 1+7*9+12*519==6292<6400
assert 2*6==12 and 2*6400==12800
new=next(x for x in pins['proof_sources'] if x['id']=='gaussian_principal_mean')
assert new['original_mathematical_source']['sha256']=='3a9df5d600c48111952bc66903d9df749d78ae3595cb5e72dbe17130628f441c'
assert new['frozen_author_manifest_identity']['sha256']=='dc8060539d5c576f9affe3cae20fc123cf089304b744ee7ca2c78d1354d816e6'
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/gaussian_principal_mean/checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/gaussian_principal_mean/EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_WITH_SCOPE_LIMITS_NOT_LEAN'
assert new['independent_review_identity']['sha256']=='d6ef27e3a740b67adc61ae5d74ffb238fbcd9091bf23cd5de82a2d2b51a26c82'
assert new['review_acceptance_record_identity']['sha256']=='7898c245f842db53392f6f30d6353d1f1d45e3dbe1ca85fd98887af27b91b216'
assert new['independent_review_manifest_identity']['sha256']=='d084548d4555388f7e0266db5292d982d55acd2e9bfe26d66775056871ed67a9'
assert new['final_acceptance_record_identity']['sha256']=='4a4488fc3f1ca99b0bce692eb350094cbcdb92f04fe940261bddeea809dc606d'
print(json.dumps({'integrity':'PASS','listed_files':len(manifest['files']),'exact_exponents':'PASS','analytic_or_Lean_certification':False},indent=2))
