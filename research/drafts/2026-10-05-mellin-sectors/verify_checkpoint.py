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

# Actual Gaussian far-swap localization.
assert 405-395==10 and 2*405-2*400==10
assert 405+6-519==-108
assert Fraction(1,8)-Fraction(1,256)==Fraction(31,256)>Fraction(1,16)
assert Fraction(1,4)-Fraction(1,256)==Fraction(63,256)>Fraction(1,16)
assert 4-2*Fraction(23,2)==-19
assert 6+Fraction(1,2)*Fraction(23,2)==Fraction(47,4)<12
assert 1200+519*Fraction(23,2)==Fraction(14337,2)<7200
assert 38+4152+90+5==4285<5000
new=next(x for x in pins['proof_sources'] if x['id']=='swap_time_localization')
assert new['original_mathematical_source']['sha256']=='c9acb6bedae79ba02779f9cf456f13c9d6d55c9bed7a82255ab98c6e84f03e0b'
assert new['frozen_author_manifest_identity']['sha256']=='9568531f4f2272127f0c3cc5b1dc2271d22255711b45f6cc32bcce2fde4fbe30'
assert new['independent_review_identity']['sha256']=='17d87e01f0888709319e50c7985df22b22195362c0a6fe8ce104e3f0faa8f24d'
assert new['review_acceptance_record_identity']['sha256']=='046502ca617322abea5f7ec8266d70cc9e022a75770ee31e5ff0a881af02196a'
assert new['independent_review_manifest_identity']['sha256']=='e22428cf864d31a8893caf590c9b67b79fa689a97a7141d1f11e75752e1a711b'
assert new['final_acceptance_record_identity']['sha256']=='6354b25cc4a6cc832fc6a1a06fa74947701ab808fc377f50ee6a0ed7f7b1b3af'
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/swap_time_localization/checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/swap_time_localization/EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_WITH_SCOPE_LIMITS_NOT_LEAN'

# Actual Gaussian four integer-ratio diagonals.
assert 4*9+2*16==68 and 68-68==0
assert 4+Fraction(1,2)==Fraction(9,2)
assert 2*519==1038 and Fraction(959,15)<64
new=next(x for x in pins['proof_sources'] if x['id']=='four_branch_diagonals')
assert new['original_mathematical_source']['sha256']=='8b17bcfa77016cc0e823eb7b17c4bf6c72a55db3ceb1a0d08afe5b5ce836dfeb'
assert new['frozen_author_manifest_identity']['sha256']=='bacd93b3986f73dd08d260580a23013ec06ed605c6ccd6d978ccc4ea3364f435'
assert new['independent_review_identity']['sha256']=='85b68c4b3a23ff1d4a49b0897974b206d5a46bef5612b0c1054dba63d4aa672e'
assert new['review_acceptance_record_identity']['sha256']=='3f2e0148f063b4732a13e27a103a9dcf5204a3f40748ec05a447bd384c8078e3'
assert new['independent_review_manifest_identity']['sha256']=='70f5d473696c4578849925f238846e176053c7c3437a2cb3db18f3df5eb84eb8'
assert new['final_acceptance_record_identity']['sha256']=='1ddbb8725f257a6f3059ebc7d7e5a50453722021b14595aee7f9798cf8117e6a'
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/four_branch_diagonals/checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/four_branch_diagonals/EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_WITH_SCOPE_LIMITS_NOT_LEAN'

# Same-branch localization and conditional sufficient exponent transfer.
assert 1038-395==643
assert 1<Fraction(959,15)<64
for b in [Fraction(-1),Fraction(1),Fraction(63),Fraction(639,10)]:
    assert max(b,Fraction(1),Fraction(959,15))<64
new=next(x for x in pins['proof_sources'] if x['id']=='near_parity_sufficient_gate')
assert new['original_mathematical_source']['sha256']=='f8c98ad63360965080b85d6b43f69a8d2e7a6feffc440c7099aabb82cce115c6'
assert new['frozen_author_manifest_identity']['sha256']=='b105aee60c54cb730e8f43d805588f47e0ec8bd7db58edb3d22d4bdfcab589c4'
assert new['independent_review_identity']['sha256']=='76a304cc8bf7d39bf9c22fd17b0b64e7e97e5d00b5767e0b8263c2746ad5dab7'
assert new['review_acceptance_record_identity']['sha256']=='d5c2ebe6591e4846dc0af1989fc5011580e835fe13cb46782b75406bddcdb121'
assert new['final_acceptance_record_identity']['sha256']=='c3b456d9724a066d263ce5bfb70a4f6b1a68ca402ddc9640c05ab2abc5556e61'
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/near_parity_sufficient_gate/checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/near_parity_sufficient_gate/EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_SUFFICIENT_REDUCTION_ONLY_NOT_LEAN'
print(json.dumps({'integrity':'PASS','listed_files':len(manifest['files']),'exact_exponents':'PASS','analytic_or_Lean_certification':False},indent=2))
