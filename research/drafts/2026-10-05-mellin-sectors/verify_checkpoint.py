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

# Conditional carrier interface: exact costs and frozen source identities only.
assert 519-400==119 and 400+6-519==-113
assert 519+405-400==524 and 2*400-395==405
assert Fraction(1,8*16)-Fraction(1,256)==Fraction(1,256)
for b in [Fraction(-1),Fraction(1),Fraction(63),Fraction(639,10)]:
    assert (b-119)+119==b<64
new=next(x for x in pins['proof_sources'] if x['id']=='shifted_correlation_carrier_interface')
assert new['original_mathematical_source']['sha256']=='ea944e132241381d560e2e53ff55ec04459eafbd602e4d209ac3225684020683'
assert new['frozen_author_manifest_identity']['sha256']=='1fdd72f21a2bf49e9907f36b9916ed2abbd945450cb8981ee10de77da1b9764c'
assert new['independent_review_identity']['sha256']=='1d0cb528c4ee7ebc5f4aca1f8c71e43f63f9a7daa66ce346f5fa7d56e7845d35'
assert new['independent_review_manifest_identity']['sha256']=='b890e7bb0d2cea34a76db4882825891e8dbc7f4f025f7bed9141b43cca58517b'
assert new['final_acceptance_record_identity']['sha256']=='6a7de9de737d5b2366c9bd5a61a35690d7ea3518de0ab480ce3cf02ef62c14ef'
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/shifted_correlation_carrier_interface/checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/shifted_correlation_carrier_interface/EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_CONDITIONAL_CARRIER_INTERFACE_ONLY_NOT_LEAN'
assert manifest['global_frontier']['actual_shifted_arithmetic_density']=='UNPROVED'
assert manifest['global_frontier']['actual_shifted_density_coefficient_budget']=='UNPROVED'
assert manifest['global_frontier']['actual_weighted_cumulative_remainder_bound']=='UNPROVED'
assert manifest['global_frontier']['near_aggregate_one_sided_upper_bound']=='UNPROVED'

# Bounded failed-direct-attachment audit; no actual arithmetic estimate.
assert 2*519-400+16*9==782 and 782+2==784
assert Fraction(2,4)+4==Fraction(9,2)
assert 1038-400==638 and 638+519==1157 and 2*1157-1038==1276
assert Fraction(2,3)*2+1==Fraction(7,3)
assert Fraction(2,3)*Fraction(9,2)==3 and Fraction(2,3)*1038==692
assert Fraction(1,2)*Fraction(9,2)==Fraction(9,4)
new=next(x for x in pins['proof_sources'] if x['id']=='primary_shifted_attachment_audit')
assert new['original_mathematical_source']['sha256']=='e92b07045452d1bd4d66a45719f2b44516747bde9963f2ffd097c2922d2670ee'
assert new['frozen_author_manifest_identity']['sha256']=='752965e1116292f3a9d7b2ab399918d16fad81a520623535fa56f33b508b46ed'
assert new['essential_positive_component_scope_addendum_identity']['sha256']=='facda806071837a4f285c0fbcc5f935804221c5ff8f8cf0de852c53716af3a1d'
assert new['scope_addendum_manifest_identity']['sha256']=='051a8c0fa66478f381f776575ef2b4f1c111e8e38c17903fb8daf9a59e61ad6e'
assert new['independent_review_identity']['sha256']=='bffb45eb65a664cbe664e075ca500c99b31cb0d139a274e9c971d55e925bcf3c'
assert new['independent_review_manifest_identity']['sha256']=='8acd52f1a441e1b9074815086550d55154edc72bea710c57dfcd7b9d8db98bfd'
assert new['final_acceptance_record_identity']['sha256']=='8255c16f9d8b3af15dac8d3229917aeac836c7c9b7bbc921d86f3247184aecaa'
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/primary_shifted_attachment_audit/checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/primary_shifted_attachment_audit/EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_FAILED_DIRECT_ATTACHMENTS_WITH_POSITIVE_COMPONENT_SCOPE_ONLY_NOT_LEAN'
assert manifest['global_frontier']['MRT_Section5_prime_divisor_accounting']=='POSITIVE_DIFFERENCE_COMPONENT_ONLY_p_DIVIDES_ell_MINUS_k'
assert manifest['global_frontier']['reflected_arithmetic_interface']=='UNPROVED_SEPARATE_p_DIVIDES_k_PLUS_ell'
print(json.dumps({'integrity':'PASS','listed_files':len(manifest['files']),'exact_exponents':'PASS','analytic_or_Lean_certification':False},indent=2))
