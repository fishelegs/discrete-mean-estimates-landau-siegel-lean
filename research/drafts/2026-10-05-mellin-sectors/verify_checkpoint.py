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

# small_transformed_rectangle: bounded source scope, exact provenance, finite diagnostics only.
new=next(x for x in pins['proof_sources'] if x['id']=='small_transformed_rectangle')
assert new['original_mathematical_source']['sha256']=='fae77897f099320f55aa06fc6f3bfeff23c7fdb4d5633f3373f9ba991ee3bab4'
assert new['frozen_author_manifest_identity']['sha256']=='1c365a521796993892770f0bccbea72162967bd690bba4cdd0e74d10fb6d2db3'
assert new['independent_review_identity']['sha256']=='f9470215dc38cc967c7eb7d200e4309a5bdf15c2cc1980bec0899a97c71e19fd'
assert new['independent_review_manifest_identity']['sha256']=='622c44ed7801ede96a262fe5e9228a4a5af5f9d7d8dd8564ebc075a118fdc87a'
assert new['final_acceptance_record_identity']['sha256']=='0938ce9d6465f5f652df0a1a59dcde7df61e665849a0b52cdf61d6aed571deaa'
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/small_transformed_rectangle/checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/small_transformed_rectangle/EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_ACTUAL_SMALL_TRANSFORMED_FULL_KERNEL_RECTANGLE_ONLY_NOT_LEAN'
assert 36+Fraction(292,15)+Fraction(32,5)==Fraction(928,15)
assert Fraction(32,5)+10==Fraction(82,5)
assert -Fraction(2011,2)+72+288==-Fraction(1291,2)
assert 12-2==10 and 12-4==8 and 10*3==30
assert Fraction(4,16)==Fraction(1,4)<1
assert manifest['global_frontier']['mixed_and_large_transformed_rectangles']=='MIXED_BOUNDARY_AND_HIGH_TAIL_PAID_BOUNDED_MIDDLE_OPEN'
assert manifest['global_frontier']['high_mixed_near_full_kernel_aggregate']=='REDUCED_TO_BOUNDED_MIDDLE_FULL_K_NEAR_UNEQUAL_SQUARE_UNPROVED'

# periodic_determinant_mapping: bounded source scope, exact provenance, finite diagnostics only.
new=next(x for x in pins['proof_sources'] if x['id']=='periodic_determinant_mapping')
assert new['original_mathematical_source']['sha256']=='5e0e77ffd01a1f895d571137a6d9f75266b2b061b1d09928380b8e052ae443f3'
assert new['frozen_author_manifest_identity']['sha256']=='f64ebbd751dfc2fe70397b5c478168a361791380c898ecf868a670f753162655'
assert new['independent_review_identity']['sha256']=='5114c2f4de304955a507f408e1b366fbb734ee0fef5257c2f149c824557a54e0'
assert new['independent_review_manifest_identity']['sha256']=='a34875410b075378734ae601f3b24da469a0862f21c7f2dee760d601a691baa8'
assert new['final_acceptance_record_identity']['sha256']=='183594b4ca49fb9fd50f48cab401c6bcf8c3f54d0dd5b535bfe607fd50fa8968'
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/periodic_determinant_mapping/checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/periodic_determinant_mapping/EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_GENERIC_SMOOTH_DETERMINANT_CELL_ONLY_NOT_LEAN'
assert 2*Fraction(7,64)+1==Fraction(39,32)
assert 2*(400-519)==-238
assert manifest['global_frontier']['collective_outer_variable_and_determinant_sums']=='UNPROVED'
assert manifest['global_frontier']['global_determinant_near_aggregate_bound']=='UNPROVED'
assert -395+9*35==-80 and -80+402-400==-78
assert 2076*12-76==24836 and 5-12==-7
assert manifest['global_frontier']['bounded_middle_restricted_principal_subtraction']=='RETAINED_INSIDE_FULL_K'

# Finite prime-Hecke interface: exact source identity and bounded mathematical replay.
new=next(x for x in pins['proof_sources'] if x['id']=='prime_hecke_correlation')
assert new['original_mathematical_source']['sha256']=='a52eab9342a869573c1547f2110b91a05254d702633ee7dfab220100895cbcd6'
assert new['independent_review_identity']['sha256']=='d317ca0374e4e8ebfd3a8fcb4737bde5a3f3df0f0e3596f715d1bdbdd1f18b44'
assert new['review_acceptance_record_identity']['sha256']=='5d34d9880ee28db8413bfc925c98bb8538e04eaafde86e1d39e279a5790a24c3'
assert new['final_acceptance_record_identity']['sha256']=='ef3f42d08cef6640735ae3718a43d75b45bf755fd2a70fc04be0bb121180e097'
for key,name in [('original_diagnostic_script','checks.py'),('original_diagnostic_expected_result','EXPECTED_CHECKS.json'),('publication_independent_diagnostic_script','independent_checks.py'),('publication_independent_diagnostic_expected_result','EXPECTED_INDEPENDENT_CHECKS.json')]:
    assert new[key]['sha256']==hashlib.sha256((root/'diagnostics/prime_hecke_correlation'/name).read_bytes()).hexdigest()
assert new['status']=='SOURCE_REVIEWED_FINITE_PRIME_HECKE_LEMMA_ONLY_NOT_LEAN'
assert manifest['global_frontier']['bounded_middle_arithmetic_upper_bound']=='UNPROVED'
assert manifest['global_frontier']['averaged_outer_variable_saving']=='UNPROVED'
assert len(manifest['preserved_proof_document_hashes'])>=16
import subprocess,sys
independent=subprocess.check_output([sys.executable,'-B',str(root/'diagnostics/prime_hecke_correlation/independent_checks.py')])
assert independent==(root/'diagnostics/prime_hecke_correlation/EXPECTED_INDEPENDENT_CHECKS.json').read_bytes()

# Actual averaged attachment: exact accepted source, common-weight scope and open middle.
new=next(x for x in pins['proof_sources'] if x['id']=='averaged_determinant_attachment')
assert new['original_mathematical_source']['sha256']=='3f58296591df9cadd06c80d3e72b2fa45a74b7e61ee5d803751037064ee75be3'
assert new['independent_review_identity']['sha256']=='ff61068e8df9be97df8c61ab07c203324bab74af5a442fb85a4212f1a1af7c2b'
assert new['review_acceptance_record_identity']['sha256']=='90d03d2a06f5e050e87b9369d92f8877b19666ab4791a3366c694839a5106aec'
assert new['final_acceptance_record_identity']['sha256']=='076822db84207e7ce2103732fff1151a9e7e2552d52b9c38b7c4eedc0867e94d'
assert new['status']=='SOURCE_REVIEWED_ACTUAL_AVERAGED_ATTACHMENT_WITH_UNPAID_OUTER_SUM_NOT_LEAN'
for key,name in [('original_diagnostic_script','checks.py'),('original_diagnostic_expected_result','EXPECTED_CHECKS.json'),('publication_independent_diagnostic_script','independent_checks.py'),('publication_independent_diagnostic_expected_result','EXPECTED_INDEPENDENT_CHECKS.json')]:
    assert new[key]['sha256']==hashlib.sha256((root/'diagnostics/averaged_determinant_attachment'/name).read_bytes()).hexdigest()
independent=subprocess.check_output([sys.executable,'-B',str(root/'diagnostics/averaged_determinant_attachment/independent_checks.py')])
assert independent==(root/'diagnostics/averaged_determinant_attachment/EXPECTED_INDEPENDENT_CHECKS.json').read_bytes()
assert 1038-34-200==804 and Fraction(519-400,2)==Fraction(119,2)
assert 804+Fraction(119,2)==Fraction(1727,2)
assert manifest['global_frontier']['averaged_actual_lower_bound']=='NOT_CLAIMED'
assert manifest['global_frontier']['balanced_core_energy_and_joint_cross']=='OPEN'
assert manifest['final_gap_status']=='OPEN'

# Bounded common-level test: exact accepted identities and scope, not a Lean proof.
new=next(x for x in pins['proof_sources'] if x['id']=='common_level_outer_variance')
assert new['original_mathematical_source']['sha256']=='30256480e5125286eff769114786eabc0eedd0e27f2ec26efc2249b10e41a659'
assert new['mandatory_scope_addendum_identity']['sha256']=='9085e2495c97464356b0c50d56d8e184aabe76ddcebe216bdc24381ffb730e29'
assert new['independent_review_identity']['sha256']=='542aafec1f63c1c6134f431f5ef2868fc84ae0fa2dff8f7c4f441c5230fc016a'
assert new['final_acceptance_record_identity']['sha256']=='7e7f9788978cb2e40e5450f5629408bf9e5add756c74ec71c882e873bf18e124'
assert new['status']=='SOURCE_REVIEWED_BOUNDED_COMMON_LEVEL_VARIANCE_TEST_ONLY_NOT_LEAN'
assert len(manifest['preserved_proof_document_hashes'])>=18
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/common_level_outer_variance'/'checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/common_level_outer_variance'/'EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['publication_independent_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/common_level_outer_variance'/'independent_checks.py').read_bytes()).hexdigest()
assert new['publication_independent_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/common_level_outer_variance'/'EXPECTED_INDEPENDENT_CHECKS.json').read_bytes()).hexdigest()
independent=subprocess.check_output([sys.executable,'-B',str(root/'diagnostics/common_level_outer_variance/independent_checks.py')])
assert independent==(root/'diagnostics/common_level_outer_variance/EXPECTED_INDEPENDENT_CHECKS.json').read_bytes()
assert manifest['global_frontier']['common_level_correlation_scope']=='EXPLICIT_GM_10_2_EXPRESSION_ONLY_Z_SLACK_RETAINED'
assert manifest['global_frontier']['common_level_GM7_1_kernel_or_total_error_lower_bound']=='NOT_CLAIMED'
assert manifest['global_frontier']['common_level_complete_collective_application']=='UNPROVED'
assert manifest['global_frontier']['bounded_middle_arithmetic_upper_bound']=='UNPROVED'
assert manifest['final_gap_status']=='OPEN'

# Local time audit: source-reviewed bounded statements and finite arithmetic only.
new=next(x for x in pins['proof_sources'] if x['id']=='time_parameter_audit')
assert new['original_mathematical_source']['sha256']=='590e0befd1fd605285acd39dd2257cf31846136ba2ac46968e70e21fb35e84f8'
assert new['frozen_author_manifest_identity']['sha256']=='97235fcb86306fc88fd87b79abb8843370224fd3eac1cfc075dbb71bd5097650'
assert new['independent_review_identity']['sha256']=='793aefc52a71877a1022591bb7bc55fe2f97e39f7d0e71caa34c1ed1ecd8ae39'
assert new['independent_review_manifest_identity']['sha256']=='ade03ad4c2cb7c88e335fc36ef00ebec5513eb2ab0d02ba651f9c2df3026575f'
assert new['review_acceptance_record_identity']['sha256']=='bbb848ccada1a83f19028bff44c01c0625dd88a82db0ab40ee1f223f8794413d'
assert new['status']=='SOURCE_REVIEWED_BOUNDED_LOCAL_PARAMETER_AND_CONDITIONAL_CONSUMER_AUDIT_ONLY_NOT_LEAN'
assert new['independent_source_review_count']==1
assert len(manifest['preserved_proof_document_hashes'])>=19
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/time_parameter_audit'/'checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/time_parameter_audit'/'EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert new['publication_independent_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics/time_parameter_audit'/'independent_checks.py').read_bytes()).hexdigest()
assert new['publication_independent_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics/time_parameter_audit'/'EXPECTED_INDEPENDENT_CHECKS.json').read_bytes()).hexdigest()
independent=subprocess.check_output([sys.executable,'-B',str(root/'diagnostics/time_parameter_audit/independent_checks.py')])
assert independent==(root/'diagnostics/time_parameter_audit/EXPECTED_INDEPENDENT_CHECKS.json').read_bytes()
assert Fraction(481,1)/Fraction(94,100)==Fraction(24050,47)
assert Fraction(461,1)/Fraction(94,100)==Fraction(23050,47)
assert -272+60+Fraction(22,5)==-Fraction(1038,5)
assert 118+400-519==-1 and 113+381-495==-1
assert manifest['global_frontier']['altered_parameter_global_theorem']=='UNPROVED'
assert manifest['global_frontier']['original_time_parameters']=='UNCHANGED_t0_L519_W_L400'
assert manifest['global_frontier']['new_time_good_family_ratio_bound']=='UNPROVED'
assert manifest['final_gap_status']=='OPEN'

# Note 21: selected accepted scope and finite diagnostics, not Lean certification.
new=next(x for x in pins['proof_sources'] if x['id']=='collective_cover_spectral_test')
assert new['original_mathematical_source']['sha256']=='91b9c8f21f6ab446a9b63463cd0d63fca4f407cfb835a592e96a0a0f6cc300f0'
assert new['independent_review_identity']['sha256']=='1fe764ded462cbb2cfe6749266cfa9d2f07fa20daf29ab9771a61836f1980d78'
assert new['review_acceptance_record_identity']['sha256']=='9b549acaa4970877cc1ed72eefce596feccebc6b762fcbea9e46e5b8b78b3ed1'
assert new['status']=='SOURCE_REVIEWED_BOUNDED_COLLECTIVE_COVER_AND_PROFILE_FLOOR_TEST_ONLY_NOT_LEAN'
assert new['independent_source_review_count']==1
assert len(manifest['preserved_proof_document_hashes'])>=20
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics'/'collective_cover_spectral_test'/'checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics'/'collective_cover_spectral_test'/'EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert next(x for x in pins['proof_sources'] if x['id']=='time_parameter_audit')['finished_snapshot_manifest_identity']['sha256']=='6f9678cf1235865ab7a053e47f58121d6f5e3be49ea3cf47b419af5fe48e1a31'
assert 1038-34-200==804 and 804+Fraction(119,2)==Fraction(1727,2)
assert manifest['global_frontier']['collective_defined_R_beta_floor']=='EXACT_INDIVIDUAL_L1_NORMS_RETAINED_H_SCALE_CONDITIONAL'
assert manifest['global_frontier']['bounded_middle_arithmetic_upper_bound']=='UNPROVED'
assert manifest['final_gap_status']=='OPEN'
assert manifest['global_frontier']['common_product_additional_h_sectors']=='UNPAID_GCD_h_p_q1_D_RETAINED'
assert manifest['global_frontier']['actual_masked_profile_l1_lower_bound']=='NOT_ESTABLISHED'

# Note 22: selected accepted scope and finite diagnostics, not Lean certification.
new=next(x for x in pins['proof_sources'] if x['id']=='reciprocal_prime_attachment_audit')
assert new['original_mathematical_source']['sha256']=='e1b25b20c4dfee3b9b3f198d7995a55c6302ccf45d5cfb69d88a94b2d279f46a'
assert new['independent_review_identity']['sha256']=='855c7b86f860b458c5154129f5c7075eb32056037e46c186c28c64de12378a9f'
assert new['review_acceptance_record_identity']['sha256']=='2dc884f0099d1ef931f3d08c8c9908904879356ac58d558231dc8e507a4a8351'
assert new['status']=='SOURCE_REVIEWED_SMOOTH_RECIPROCAL_REPRESENTATION_AND_WEAK_BC_WRIGHT_LEDGER_ONLY_NOT_LEAN'
assert new['independent_source_review_count']==1
assert len(manifest['preserved_proof_document_hashes'])>=21
assert new['original_diagnostic_script']['sha256']==hashlib.sha256((root/'diagnostics'/'reciprocal_prime_attachment_audit'/'checks.py').read_bytes()).hexdigest()
assert new['original_diagnostic_expected_result']['sha256']==hashlib.sha256((root/'diagnostics'/'reciprocal_prime_attachment_audit'/'EXPECTED_CHECKS.json').read_bytes()).hexdigest()
assert Fraction(5,2)-Fraction(3,2)+Fraction(17,8)==Fraction(25,8)
assert Fraction(5,2)-Fraction(3,2)+Fraction(19,8)==Fraction(27,8)
assert Fraction(27,8)>2 and Fraction(1,2)-Fraction(1,16)==Fraction(7,16)
assert manifest['global_frontier']['reciprocal_actual_lower_bound_or_impossibility']=='NOT_CLAIMED'
assert manifest['global_frontier']['bounded_middle_arithmetic_upper_bound']=='UNPROVED'
assert manifest['final_gap_status']=='OPEN'
# Note 23: the source proof and fixed-gap clarification form one accepted package.
new=next(x for x in pins['proof_sources'] if x['id']=='averaged_scalar_saddle')
assert new['original_mathematical_source']['sha256']=='f1734577f68fc45b50e559ed67b0398d4221d375e6a8867c249a20ae1ed7b895'
assert new['mandatory_fixed_gap_addendum_identity']['sha256']=='b76584a68e6673a5694472e04c7f66c4f47a50dba1860cd56ce7dec3b35b2fbe'
assert new['independent_review_identity']['sha256']=='724180ca5c279bd59921a5cad77a06a1349ced8ded21619e19c0d988d6a434fd'
assert new['review_acceptance_record_identity']['sha256']=='e8131c3135338ed719646c520ad01cb0d3e526e80b951601669bc7dd8a0859c6'
assert new['finished_snapshot_manifest_identity']['sha256']=='ed2dc8d99eae57cdffd654fd37a71687827e6db0130d55d8c227a9e882b8223a'
assert new['status']=='SOURCE_REVIEWED_JOINT_UNTILTED_SCALAR_AND_NAMED_CONSUMER_INTERFACES_ONLY_NOT_LEAN'
assert new['independent_source_review_count']==1
assert len(manifest['preserved_proof_document_hashes'])==22
for key,directory,name in [('original_diagnostic_script','averaged_scalar_saddle','checks.py'),('original_diagnostic_expected_result','averaged_scalar_saddle','EXPECTED_CHECKS.json'),('fixed_gap_diagnostic_script','averaged_scalar_saddle_fixed_gap','checks.py'),('fixed_gap_diagnostic_expected_result','averaged_scalar_saddle_fixed_gap','EXPECTED_CHECKS.json'),('publication_independent_diagnostic_script','averaged_scalar_saddle','independent_checks.py'),('publication_independent_diagnostic_expected_result','averaged_scalar_saddle','EXPECTED_INDEPENDENT_CHECKS.json')]:
    assert new[key]['sha256']==hashlib.sha256((root/'diagnostics'/directory/name).read_bytes()).hexdigest()
independent=subprocess.check_output([sys.executable,'-B',str(root/'diagnostics/averaged_scalar_saddle/independent_checks.py')])
assert independent==(root/'diagnostics/averaged_scalar_saddle/EXPECTED_INDEPENDENT_CHECKS.json').read_bytes()
assert Fraction(2)/(1+Fraction(1,4))>Fraction(3,2)
assert 247-128==119 and 2*128-247==9
assert 237-123==114 and 2*123-237==9
assert 2+9*11==101
assert manifest['global_frontier']['averaged_saddle_scope']=='JOINT_UNTILTED_SCALAR_AND_NAMED_CONSUMERS_ONLY'
assert manifest['global_frontier']['averaged_saddle_fixed_gap_primary_upper_edge']=='SUPPLIED_BY_MANDATORY_FIXED_GAP_EXTENSION'
assert manifest['global_frontier']['averaged_saddle_arbitrary_tilted_kernels']=='UNPROVED'
assert manifest['global_frontier']['averaged_saddle_relative_positivity']=='NOT_CLAIMED'
assert manifest['global_frontier']['altered_parameter_global_theorem']=='UNPROVED'
assert manifest['global_frontier']['original_time_parameters']=='UNCHANGED_t0_L519_W_L400'
assert manifest['global_frontier']['new_time_good_family_ratio_bound']=='UNPROVED'
assert manifest['global_frontier']['bounded_middle_arithmetic_upper_bound']=='UNPROVED'
assert manifest['final_gap_status']=='OPEN'
# Note 24: unchanged-input threshold and conditional new-mask ledger only.
new=next(x for x in pins['proof_sources'] if x['id']=='symbolic_exceptional_gate')
assert new['original_mathematical_source']['sha256']=='c8c53d25f8d52ebd307a1cc3d9b627bbff5283c8e88ab76794ddb65a5ee539e9'
assert new['independent_review_identity']['sha256']=='eea705da2e3c5a6892b6e2c27927db07476d47c83bfc497dd221ac9d889c6ae3'
assert new['independent_review_manifest_identity']['sha256']=='e2b521ad3b454d116f10f2f54b8470b20759bd314285d82602753ef0f3444886'
assert new['status']=='SOURCE_REVIEWED_CONDITIONAL_SYMBOLIC_EXCEPTIONAL_GATE_ONLY_NOT_LEAN'
assert new['independent_source_review_count']==1
for key,name in [('publication_independent_diagnostic_script','independent_checks.py'),('publication_independent_diagnostic_expected_result','EXPECTED_INDEPENDENT_CHECKS.json')]:
    assert new[key]['sha256']==hashlib.sha256((root/'diagnostics/symbolic_exceptional_gate'/name).read_bytes()).hexdigest()
independent=subprocess.check_output([sys.executable,'-B',str(root/'diagnostics/symbolic_exceptional_gate/independent_checks.py')])
assert independent==(root/'diagnostics/symbolic_exceptional_gate/EXPECTED_INDEPENDENT_CHECKS.json').read_bytes()
assert Fraction(739-547,3)==64 and Fraction(5*739-2219,12)==123
assert 2*Fraction(1435,4)-Fraction(81+81+5*77,3)==Fraction(3211,6)
assert 739-77==662 and Fraction(Fraction(1567,2)-547,3)==Fraction(473,6)
assert manifest['global_frontier']['symbolic_original_raw_gate']==64
assert manifest['global_frontier']['symbolic_473_over_6_scope']=='CONDITIONAL_NEW_MASK_AND_COMPLETE_TRANSFER_ONLY'
assert manifest['global_frontier']['symbolic_changed_time_count_or_genuine_moment']=='UNPROVED'
assert manifest['final_gap_status']=='OPEN'
print(json.dumps({'integrity':'PASS','listed_files':len(manifest['files']),'exact_exponents':'PASS','analytic_or_Lean_certification':False},indent=2))
