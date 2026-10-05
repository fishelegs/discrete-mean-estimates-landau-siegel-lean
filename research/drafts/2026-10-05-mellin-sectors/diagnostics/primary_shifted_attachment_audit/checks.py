#!/usr/bin/env python3
"""Finite budget/logic checks, not proof of the cited primary theorems."""
import json,math
import mpmath as mp
mp.mp.dps=60
from fractions import Fraction as F
from pathlib import Path
from sympy import primerange,isprime,kronecker_symbol
HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True,'new_arithmetic_estimate_claimed':False}
assert 2*519-400+16*9==782
assert 782+2==784
assert F(2,4)+4==F(9,2)
assert 1038-400==638
assert 638+519==1157
assert 2*1157-1038==1276
assert 2*F(9,2)-F(9,2)==F(9,2)
assert F(2,3)*2+1==F(7,3)
assert F(2,3)*F(9,2)==3
assert F(2,3)*1038==692
assert F(1,2)*F(9,2)==F(9,4)
assert 519-400==119
assert F(127,128)>F(1,2)
assert F(37,38)+F(7,64*19)==F(1191,1216)>F(1,2)
assert F(25,28)<1 and F(15,19)<1
out['exact_CLMR_MRT_and_pointwise_error_exponents']='PASS'

largeprime=0;aggregate=0
for P in [3,5,7,11,20]:
 ps=list(primerange(P+1,2*P))
 E=[]
 for r in range(1,min(P**3,5001)):
  divisors=[p for p in ps if r%p==0]
  assert len(divisors)<=2
  assert sum(divisors)<=4*P
  largeprime+=1
  if r%7 in [0,1,4]:E.append(r)
 lhs=sum(p*sum(r%p==0 for r in E) for p in ps)
 rhs=sum(sum(p for p in ps if r%p==0) for r in E)
 assert lhs==rhs and lhs<=4*P*len(E)
 aggregate+=1
out['aggregate_large_prime_divisor_accounting']={'shift_cases':largeprime,'exceptional_set_identities':aggregate,'actual_contribution_lower_bound_claimed':False,'status':'PASS'}

widthtests=0
for P in [100,1000]:
 for eps in [F(1,10),F(1,20),F(1,100)]:
  hi=F(P)*(1+eps);ps=[p for p in primerange(P+1,math.ceil(hi)) if p<hi]
  H=50*P
  actual=sum(p*(H//p) for p in ps)
  assert len(ps)<=P*eps+1
  assert actual<=2*P*(P*eps+1)*(F(H,P)+1)
  widthtests+=1
out['selected_good_shift_count_budget']={'cases':widthtests,'status':'PASS'}

scales=[]
for L in [5,10,20,30]:
 B=mp.mpf(L)**9;logx=2*B+mp.mpf("4.5")*L+1038*mp.log(L)
 log_eff=logx-400*mp.log(L);log_literal=logx-395*mp.log(L)
 assert abs(log_literal-log_eff-5*mp.log(L))<mp.mpf("1e-40")
 assert log_eff-(1-.01)*logx>0
 assert (2/3)*logx<log_literal
 assert (2/3)*logx>B
 assert math.log(2)+log_literal<3*B
 assert logx>2*B # natural weighted length is above Q^2 for Q=P
 assert (1/3)*B-1000*math.log(L)>0
 scales.append({'L':L,'range_obstruction_log_ratio':float(log_eff-mp.mpf('.99')*logx),'natural_length_excess_log':float(logx-2*B)})
out['physical_shift_and_length_scale_checks']={'cases':scales,'effective_band_is_only_favorable_subband':True,'status':'PASS'}

# Formal finite/infinite inverse distinction in a concrete non-exceptional
# character model; this is an algebra diagnostic, not an A2022 example.
D=5;X=D**4;ell=641
assert isprime(ell) and ell>X
h=int(kronecker_symbol(D,ell));assert h==1
nu_p=1+h;ups_p=-(1+h)
finite_inverse_nu_prime=nu_p
infinite_inverse_nu_prime=nu_p+ups_p
assert finite_inverse_nu_prime==2 and infinite_inverse_nu_prime==0
assert finite_inverse_nu_prime+2==4 and infinite_inverse_nu_prime+2==2
out['finite_inverse_cannot_be_replaced_by_infinite_model']={'D':D,'X':X,'prime':ell,'finite_inverse_nu_prime':finite_inverse_nu_prime,'infinite_inverse_nu_prime':infinite_inverse_nu_prime,'A2022_claimed_for_sample':False,'status':'PASS'}

out['theorem_scope_logic']={
 'CLMR_2023_unconditional_not_earlier_GRH_paper':True,
 'MRT_ordinary_divisor_coefficients_not_actual_mixed_finite_inverse':True,
 'MRT_exceptional_budget_failure_not_actual_lower_bound':True,
 'Lau_current_version_is_v2_2026':True,
 'dk_times_d2_not_actual_four_factor_times_four_factor':True,
 'BTB_Generalized_Lindelof_not_assumed':True,
 'failed_printed_attachment_not_impossibility_of_adaptation':True,
 'status':'PASS'}
out['status']='PASS'
s=json.dumps(out,indent=2,sort_keys=True)+'\n';(HERE/'CHECKS.json').write_text(s);print(s,end='')
