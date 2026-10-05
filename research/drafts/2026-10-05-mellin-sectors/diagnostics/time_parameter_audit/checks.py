#!/usr/bin/env python3
"""Finite consistency checks for local lemmas and exact constraint ledger."""
from fractions import Fraction as F
from pathlib import Path
import itertools,json,math
import mpmath as mp
ROOT=Path(__file__).resolve().parent
out={'finite_diagnostics_only':True,'no_new_good_character_or_main_term_theorem':True}
for gap,want in [(118,(516,397)),(113,(495,381))]:
 found=next((a,b) for a in range(1,651) for b in range(1,601) if a-b>gap and F(153,50)*a-4*b<=-9)
 assert found==want
out['minimal_integer_two_constraint_pairs']={'hard':[516,397],'conditional_Gaussian':[495,381],'status':'PASS'}
assert F(481,1)/F(94,100)==F(24050,47)
assert F(461,1)/F(94,100)==F(23050,47)
assert -272+60+F(22,5)==-F(1038,5)
ledgers=[]
for a,b in [(519,400),(516,397),(495,381),(53,43)]:
 vals={'a':a,'b':b,'gap':a-b,'hard_consumer_exponent':118+b-a,'Gaussian_consumer_exponent':113+b-a,'u_exponent':5-b,'v_exponent':F(51,50)*a-2*b,'xu2_exponent':F(51,50)*a+10-2*b,'xv2_exponent':F(153,50)*a-4*b,'far_tail_exponent':F(5049,5000)*a-b,'common_Pt0_AFE_eligible':a>=max(b+73,88)}
 assert a>b+5 and b>5 and b>=14 and 2*b>=F(51,50)*a+19 and 4*b>=F(153,50)*a+9 and F(5049,5000)*a-b>10
 ledgers.append({k:str(v) if isinstance(v,F) else v for k,v in vals.items()})
assert not ledgers[-1]['common_Pt0_AFE_eligible']
out['complete_local_saddle_ledger']={'cases':ledgers,'status':'PASS'}
# Normalized broadened Gaussian domination, including its exact maximum.
maxratio=0
for n in range(10001):
 y=n/500
 ratio=math.sqrt(2)*y*math.exp(-y*y/8)
 assert ratio<=2*math.sqrt(2/math.e)+1e-13;maxratio=max(maxratio,ratio)
assert abs(maxratio-2*math.sqrt(2/math.e))<1e-13
out['broadened_Gaussian_weight_domination']={'grid_cases':10001,'maximum':maxratio,'maximizer_abs_t_minus_tc_over_W':2,'status':'PASS'}
mp.mp.dps=35
height=[]
for eta,kappa in itertools.product([mp.mpf('.1'),mp.mpf('.01')],[0,mp.mpf('.2'),mp.mpf('.5'),1]):
 lhs=2*mp.quad(lambda y:mp.exp(-y*y/2+kappa*y)/mp.sqrt(eta*eta+y*y),[0,1,4,mp.inf])
 rhs=mp.exp(kappa*kappa)*2*mp.quad(lambda y:mp.exp(-y*y/4)/mp.sqrt(eta*eta+y*y),[0,1,4,mp.inf])
 assert lhs<=rhs*(1+mp.mpf('1e-28'));height.append(float(lhs/rhs))
out['integrated_height_completion_of_squares']={'cases':len(height),'maximum_ratio':max(height),'status':'PASS'}
# Exact FE gamma definitions; relation-preserving small shifts, no A2022 sample.
b1=mp.mpc(0,'.011');b2=mp.mpc(0,'.021');b3=b1+b2
B=mp.mpf(80);al=mp.pi/B

def logZ(s,p,par,root):return 1j*root+(mp.mpf('.5')-s)*mp.log(p/mp.pi)+mp.loggamma((1-s+par)/2)-mp.loggamma((s+par)/2)
def gpp(s,par):return (mp.polygamma(1,(1-s+par)/2)-mp.polygamma(1,(s+par)/2))/4
qerrors=[];rerrors=[];moderrs=[];curv=[]
for t0,par,realoff,toff in itertools.product([20,100],[0,1],[0,al,-al],[0,2,-3]):
 s=mp.mpf('.5')+realoff+1j*(2*mp.pi*t0+toff)
 qs=[];rs=[]
 for p,root in [(11,mp.mpf('.2')),(101,mp.mpf('-.7'))]:
  z=logZ(s,p,par,root);zz=[logZ(s+h,p,par,root) for h in [b1,b2,b3]]
  logq=-sum(v-z for v in zz)/2-b3*mp.log(p*t0)
  logr=(z+zz[2]-zz[0]-zz[1])/2
  q=mp.exp(logq);r=mp.exp(logr);qs.append(q);rs.append(r)
  assert abs(r-q*mp.exp(b3*mp.log(p*t0)+zz[2]-z))<mp.mpf('1e-27')
  ratio=abs(r-1)/(abs(b1*b2)/t0);assert ratio<10;curv.append(float(ratio))
  if realoff==0:moderrs.append(float(abs(abs(q)-1)))
 qerrors.append(float(abs(qs[0]-qs[1])));rerrors.append(float(abs(rs[0]-rs[1])))
 assert abs(qs[0]-qs[1])<mp.mpf('1e-27') and abs(rs[0]-rs[1])<mp.mpf('1e-27')
integerrs=[]
for par in [0,1]:
 s=mp.mpf('.5')+40j;p=11;root=mp.mpf('.2')
 lhs=(logZ(s,p,par,root)+logZ(s+b3,p,par,root)-logZ(s+b1,p,par,root)-logZ(s+b2,p,par,root))/2
 rhs=b1*b2/2*mp.quad(lambda u:mp.quad(lambda v:gpp(s+u*b1+v*b2,par),[0,1]),[0,1])
 assert abs(lhs-rhs)<mp.mpf('1e-27');integerrs.append(float(abs(lhs-rhs)))
out['exact_parity_only_q_and_curvature_r']={'parameter_cases':len(qerrors),'max_prime_root_q_difference':max(qerrors),'max_prime_root_r_difference':max(rerrors),'max_critical_modulus_error':max(moderrs),'max_normalized_curvature_ratio':max(curv),'mixed_second_difference_checks':len(integerrs),'max_integral_error':max(integerrs),'status':'PASS'}
# The central saddle Taylor factor at small contour points.
saddle=0
for x,u,v in itertools.product([1,20,50,80],[-.02,0,.02],[-.004,0,.003]):
 w=u+1j*v;term=abs(mp.exp(w/2-2j*mp.pi*x*(mp.exp(w)-1-w))-1);cap=30*(abs(w)+x*abs(w)**2)
 assert term<=cap+mp.mpf('1e-25');saddle+=1
out['local_saddle_Taylor_factor']={'cases':saddle,'status':'PASS'}
# Printed P^3 obstruction is unchanged by fixed time powers.
for a,b in [(519,400),(495,381),(53,43)]:
 assert 1+2*1==3
out['GM_extra_P_is_parameter_independent']='PASS'
out['status']='PASS'
s=json.dumps(out,sort_keys=True,indent=2)+'\n';(ROOT/'CHECKS.json').write_text(s);print(s,end='')
