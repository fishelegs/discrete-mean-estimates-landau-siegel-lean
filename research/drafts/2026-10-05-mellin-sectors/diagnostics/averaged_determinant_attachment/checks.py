#!/usr/bin/env python3
"""Finite normalization and primary exponent checks, not an asymptotic proof."""
import itertools,cmath,math,json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
ROOT=Path(__file__).resolve().parent
out={'finite_diagnostics_only':True,'not_an_A2022_example':True}
ratios=0;signs=set();homerr=[]
alpha=.02;en=alpha+.17j;eb=alpha-.23j;beta=.011j
for M,E in [(2,3),(3,5),(5,2)]:
 for a1,a2,b1,b2 in itertools.product(range(1,7),repeat=4):
  k=M*a1*a2;ell=E*b1*b2
  for sig in [1,-1]:
   Delta=k-sig*ell
   if Delta==0:continue
   eps=1 if Delta>0 else -1;root=math.sqrt(abs(Delta))
   A=M*a1/root;B=sig*E*b1/root;C=b2/root;FF=a2/root
   assert abs(A*FF-B*C-eps)<2e-12
   rr=sig*(1-eps/(A*FF));assert abs(rr-ell/k)<2e-12
   signs.add((sig,eps));ratios+=1
   raw=(a1**(-beta)*(a1*a2)**(-en)*b1**beta*(b1*b2)**(-eb.conjugate())/(k*ell)**.5)
   aa1=a1/root;aa2=a2/root;bb1=b1/root;bb2=b2/root
   norm=(aa1**(-beta)*(aa1*aa2)**(-en)*bb1**beta*(bb1*bb2)**(-eb.conjugate())/((M*aa1*aa2)*(E*bb1*bb2))**.5)
   transformed=abs(Delta)**(-1-en-eb.conjugate())*norm
   er=abs(raw-transformed);assert er<1e-12;homerr.append(er)
assert signs=={(1,1),(1,-1),(-1,1)}
out['both_congruence_signs_and_determinant_normalization']={'cases':ratios,'sign_pairs':sorted(signs),'status':'PASS'}
out['actual_monomial_harmonic_homogeneity']={'cases':len(homerr),'max_error':max(homerr),'status':'PASS'}
# Common p exponent has no t after same-branch FE matching.
z1=alpha+.15j;z2=alpha-.07j;wr1=-alpha+.23j;wr2=-alpha-.11j;wn1=-alpha-.13j;wn2=-alpha+.31j
on1=alpha+.21j;on2=alpha-.19j;op1=alpha+.28j;op2=alpha-.24j
phasechecks=0
for i,j in itertools.product([0,1],repeat=2):
 power=2*z1+2*z2.conjugate()+on1+on2.conjugate()+op1+op2.conjugate()+2*i*((z2+wr2)-(z1+wr1))+2*j*((z2+wn2)-(z1+wn1))
 assert abs(power.real-8*alpha)<1e-14
 for p in [11,17,101]:
  vals=[]
  for t in [0,1.5,100]:
   s=.5+1j*t;un1=s+z1+wr1;un2=s+z2+wr2;up1=s+z1+wn1;up2=s+z2+wn2
   matched=(p**(1-2*un1)*(p**(1-2*un2)).conjugate())**i*(p**(1-2*up1)*(p**(1-2*up2)).conjugate())**j
   exact=p**(2*i*((z2+wr2)-(z1+wr1))+2*j*((z2+wn2)-(z1+wn1)))
   assert abs(matched-exact)<1e-11;phasechecks+=1
out['same_branch_conductor_t_cancellation']={'cases':phasechecks,'residual_gamma_not_frozen':True,'status':'PASS'}
# Fourier inversion toy with the same log-rho scaling structure, three cutoff variables.
mp.mp.dps=30;fourier=[]
for rr in [(mp.mpf('.8'),mp.mpf('1.1'),mp.mpf('1.3')),(mp.mpf('1.2'),mp.mpf('.9'),mp.mpf('1.05'))]:
 logs=[mp.log(v) for v in rr];aa=mp.mpf(7)/4;bb=-sum(logs);cc=-sum(v*v for v in logs)
 for rho in [mp.mpf('.7'),mp.mpf('1'),mp.mpf('2.5'),mp.mpf('4')]:
  y=mp.log(rho);direct=mp.exp(aa*(-y*y)+bb*y+cc)
  def integrand(u):return mp.sqrt(mp.pi/aa)*mp.exp(cc+(bb-1j*u)**2/(4*aa))*mp.exp(1j*u*y)/(2*mp.pi)
  reconstructed=mp.quad(integrand,[-30,0,30]);err=abs(direct-reconstructed)
  assert err<mp.mpf('1e-25');fourier.append(float(err))
out['log_rho_common_weight_Fourier_model']={'cases':len(fourier),'max_error':max(fourier),'not_a_substitute_for_compact_support_proof':True,'status':'PASS'}
# Exponent vectors in P,D,L, with tc of size L^519.
def add(*xs):return tuple(sum(x[j] for x in xs) for j in range(3))
def mul(c,x):return tuple(c*a for a in x)
P=(F(1),F(0),F(0));D=(F(0),F(1),F(0));Q=(F(1),F(0),F(519));x=(F(2),F(1,2),F(1038));W=(F(0),F(0),F(400));N=(F(1),F(0),F(-68));H=add(x,mul(-1,P),mul(-1,W))
rootK=add(P,mul(F(1,2),D),mul(F(1,2),N))
perouter=add(mul(F(-1,2),x),rootK,mul(F(1,2),H))
outer=add(perouter,mul(2,Q));R0=mul(F(1,2),add(H,mul(-1,Q)));outerR0=add(outer,R0)
assert perouter==(F(1),F(1,2),F(-234));assert outer==(F(3),F(1,2),F(804));assert outerR0==(F(3),F(3,4),F(1727,2))
Qnu=add(Q,mul(F(1,2),D));arg1=add(Qnu,mul(-1,P),mul(-1,D));arg2=add(H,mul(-1,Q),mul(-1,D))
assert arg1==(0,F(-1,2),519) and arg2==(0,F(-1,2),119)
out['primary_R0_R2_and_outer_budget']={'H_exponents':list(map(str,H)),'per_outer':list(map(str,perouter)),'outer_R2':list(map(str,outer)),'outer_R0':list(map(str,outerR0)),'R2_arguments':[list(map(str,arg1)),list(map(str,arg2))],'status':'PASS'}
# Coupled gcd remains the theorem condition, not factored into a beta indicator.
gcdtest=0
for p in [5,7,11]:
 for h in range(1,101):
  assert (math.gcd(h,p*6)==1)==(math.gcd(h,6)==1 and h%p!=0);gcdtest+=1
out['coupled_gcd_bookkeeping']={'cases':gcdtest,'p_condition_retained':True,'status':'PASS'}
out['status']='PASS'
s=json.dumps(out,sort_keys=True,indent=2)+'\n';(ROOT/'CHECKS.json').write_text(s);print(s,end='')
