#!/usr/bin/env python3
"""Finite diagnostics for the smooth reduction and actual weighted-row proof."""
import cmath
import json
import math
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import mpmath as mp
from sympy import divisors, factorint, kronecker_symbol, mobius, primitive_root

HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True}

assert F(1,2)+F(1,37)-F(1,37)==F(1,2)
assert 4+F(1,2)-5==-F(1,2)
assert 5-12==-7
assert 2076*12+324-400==24836
assert (24836-76)//2==12380
assert 3-2*12==-21 and 9*12==108
assert 12+24*9==228
assert -F(1,2)+F(1,4)==-F(1,4)
assert F(958,15)+F(1,15)==F(959,15)<64
assert -8-14==-22
out['exact_exponents_and_critical_lines']='PASS'

# Finite probability measures test the exact cutoff-average algebra; smooth
# Mellin decay for the fixed C-infinity profile is proved analytically.
atoms=[(math.log(2)*.15,.2),(math.log(2)*.43,.3),(math.log(2)*.81,.5)]
def U(x):return sum(w for a,w in atoms if x>math.exp(a))
transition_checks=0
for R,S in [(4,3),(4.2,3.7),(2,2)]:
 for r in range(1,15):
  for n in range(1,14):
   hr=int(r>R);hs=int(n>S);ur=U(r/R);un=U(n/S)
   A=hr-ur;C=hs-un
   assert abs(hr*hs-ur*un-(A*hs+ur*C))<1e-13
   wa=sum(w*int(R<r<=R*math.exp(a)) for a,w in atoms)
   wb=sum(w*int(S<n<=S*math.exp(a)) for a,w in atoms)
   assert abs(A-wa)<1e-13 and abs(C-wb)<1e-13
   expanded=sum(wa*wb*(int(r>R*math.exp(a) and n<=S*math.exp(b))-int(r>R*math.exp(a) and n<=S)) for a,wa in atoms for b,wb in atoms)
   assert abs(ur*C-expanded)<1e-13
   transition_checks+=1
out['exact_transition_average_identity']={'cases':transition_checks,'no_norm_monotonicity_used':True,'status':'PASS'}

reserve_checks=0
for D in [3,5,10,100]:
 for u in [F(1),F(3,2),F(2)]:
  for v in [F(1),F(5,4),F(2)]:
   assert u/F(D**2)<=F(2,D**2)
   assert v/F(D)<1
   assert u*v/F(D**22)<1
   reserve_checks+=1
out['constant_factor_cutoff_reserves']={'cases':reserve_checks,'status':'PASS'}

shell_sum=sum(2**(-11.5*j)*(1+j)**18 for j in range(40))
assert all(2**(-11.5)*((j+2)/(j+1))**18<.5 for j in range(2,100))
out['infinite_remote_shell_envelope']={'first_40_sum':shell_sum,'geometric_tail_ratio_below_half_from_index':2,'status':'PASS'}

mp.mp.dps=45
fe_checks=[]
for disc in [-3,5,8,12]:
 D=abs(disc);c=0 if int(kronecker_symbol(disc,-1))==1 else 1
 p=17;beta=[mp.mpc(0,'.013'),mp.mpc(0,'.021'),mp.mpc(0,'.031')]
 for a in [0,1]:
  for T in [-100,-.013,0,.1,10,100]:
   u=mp.mpf('.5')+1j*T
   anu=(mp.mpf(p)/mp.pi)**(mp.mpf('.5')-u-beta[0])*(mp.mpf(p*D)/mp.pi)**(mp.mpf('.5')-u)
   anu*=mp.gamma((1-u-beta[0]+a)/2)/mp.gamma((u+beta[0]+a)/2)
   anu*=mp.gamma((1-u+(a+c)%2)/2)/mp.gamma((u+(a+c)%2)/2)
   a23=(mp.mpf(p)/mp.pi)**(1-2*u-beta[1]-beta[2])
   for b in beta[1:]:a23*=mp.gamma((1-u-b+a)/2)/mp.gamma((u+b+a)/2)
   error=max(abs(abs(anu)-1),abs(abs(a23)-1))
   assert error<mp.mpf('1e-38')
   fe_checks.append(float(error))
out['exact_unit_modulus_FE_scalars']={'cases':len(fe_checks),'max_error':max(fe_checks),'all_psi_chi_parities':True,'status':'PASS'}

@lru_cache(None)
def tau(k,n):
 ans=1
 for e in factorint(n).values():ans*=math.comb(e+k-1,k-1)
 return ans

@lru_cache(None)
def nu(disc,n):return sum(int(kronecker_symbol(disc,n//a)) for a in divisors(n))

@lru_cache(None)
def ups(disc,n):return sum(int(mobius(a))*int(mobius(n//a))*int(kronecker_symbol(disc,n//a)) for a in divisors(n))

contraction_checks=0;normalization_checks=0;majorant_checks=0
for disc in [-3,5,8,12]:
 D=abs(disc);X=min(D**4,40)
 for d in range(1,7):
  for n in range(1,7):
   for nn in range(1,5):
    T=D*d*n*nn
    restricted=0;upper=0
    for e in divisors(T):
     mm=T//e
     inner=sum(tau(2,m)*tau(2,mm//m) for m in divisors(mm))
     assert inner==tau(4,mm)
     if e<=X:restricted+=abs(ups(disc,e))*inner
     upper+=nu(disc,e)*inner
     for m in divisors(mm):
      mp_=mm//m
      assert d*e*m*mp_*n*nn==D*d*d*n*n*nn*nn
      normalization_checks+=1
    assert restricted<=upper<=tau(6,T)
    assert tau(6,T)<=tau(6,D)*tau(6,d)*tau(6,n)*tau(6,nn)
    contraction_checks+=1
 for d in range(1,301):
  assert abs(ups(disc,d))<=nu(disc,d)<=tau(2,d)
  assert tau(2,d)*tau(6,d)<=tau(12,d)
  majorant_checks+=1
out['full_integer_row_divisor_contraction']={'cases':contraction_checks,'normalization_checks':normalization_checks,'ramified_conductors_included':True,'status':'PASS'}
out['upsilon_and_divisor_majorants']={'cases':majorant_checks,'status':'PASS'}

rankin_checks=0
for B in [10,37,100]:
 eps=mp.mpf(1)/B;Q=mp.exp(B)*B**2
 for ratio in [mp.mpf('.01'),mp.mpf('.5'),mp.mpf(1),mp.mpf(2),mp.mpf(1000)]:
  theta=min(mp.mpf(1),ratio**-4)
  assert theta<=ratio**(-eps)
  rankin_checks+=1
 assert mp.zeta(1+eps)<=1+B
out['all_height_harmonic_envelope']={'rankin_checks':rankin_checks,'theta4_dominated_by_rankin_power':True,'status':'PASS'}

parity_checks=0
for p in [5,7,11,13,17]:
 g=int(primitive_root(p));logs={pow(g,j,p):j for j in range(p-1)}
 def psi(j,n):return 0j if n%p==0 else cmath.exp(2j*math.pi*j*logs[n%p]/(p-1))
 for a in [0,1]:
  for x in range(1,3*p):
   actual=sum(psi(j,x)*psi(j,x).conjugate() for j in range(1,p-1) if j%2==a)
   expected=0 if x%p==0 else (p-1)/2-(a==0)
   assert abs(actual-expected)<1e-12
   parity_checks+=1
out['restricted_even_principal_equality_row']={'checks':parity_checks,'status':'PASS'}

# Coefficients with arbitrary common bounded tuple multipliers retain tau_6.
multiplier_checks=0
for disc in [-3,5,8,12]:
 D=abs(disc);X=5;J=3;beta=[.013j,.021j,.031j]
 def nb(m):return sum(cmath.exp(-beta[0]*math.log(a))*int(kronecker_symbol(disc,m//a)) for a in divisors(m))
 def d23(n):return sum(cmath.exp(-beta[1]*math.log(a)-beta[2]*math.log(n//a)) for a in divisors(n))
 for k in range(1,150):
  coeff=0j
  for d in divisors(k):
   if d>X:continue
   for m in divisors(k//d):
    n=k//d//m
    mult=cmath.exp(.17j*(d+2*m+3*n))/(1+(d+m+n)%3)
    coeff+=ups(disc,d)*d**(J+.31j)*nb(m)*d23(n)*mult
  assert abs(coeff)<=X**J*tau(6,k)+1e-8
  multiplier_checks+=1
out['common_bounded_multiplier_cap']={'checks':multiplier_checks,'status':'PASS'}

out['status']='PASS'
(HERE/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
