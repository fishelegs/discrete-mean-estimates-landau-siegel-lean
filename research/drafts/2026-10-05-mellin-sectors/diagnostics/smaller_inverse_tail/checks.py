#!/usr/bin/env python3
"""Finite unconditional identities and budgets; no numerical claim of A2022."""
import cmath
import json
import math
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
from sympy import divisors, kronecker_symbol, mobius, primitive_root

HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True,'exceptional_assumption_numerically_instantiated':False}
assert -2022+2+9==-2011
assert -2022+2+1==-2019
assert F(5,2)-F(8054,4)==-2011
assert F(5,2)-F(8086,4)==-2019
assert -F(2019,2)+8+288==-F(1427,2)
assert (324-F(1427,2))/2==-F(779,4)
assert (52-F(1427,2))/2==-F(1323,4)
assert -F(1427,2)-400==-F(2227,2)
assert -F(779,4)-400==-F(2379,4)
assert -F(1323,4)-400==-F(2923,4)
assert 594-400-F(779,4)==-F(3,4)
assert 730-400-F(1323,4)==-F(3,4)
assert 1113-400-F(1427,2)==-F(1,2)
assert 2*F(1,8)==F(1,4)
assert (F(1,4)-F(1,2))/4==-F(1,16)
out['exact_exponents']='PASS'

mp.mp.dps=40
pv_cases=0;fourier_cases=0;hyperbola_cases=0;linear_cases=0;square_cases=0;cauchy_cases=0
max_fourier=0.0
M=50000
tau=[0]*(M+1)
for d in range(1,M+1):
 for n in range(d,M+1,d):tau[n]+=1

for disc in [-3,5,8,12,13]:
 D=abs(disc);L=math.log(D);Q=2*math.sqrt(D)*(1+L)
 cp=[int(kronecker_symbol(disc,n)) for n in range(D)]
 ch=lambda n:cp[n%D]
 assert sum(cp)==0
 gauss=sum(mp.mpf(ch(n))*mp.exp(2j*mp.pi*n/D) for n in range(D))
 assert abs(abs(gauss)-mp.sqrt(D))<mp.mpf('1e-35')
 for x in range(D):
  rhs=gauss*sum(ch(-a)*mp.exp(2j*mp.pi*a*x/D) for a in range(D))
  err=abs(D*ch(x)-rhs)
  max_fourier=max(max_fourier,float(err));assert err<mp.mpf('1e-34')
  fourier_cases+=1
 for start in range(-D,D+1):
  for length in range(0,2*D+1):
   actual=abs(sum(ch(n) for n in range(start,start+length)))
   assert actual<=Q+1e-12
   pv_cases+=1
 nu=[0]*(M+1)
 for d in range(1,M+1):
  cd=ch(d)
  if cd:
   for n in range(d,M+1,d):nu[n]+=cd
 assert min(nu)>=0
 A=[0]*(M+1);H=[0.0]*(M+1);W=[0.0]*(M+1)
 for n in range(1,M+1):
  A[n]=A[n-1]+nu[n];H[n]=H[n-1]+nu[n]/n;W[n]=W[n-1]+nu[n]*nu[n]/n
 lam=float(-sum(ch(a)*mp.digamma(mp.mpf(a)/D) for a in range(1,D+1))/D)
 assert lam>0
 for N in [math.ceil(Q),2*math.ceil(Q),100,1000,5000]:
  if N<Q:continue
  for U in sorted(set([1,math.ceil(math.sqrt(Q*N)),N//2,N])):
   if not 1<=U<=N:continue
   error=abs(A[N]-lam*N)
   assert error<=U+2*Q*N/U+1e-8
   hyperbola_cases+=1
  assert abs(A[N]-lam*N)<=4*math.sqrt(Q*N)+1e-8
 for V in [math.ceil(Q)+1,100,1000,5000]:
  for N in [1000,10000,M]:
   if N<V:continue
   tail=H[N]-H[V]
   bound=lam*(1+math.log(N))+12*math.sqrt(Q/V)
   assert tail<=bound+1e-8
   linear_cases+=1
 for n in range(1,1500):
  conv=sum(nu[d]*nu[n//d] for d in divisors(n))
  assert nu[n]*nu[n]<=conv
  square_cases+=1
 for U in [5,20,50,100]:
  Z=U*U
  for N in [1000,10000,M]:
   if N<Z:continue
   assert W[N]-W[Z]<=2*H[N]*(H[N]-H[U])+1e-8
   square_cases+=1
 X=min(D**4,M);Z=D**1.5
 eps=sum(nu[d]**2/d for d in range(1,X+1) if d>Z)
 first=sum(nu[d]**2*tau[d]/d for d in range(1,X+1) if d>Z)
 second=sum(nu[d]**2*tau[d]**2/d for d in range(1,X+1))
 assert first*first<=eps*second+1e-8
 cauchy_cases+=1

out['primitive_PV_and_Fourier']={'interval_cases':pv_cases,'Fourier_cases':fourier_cases,'max_Fourier_error':max_fourier,'conductors':[3,5,8,12,13],'non_squarefree_primitive_conductors_included':True,'status':'PASS'}
out['optimized_hyperbola_and_linear_tail']={'hyperbola_cases':hyperbola_cases,'linear_tail_cases':linear_cases,'status':'PASS'}
out['nu_square_and_positive_tail']={'cases':square_cases,'status':'PASS'}
out['finite_endpoint_Cauchy']={'cases':cauchy_cases,'status':'PASS'}

# Exact complex finite inverse partition and the actual discarded coefficient majorant.
coeff_cases=0;max_partition=0.0
N=240
mu=[0]+[int(mobius(n)) for n in range(1,N+1)]
divs=[[]]+[list(divisors(n)) for n in range(1,N+1)]
def conv(a,b):return [0]+[sum(a[d]*b[n//d] for d in divs[n]) for n in range(1,N+1)]
ones=[0]+[1]*N
t2=[0]+[len(divs[n]) for n in range(1,N+1)]
t4=conv(t2,t2)
for disc in [-3,5,8,12]:
 D=abs(disc);X=min(D**4,N);Z=D**1.5
 ch=[0]+[int(kronecker_symbol(disc,n)) for n in range(1,N+1)]
 ups=conv(mu,[0]+[mu[n]*ch[n] for n in range(1,N+1)])
 nu=conv(ones,ch)
 beta=[.017j,-.023j,.031j]
 shifts=[[0]+[cmath.exp(-b*math.log(n)) for n in range(1,N+1)] for b in beta]
 ab=conv(conv(conv(shifts[0],shifts[1]),shifts[2]),ch)
 for v in [-1.3,0,.41]:
  z=.02+1j*v
  weighted=[0]+[ups[n]*cmath.exp(z*math.log(n)) if n<=X else 0 for n in range(1,N+1)]
  full=conv(weighted,ab)
  small=conv([0]+[weighted[n] if n<=Z else 0 for n in range(1,N+1)],ab)
  tail=conv([0]+[weighted[n] if n>Z else 0 for n in range(1,N+1)],ab)
  major=conv([0]+[nu[n] if Z<n<=X else 0 for n in range(1,N+1)],t4)
  radial=X**.02
  for k in range(1,N+1):
   error=abs(full[k]-small[k]-tail[k]);max_partition=max(max_partition,error)
   assert error<1e-10
   assert abs(tail[k])<=radial*major[k]+1e-10
   coeff_cases+=1
out['literal_finite_inverse_split']={'cases':coeff_cases,'max_partition_error':max_partition,'status':'PASS'}

# Explicit common-coefficient resonance with a fixed primitive nonprincipal character.
resonance=[]
for p in [7,11,13]:
 g=int(primitive_root(p));logs={pow(g,e,p):e for e in range(p-1)}
 j=1
 def psi(n):return 0j if n%p==0 else cmath.exp(2j*math.pi*j*logs[n%p]/(p-1))
 U=10*p;I=list(range(U+1,2*U+1));tc=7.3
 aa={n:psi(n).conjugate()*cmath.exp(1j*tc*math.log(n)) for n in I}
 harmonic=sum(abs(aa[n])**2/n for n in I)
 assert harmonic<=math.log(2)+.02
 positive=sum(1/math.sqrt(n) for n in I if n%p)
 for dt in [-.1,0,.1]:
  factor=sum(aa[n]*psi(n)*cmath.exp(-1j*(tc+dt)*math.log(n))/math.sqrt(n) for n in I)
  assert abs(factor)>=math.cos(.1*math.log(2))*positive-1e-11
  resonance.append({'p':p,'dt':dt,'factor_squared':abs(factor)**2,'harmonic_energy':harmonic})
out['fixed_character_resonance']=resonance
out['status']='PASS'
(HERE/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
