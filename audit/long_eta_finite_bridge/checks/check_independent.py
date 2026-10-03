#!/usr/bin/env python3
"""Independent finite regression evidence, never an analytic certificate."""
from fractions import Fraction as F
from pathlib import Path
from math import comb, gcd, lcm
import json
import sympy as sy
import mpmath as mp

OUT = Path(__file__).resolve().parent

import argparse
_parser = argparse.ArgumentParser(description=__doc__)
_parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'results' / 'INDEPENDENT_RERUN.json')
_OUTPUT = _parser.parse_args().output
_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
I = (0, 1)
ONE = (1, 0)
ZERO = (0, 0)
def add(x,y): return (x[0]+y[0], x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def mul(x,y): return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def power(x,n):
    y=ONE
    for _ in range(n): y=mul(y,x)
    return y
def summ(xs):
    y=ZERO
    for x in xs:y=add(y,x)
    return y
def factors(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=1
    return out
def mobius(n):
    fs=factors(n)
    return 0 if 2 in [min(2,v) for v in fs.values()] else (-1)**len(fs)
def divs(n):return [d for d in range(1,n+1) if n%d==0]
def tau(k,n):return sy.prod(comb(e+k-1,k-1) for e in factors(n).values())
counts={"local_euler":0,"truncated_tail":0,"ramified_deletion":0,"gauss_exact":0,"divisor":0,"fourier_numeric":0}

# Prime-local formal Euler series, including ramified chi(l)=0.
for c in [-1,0,1]:
  for alpha in [ONE,I,(-1,0),(0,-1)]:
    aa=[power(alpha,j) for j in range(16)]
    eta=[aa[0]]+[add(aa[j],neg(aa[j-1])) for j in range(1,16)]
    nu=[sum(c**k for k in range(j+1)) for j in range(16)]
    for j in range(16):
      lhs=summ(mul(eta[k],(nu[j-k],0)) for k in range(j+1))
      rhs=summ(mul(aa[k],(c**(j-k),0)) for k in range(j+1))
      assert lhs==rhs
      counts["local_euler"]+=1

tables={3:[0,1,-1],4:[0,1,0,-1],5:[0,1,-1,-1,1],8:[0,1,0,-1,0,-1,0,1]}
limit=150
for D,tab in tables.items():
  chi=lambda n:tab[n%D]
  nu=lambda n:sum(chi(e) for e in divs(n))
  inv=lambda n:sum(mobius(d)*mobius(n//d)*chi(n//d) for d in divs(n))
  alpha=lambda n:power(I,sum((p%4)*e for p,e in factors(n).items()))
  eta=lambda n:summ(mul((mobius(d),0),alpha(n//d)) for d in divs(n))
  for n in range(1,limit+1):
    full=summ(mul((chi(e),0),alpha(n//e)) for e in divs(n))
    for X in [2,5,13,37]:
      short=summ(mul(eta(n//e),(nu(e),0)) for e in divs(n) if e<=X)
      tail=summ(mul(eta(n//e),(nu(e),0)) for e in divs(n) if e>X)
      assert add(short,tail)==full
      counts["truncated_tail"]+=1
    # Exact deletion coefficient at multiples of D, with nonsquarefree D.
    expected=mobius(D)*inv(n) if gcd(n,D)==1 else 0
    assert inv(D*n)==expected
    counts["ramified_deletion"]+=1

# Exact cyclotomic arithmetic verifies primitive Gauss products, no float roots.
z=sy.Symbol('z')
def gauss_poly(p,k,D,tab,conjugate=False):
    q=p*D;N=lcm(q,p-1);g=sy.primitive_root(p)
    logs={pow(int(g),j,p):j for j in range(p-1)}
    cs={}
    for x in range(q):
        if x%p==0:continue
        c=tab[x%D]
        if not c:continue
        a=((N//q)*x+(N//(p-1))*(-k if conjugate else k)*logs[x%p])%N
        cs[a]=cs.get(a,0)+c
    return sy.Poly.from_dict({(a,):c for a,c in cs.items()},z),N
for p in [5,7,13]:
  for k in [1,2,p-2]:
    for D,tab in {1:[1],**tables}.items():
      if gcd(p,D)>1:continue
      g,N=gauss_poly(p,k,D,tab)
      gb,_=gauss_poly(p,k,D,tab,True)
      parity=(-1)**k*tab[-1%D]
      remainder=sy.rem(g*gb-sy.Poly(parity*D*p,z),sy.Poly(sy.cyclotomic_poly(N,z),z))
      assert remainder.is_zero,(p,k,D)
      counts["gauss_exact"]+=1

for n in range(1,301):
  for a,b in [(2,2),(2,3),(3,3),(4,9),(5,5),(6,6)]:
    assert tau(a,n)*tau(b,n)<=tau(a*b,n)
    counts["divisor"]+=1
for a in range(1,51):
  for b in range(1,51):
    for j in [2,3]:
      assert tau(j,a*b)<=tau(j,a)*tau(j,b)
      counts["divisor"]+=1

budgets={}
budgets['two_error_energy']=F(108)+F(27)-F(2011,2)+F(9*36,2)
budgets['two_per_box']=77+(225+budgets['two_error_energy'])/2
budgets['two_aggregate']=budgets['two_per_box']+27
budgets['three_error_energy']=F(72)-F(2011,2)+F(9*16,2)
budgets['three_per_box']=77+(324+budgets['three_error_energy'])/2
budgets['three_aggregate']=budgets['three_per_box']+36
assert budgets['two_aggregate']==-F(551,4)
assert budgets['three_aggregate']==-F(623,4)
assert -2+F(2,8)==-F(7,4) # two-completion length margin
assert -2+F(3,8)==-F(13,8) # three-completion length margin
assert F(201,400)-F(251,500)==F(1,2000)

# Both Fourier signs. This is a change-of-variables regression at moderate t;
# uniformity for actual t~L^519 is proved analytically in INDEPENDENT_REVIEW.md.
mp.mp.dps=55
def phi(v):return (v-1)**6*(2-v)**6 if 1<v<2 else mp.mpf(0)
worst=mp.mpf(0)
for q,R,t,h in [(17,8,11,3),(104,19,27,9),(91,24,53,7)]:
  q,R,t,h=map(mp.mpf,(q,R,t,h));y=2*mp.pi*h*R/(q*t)
  for sign in [-1,1]:
    lhs=mp.quad(lambda x:x**(-mp.mpf('.5')+1j*t)*phi(x/R)*mp.exp(-2j*mp.pi*sign*h*x/q),[R,mp.mpf('1.5')*R,2*R])/mp.sqrt(q)
    vv=mp.sqrt(t/(2*mp.pi))*mp.quad(lambda zz:zz**(-mp.mpf('.5'))*phi(zz/y)*mp.exp(1j*t*(mp.log(zz)-sign*zz+1)),[y,mp.mpf('1.5')*y,2*y])
    rhs=h**(-mp.mpf('.5'))*mp.exp(1j*t*mp.log(q*t/(2*mp.pi*mp.e*h)))*vv
    err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs));worst=max(worst,err)
    assert err<mp.mpf('1e-45')
    counts['fourier_numeric']+=1
result={'status':'PASS','scope':'Finite exact algebra and accounting plus moderate-height numerical change-of-variable checks only. Not a stationary-phase proof or sign theorem.','counts':counts,'budgets':{k:str(v) for k,v in budgets.items()},'max_fourier_relative_error':str(worst)}
_OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
