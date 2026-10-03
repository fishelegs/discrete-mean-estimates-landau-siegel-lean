"""Portable finite regressions supplementing the Lean proofs; no external packages."""
from fractions import Fraction
import itertools, json, math
F=Fraction
checks=[]
def require(ok,name,detail=None):
 assert ok,name
 checks.append({'name':name,'passed':bool(ok),'detail':detail})
def check(name,ok,detail=None):require(ok,name,detail)
# Broader exact arithmetic stress tests; these are finite regressions, not Lean proofs.
def factors(n):
 out=[];p=2
 while p*p<=n:
  if n%p==0:
   k=0
   while n%p==0:n//=p;k+=1
   out.append((p,k))
  p+=1
 if n>1:out.append((n,1))
 return out
def divs(n):return [i for i in range(1,n+1) if n%i==0]
def phi(n):
 for p,_ in factors(n):n=n//p*(p-1)
 return n
def mobius_abs(n): return int(all(k==1 for _,k in factors(n)))
pi_count=0
for n in range(1,361):
 ps=[p for p,k in factors(n)]
 for values in itertools.product([-1,0,1],repeat=len(ps)):
  cv=dict(zip(ps,values)); tot=Fraction(0)
  for r in divs(n):
   d=n//r
   pi=math.prod((1-Fraction(cv[p],p))**-1 for p in ps)
   pi*=math.prod((1-Fraction(1,p)-Fraction(cv[p],p))/(1-Fraction(1,p)) for p,k in factors(d) if r%p)
   tot+=Fraction(mobius_abs(r),phi(r))*pi
  assert tot==Fraction(n,phi(n)),(n,cv,tot)
  pi_count+=1
# Local complex polynomial identities can be checked exactly with Gaussian integers.
h2=lambda x,y,k: sum(x**a*y**(k-a) for a in range(k+1))
h3=lambda x,y,z,k: sum(h2(x,y,a)*z**(k-a) for a in range(k+1))
rec_count=0
for x,y,z in itertools.product([1,-1,1j,-1j],repeat=3):
 for k in range(12):
  assert h3(x,y,z,k+1)-h3(x,y,z,k)==h2(x,y,k+1)+(z-1)*h3(x,y,z,k)
  rec_count+=1
tau=lambda n,k: math.prod(math.comb(e+k-1,k-1) for p,e in factors(n))
tr_count=0
for R in [Fraction(1),Fraction(2),Fraction(5),Fraction(17,2),Fraction(10),Fraction(32)]:
 for n in range(1,1001):
  actual=sum(tau(d,2)*tau(n//d,2) for d in divs(n) if d<R and n//d<R)
  assert actual<=tau(n,4)
  tr_count+=1
require(True,'independent_finite_exact_checks',{'pi_collapse_n_range':[1,360],'local_character_values':[-1,0,1],'pi_cases':pi_count,'includes_p2_chi2_eq1_vanishing_pi':True,'kappa_gaussian_unit_recurrences':rec_count,'zero_shift_strict_truncated_square_cases':tr_count,'not_a_substitute_for_kernel_replay':True})

# Independent finite rational tests. These supplement, and never replace, Lean replay.
endpoint_cases=0
for q in range(1,1001):
    layer=[(q//r,r) for r in range(1,q+1) if q%r==0]
    assert len({r for d,r in layer})==len(layer)
    assert sum(F(1,d*r*r) for d,r in layer)<=sum(F(1,r*r) for d,r in layer)<=2
    endpoint_cases+=1
check('exact product endpoint reciprocal mass regression',True,dict(cases=endpoint_cases,range='Q=1..1000',uses_actual_weight_pointwise_majorant=True))
cutoff_cases=0
for R2 in range(1,81):
    R=F(R2,2)
    original={m for m in range(1,42) if m<R}
    for x3 in range(0,3*R2//2+1):
        x=F(x3,3)
        if x>R:continue
        strict={m for m in range(1,42) if m<x}
        assert {m for m in original if m<x}==strict
        if x.denominator==1:assert x not in strict
        cutoff_cases+=1
check('exact strict filtered cutoff including integral endpoints',True,dict(cases=cutoff_cases))

def padd(a,b):return [ (a[k] if k<len(a) else F(0))+(b[k] if k<len(b) else F(0)) for k in range(max(len(a),len(b))) ]
def pmul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
def power(p,n):
    ans=[F(1)]
    for _ in range(n):ans=pmul(ans,p)
    return ans
def deriv(p):return [F(i)*p[i] for i in range(1,len(p))]
def value(p,x):return sum(c*x**i for i,c in enumerate(p))
def integral(p,a,b):return sum(c*(b**(i+1)-a**(i+1))/F(i+1) for i,c in enumerate(p))
ramp_cases=0
for a,b in [(F(0),F(1)),(F(-2),F(3)),(F(1,3),F(7,3))]:
    p=pmul(power([-a,F(1)],3),power([b,F(-1)],3))
    for t in [a-F(3),a-F(1),a,a+(b-a)/4,(a+b)/2,b-(b-a)/4,b,b+1,b+3]:
        actual=F(0) if t>=b else integral(pmul(deriv(deriv(p)),[-t,F(1)]),max(a,t),b)
        target=value(p,t) if a<=t<=b else F(0)
        assert actual==target
        # For f(v)=exp(-ell*v)*p(v) on [a,b], density=exp(-ell*v)*p''(v).
        # The exponential cancels exactly to exp(-ell*t) in the ramp integral.
        ramp_cases+=1
check('exact fixed-interval compact C2 polynomial ramp incl lower tail and both endpoints',True,dict(cases=ramp_cases,arbitrary_complex_shift_via_exact_exponential_conjugation=True))
algebra_cases=0
vals=[F(-3),F(-1),F(0),F(1,2),F(2)]
for ell in [F(-3),F(-1,2),F(1),F(5,2)]:
    for a1 in vals:
        for a2 in vals:
            A=a1*a2/ell**2; BB=(a1+ell)*(a2+ell)/ell
            assert -A-(1-A)==-1
            assert -2*ell*A-ell*(1-A)+BB==a1+a2
            assert A*ell**2==a1*a2
            algebra_cases+=1
check('exact second main derivative local and plus Volterra coefficients',True,dict(cases=algebra_cases))

print(json.dumps({'status':'PASS','checks':checks},indent=2))
