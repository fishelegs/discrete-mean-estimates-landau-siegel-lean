"""Read-only finite variance, projective-action and representative diagnostics."""
from fractions import Fraction as F
from itertools import product
from math import prod,gcd
import json
variance_cases=0
for n in range(1,7):
 ps=(2,3,5,7,11,13)[:n];N=prod(p+1 for p in ps)
 for seed in range(61):
  cs=[((seed*(j+3)+j)%13-6,(seed*(j+7)+2*j)%11-5) for j in range(n)]
  lhs=0
  for bits in product((0,1),repeat=n):
   multiplicity=prod(1 if b else p for p,b in zip(ps,bits))
   re=sum(c[0]*b for c,b in zip(cs,bits));im=sum(c[1]*b for c,b in zip(cs,bits))
   lhs+=multiplicity*(re*re+im*im)
  meanre=sum(F(c[0],p+1) for p,c in zip(ps,cs));meanim=sum(F(c[1],p+1) for p,c in zip(ps,cs))
  var=sum(F(p*(c[0]**2+c[1]**2),(p+1)**2) for p,c in zip(ps,cs))
  assert lhs==N*(meanre**2+meanim**2+var) and lhs>=N*var
  variance_cases+=1
# Explicit projective GL2 action checks, including composite moduli.
def P1(q):
 U=[u for u in range(q) if gcd(u,q)==1]
 return U,{min((u*a%q,u*b%q) for u in U) for a in range(q) for b in range(q) if gcd(gcd(a,b),q)==1}
actions=0
for q in (4,5,8,12,15,21):
 U,rows=P1(q)
 for p in (11,13,17):
  if gcd(p,q)!=1:continue
  for b in range(1,p):
   image={min((u*a%q,u*(a*b+c*p)%q) for u in U) for a,c in rows}
   assert image==rows;actions+=1
# Equal-prime g=+-I has only matching primitive-column reps.
pairs=0
for p in (11,13,17,19):
 for a,b in product(range(1,p),repeat=2):
  assert (F(b-a,p).denominator==1)==(a==b);pairs+=1
print(json.dumps(dict(status='PASS',exact_complex_variance_cases=variance_cases,projective_GL_actions=actions,equal_prime_pair_cases=pairs,off_prime_vanishing_assumed=False,actual_energy_lower_bound=False,mathematical_certification=False),indent=2,sort_keys=True))
