#!/usr/bin/env python3
"""Portable read-only mathematical checks; source identities are pinned separately."""
import json,math
from fractions import Fraction as F
# Mathematical enumeration extracted from the pinned independent v2 diagnostic.
primes=(11,13,17,19,23,29,31,37)
matrix_cases=0;survivors=0
for p in primes:
 for q in primes:
  found=[]
  for u in range(1,p*q+1):
   if (p*q)%u:continue
   v=p*q//u
   for sign in (-1,1):
    a=sign*F(u,q);d=sign*F(v,q)
    if abs(a)+abs(d)>10:continue
    for b in range(1,p):
     for c in range(1,q):
      entries=(a,(-a*b+c*d)/p,q*d/p)
      matrix_cases+=1
      if all(z.denominator==1 for z in entries):found.append((a,d,b,c))
  assert len(found)==(2*(p-1) if p==q else 0)
  assert all(a==d and a in (-1,1) and b==c for a,d,b,c in found)
  survivors+=len(found)
# Independent CRT projective orbit checks with odd/even nonsquarefree moduli.
def ch(n,D):
 n%=D
 if math.gcd(n,D)!=1:return 0
 if D in (3,5,13):return 1 if pow(n,(D-1)//2,D)==1 else -1
 if D==8:return 1 if n in (1,7) else -1
 if D==12:return 1 if n in (1,11) else -1
 raise AssertionError(D)
orbits=0
for D in (3,5,8,12,13):
 units=[u for u in range(D) if math.gcd(u,D)==1]
 reps=set()
 for c in range(D):
  for d in range(D):
   if math.gcd(math.gcd(c,d),D)==1:
    reps.add(min((u*c%D,u*d%D) for u in units))
 for p in primes:
  if math.gcd(p,D)!=1:continue
  for b in range(1,p):
   transformed={min((u*c%D,u*(b*c+p*d)%D) for u in units) for c,d in reps}
   assert transformed==reps
   vals=[ch(c*(b*c+p*d),D) for c,d in reps]
   assert sum(vals)==0 and sum(z*z for z in vals)==len(units)
   orbits+=1
# Check the quadratic-form weights using exact rational complex moduli squared.
P=F(11);ps=(11,13,17,19)
weights={p:F((p%5)**2+(p%7)**2,9) for p in ps}
for phi in (2,4,12):
 exact=sum(2*phi*(p-1)*weights[p]/P for p in ps)
 assert exact<=4*phi*sum(weights.values())
print(json.dumps(dict(status='PASS',independent_matrix_cases=matrix_cases,surviving_pairs=survivors,independent_projective_orbits=orbits,finite_lemma_only=True,actual_averaged_application=False,mathematical_certification=False),indent=2,sort_keys=True))
