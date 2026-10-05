from fractions import Fraction as F
from math import gcd
import json,pathlib
ps=[11,13,17,19,23]; cases=0
for p in ps:
 for q in ps:
  surviving=0
  for u in range(1,p*q+1):
   if p*q%u:continue
   v=p*q//u
   for sign in [-1,1]:
    a,d=sign*F(u,q),sign*F(v,q)
    if abs(a)+abs(d)>10:continue
    for b1 in range(1,p):
     for b2 in range(1,q):
      # sigma(q,b2)*diag(a,d)*inverse(sigma(p,b1))
      entries=[a,(-a*b1+b2*d)/p,F(0),q*d/p]
      cases+=1
      if all(x.denominator==1 for x in entries):surviving+=1
  assert surviving==(2*(p-1) if p==q else 0),(p,q,surviving)
def chi(n,D):
 n%=D
 if gcd(n,D)>1:return 0
 if D in (3,5,13):return 1 if pow(n,(D-1)//2,D)==1 else -1
 if D==8:return 1 if n in (1,7) else -1
 if D==12:return 1 if n in (1,11) else -1
 raise ValueError
orbits=0
for D in [3,5,8,12,13]:
 units=[u for u in range(D) if gcd(u,D)==1]
 reps=set()
 for c in range(D):
  for d in range(D):
   if gcd(gcd(c,d),D)==1:reps.add(min(((u*c)%D,(u*d)%D) for u in units))
 assert sum(chi(c*d,D) for c,d in reps)==0
 assert sum(chi(c*d,D)**2 for c,d in reps)==len(units)
 for p in ps:
  if gcd(p,D)>1:continue
  for b in range(1,p):
   vals=[chi(c*(b*c+p*d),D) for c,d in reps]
   assert sum(vals)==0 and sum(v*v for v in vals)==len(units)
   orbits+=1
out={'status':'PASS','representative_matrix_cases':cases,'transformed_projective_orbits':orbits,'proof_status':'Finite diagnostics only; independent analytic review pending'}
pathlib.Path(__file__).with_name('CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
