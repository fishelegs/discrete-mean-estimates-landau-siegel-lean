from fractions import Fraction as F
from itertools import product
from math import gcd,prod
import pathlib,json,random
rng=random.Random(49117); ncases=0
for n in range(1,7):
 ps=[2,3,5,7,11,13][:n]; N=prod(p+1 for p in ps)
 for _ in range(40):
  cs=[(rng.randint(-5,5),rng.randint(-5,5)) for p in ps]
  lhs=0
  for bits in product([0,1],repeat=n):
   wt=prod(p if bit==0 else 1 for p,bit in zip(ps,bits))
   re=sum(c[0]*bit for c,bit in zip(cs,bits));im=sum(c[1]*bit for c,bit in zip(cs,bits))
   lhs+=wt*(re*re+im*im)
  mr=sum((F(c[0],p+1) for p,c in zip(ps,cs)),F(0));mi=sum((F(c[1],p+1) for p,c in zip(ps,cs)),F(0))
  variance=sum((F((c[0]**2+c[1]**2)*p,(p+1)**2) for p,c in zip(ps,cs)),F(0))
  assert lhs==N*(mr*mr+mi*mi+variance)
  assert lhs>=N*variance
  ncases+=1
def P1(q):
 units=[u for u in range(q) if gcd(u,q)==1]
 return {min(((u*a)%q,(u*b)%q) for u in units) for a in range(q) for b in range(q) if gcd(gcd(a,b),q)==1}
full=0
for ps,D in [([2,3],5),([2,3,5],7)]:
 q=prod(ps);cs=[(j+1,1-j) for j in range(len(ps))]; lhs=0;linear=[0,0]
 for a,b in P1(q):
  re=sum(c[0] for p,c in zip(ps,cs) if a%p==0);im=sum(c[1] for p,c in zip(ps,cs) if a%p==0)
  for c,d in P1(D):
   ch=0 if c*d%D==0 else (1 if pow(c*d,(D-1)//2,D)==1 else -1)
   lhs+=ch*ch*(re*re+im*im);linear[0]+=ch*re;linear[1]+=ch*im;full+=1
 N=prod(p+1 for p in ps);mr=sum((F(c[0],p+1) for p,c in zip(ps,cs)),F(0));mi=sum((F(c[1],p+1) for p,c in zip(ps,cs)),F(0));var=sum((F((c[0]**2+c[1]**2)*p,(p+1)**2) for p,c in zip(ps,cs)),F(0))
 assert lhs==(D-1)*N*(mr*mr+mi*mi+var) and linear==[0,0]
out={'status':'PASS','exact_complex_variance_cases':ncases,'full_projective_orbit_pairs':full,'proof_status':'Finite checks supplement pending independent source review; no actual-energy lower bound.'}
pathlib.Path(__file__).with_name('CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
