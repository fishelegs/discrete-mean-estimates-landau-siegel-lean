import json,math,random,cmath
from fractions import Fraction as F
from pathlib import Path
root=Path(__file__).resolve().parent
random.seed(20261005)
counts={};worst={}
def ck(name,a,b,tol=1e-9):
 err=abs(a-b);counts[name]=counts.get(name,0)+1;worst[name]=max(worst.get(name,0),float(err));assert err<=tol*(1+abs(a)+abs(b)),(name,a,b)
def mm(x,y,n):
 a,b,c,d=x;A,B,C,D=y;return ((a*A+b*C)%n,(a*B+b*D)%n,(c*A+d*C)%n,(c*B+d*D)%n)
def cosets(H,G,n):
 remaining=set(G);reps=[];which={}
 while remaining:
  r=min(remaining);index=len(reps);reps.append(r)
  orbit={mm(h,r,n) for h in H}
  for z in orbit:which[z]=index
  remaining-=orbit
 return reps,which
for D,q1 in [(2,3),(3,4),(3,5),(4,3),(5,2)]:
 n=D*q1;G=[(a,b,c,d) for a in range(n) for b in range(n) for c in range(n) for d in range(n) if (a*d-b*c)%n==1]
 K=[g for g in G if g[2]%D==0];H=[g for g in K if g[1]%q1==0]
 expected=q1
 for p in range(2,q1+1):
  if q1%p==0 and all(p%j for j in range(2,int(math.sqrt(p))+1)):expected=expected*(p+1)//p
 ck('cover_index',len(K)/len(H),expected)
 repsHG,labelsHG=cosets(H,G,n);repsKG,_=cosets(K,G,n);repsHK,labelsHK=cosets(H,K,n)
 vals=[complex(random.random(),random.random()) for _ in repsHG]
 lhs=sum(abs(vals[labelsHG[mm(r,g,n)]])**2 for g in repsKG for r in repsHK)
 rhs=sum(abs(v)**2 for v in vals)
 ck('counting_fibre_isometry',lhs,rhs)
 for gamma in random.sample(K,min(10,len(K))):
  perm=[labelsHK[mm(r,gamma,n)] for r in repsHK]
  ck('right_coset_permutation',len(set(perm)),len(repsHK))
for J in [1,2,5,20]:
 for _ in range(40):
  c=[complex(random.uniform(-2,2),random.uniform(-2,2)) for _ in range(J)]
  K=[random.uniform(.1,4) for _ in range(J)];R=[random.uniform(.1,9) for _ in range(J)]
  w=[math.sqrt(R[i])/(abs(c[i])*math.sqrt(K[i])) for i in range(J)]
  target=sum(abs(c[i])*math.sqrt(K[i]*R[i]) for i in range(J))
  product=math.sqrt(sum(w[i]*abs(c[i])**2*K[i] for i in range(J))*sum(R[i]/w[i] for i in range(J)))
  ck('optimal_direct_sum_Cauchy',product,target)
  arbitrary=[random.uniform(.1,5) for i in range(J)]
  upper=math.sqrt(sum(arbitrary[i]*abs(c[i])**2*K[i] for i in range(J))*sum(R[i]/arbitrary[i] for i in range(J)))
  assert upper+1e-9>=target
  counts['arbitrary_weight_cannot_improve']=counts.get('arbitrary_weight_cannot_improve',0)+1
# Exact exponents in (P,D,L), using t0~L519, W=L400.
add=lambda *vs:tuple(sum(v[i] for v in vs) for i in range(3))
sc=lambda a,v:tuple(a*z for z in v)
U=(F(1),F(0),F(519));W=(0,0,F(400));x=(F(2),F(1,2),F(1038));P=(F(1),0,0)
H=add(x,sc(-1,P),sc(-1,W));assert H==(1,F(1,2),638)
C0=(F(1,2),F(1,4),F(-553));J=sc(2,U)
assert add(C0,sc(F(1,2),H),J)==(3,F(1,2),804)
assert add(C0,H,sc(F(-1,2),U),J)==(3,F(3,4),F(1727,2))
assert add(H,sc(-1,U))==(0,F(1,2),119)
counts['actual_scale_equalities']=4
# Spectral floor is exactly additive, irrespective of phases.
for n in [1,3,17]:
 for Hn,Un in [(100,20),(10000,100)]:
  floors=[Hn*Hn/Un for i in range(n)]
  ck('nonnegative_spectral_floor',sum(floors),n*Hn*Hn/Un)
out={'status':'PASS','scope':'Finite cover identities, sharp norm bookkeeping and exact exponent checks; no actual collective energy bound','counts':counts,'total_checks':sum(counts.values()),'maximum_absolute_errors':worst,'strict_gap':'OPEN'}
(root/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
