import math,cmath,json,random
from fractions import Fraction as F
from pathlib import Path
root=Path(__file__).resolve().parent;random.seed(20261005)
counts={};errors={}
def ex(t):return cmath.exp(2j*math.pi*t)
def ck(name,a,b,tol=1e-9):
 err=abs(a-b);counts[name]=counts.get(name,0)+1;errors[name]=max(errors.get(name,0),float(err));assert err<=tol*(1+abs(a)+abs(b)),(name,a,b)
for p in [3,5,7,11,17]:
 w=[0]+[complex(random.uniform(-1,1),random.uniform(-1,1)) for a in range(1,p)]
 W=[sum(w[a]*ex(-j*a/p) for a in range(p)) for j in range(p)]
 for m in range(1,2*p):
  if m%p==0:continue
  inv=pow(m,-1,p)
  for l in range(1,2*p):
   if l%p==0:continue
   for eps in [0,1]:
    lhs=sum(w[a]*((p-1)/2*((m*a-l)%p==0)+(p-1)/2*(-1)**eps*((m*a+l)%p==0)-(eps==0)) for a in range(1,p))
    rhs=(p-1)/(2*p)*sum((ex(j*l*inv/p)+(-1)**eps*ex(-j*l*inv/p))*W[j] for j in range(p))-(eps==0)*W[0]
    ck('projected_prime_Poisson_both_parities',lhs,rhs)
   for j in [1,-1,p-1]:
    if math.gcd(m,p)==1:
     invp=pow(p,-1,m) if m>1 else 0
     ck('exact_additive_reciprocity',ex(j*l*inv/p),ex(j*l/(m*p))*ex(-j*l*invp/m))
    assert ((j*l)%p==0)==(l%p==0)
    counts['alias_p_unit_equivalence']=counts.get('alias_p_unit_equivalence',0)+1
 for eps in [0,1]:
  ck('exact_zero_mode_centering',(p-1)/(2*p)*(1+(-1)**eps)-(eps==0),-(eps==0)/p)
 for m in range(2,2*p):
  if math.gcd(m,p)>1:continue
  for c in range(1,10):
   ck('excluded_alias_phase',ex(p*c*pow(p,-1,m)/m),ex(c/m))
def divs(n):return [d for d in range(1,n+1) if n%d==0]
def mu(n):
 k=0;p=2
 while p*p<=n:
  if n%p==0:
   n//=p;k+=1
   if n%p==0:return 0
   while n%p==0:n//=p
  p+=1
 if n>1:k+=1
 return (-1)**k
chi=lambda n:{1:1,2:-1,3:-1,4:1}.get(n%5,0)
u=lambda d:sum(mu(v)*mu(d//v)*chi(d//v) for v in divs(d))
B1=.07j;B2=-.03j;B3=.02j;alpha=.03;en=alpha+.04j;e23=alpha-.02j;wn=-alpha+.03j;X=6
nu=lambda n:sum(a**(-B1)*chi(n//a) for a in divs(n))
d23=lambda n:sum(a**(-B2)*(n//a)**(-B3) for a in divs(n))
def grouped(m):
 total=0j
 for d in divs(m):
  if d>X:continue
  rem=m//d
  for a2 in divs(rem):
   for a3 in divs(rem//a2):
    a4=rem//a2//a3
    total+=u(d)*d**(-wn)*chi(a2)*a2**(-en)*a3**(-B2-e23)*a4**(-B3-e23)
 return total
for k in range(1,101):
 original=sum(u(d)*d**(-wn)*nu(m)*m**(-en)*d23(k//d//m)*(k//d//m)**(-e23) for d in divs(k) if d<=X for m in divs(k//d))
 restored=sum(grouped(k//a)*a**(-B1-en) for a in divs(k))
 ck('literal_finite_inverse_factor_opening',original,restored)
add=lambda *v:tuple(sum(x[i] for x in v) for i in range(3))
sc=lambda a,v:tuple(a*x for x in v)
P=(F(1),0,0);T=(0,0,F(1));J=(F(1,2),F(1,4),F(1,2));B=(F(3,2),F(1,4),F(3,2));x=(F(2),F(1,2),F(2))
R=add(P,T,sc(-1,J));A=add(R,x);assert A==(F(5,2),F(1,4),F(5,2))
normal=add(sc(F(1,2),P),sc(F(1,2),B),sc(F(1,2),A),J,sc(-1,x),sc(F(1,2),add(A,sc(-1,P),sc(-1,B))))
t1=add(sc(F(7,20),add(A,P,B)),sc(F(1,4),B));t2=add(sc(F(3,8),add(A,P,B)),sc(F(1,8),add(A,B)))
assert add(normal,t1)==(F(25,8),F(19,80),F(111,40))
assert add(normal,t2)==(F(27,8),F(1,4),F(3))
counts['BC_full_normalization_equalities']=3
terms=[-F(1,2)/8,F(1,8)+F(1,2)/8-F(1,4),F(1,10)-F(3,20)-F(5,2)/20-F(1,2)*F(3,20),F(1,2)*F(3,20)-F(5,2)*F(3,20)-F(1,5),F(1,2)*F(3,8)-F(1,2)]
assert terms==[-F(1,16),-F(1,16),-F(1,4),-F(1,2),-F(5,16)]
assert F(1,2)+max(terms)==F(7,16)
counts['Wright_fixed_factor_exponents']=6
out={'status':'PASS','scope':'Exact coefficient/Poisson/reciprocity/principal identities and theorem ledgers; no target estimate','counts':counts,'total_checks':sum(counts.values()),'maximum_absolute_errors':errors,'strict_gap':'OPEN'}
(root/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
