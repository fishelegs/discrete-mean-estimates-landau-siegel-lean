import json
import mpmath as mp
from math import gcd
mp.mp.dps=50
chars={3:{1:1,2:-1},4:{1:1,3:-1},5:{1:1,2:-1,3:-1,4:1},8:{1:1,3:-1,5:-1,7:1},12:{1:1,5:-1,7:-1,11:1}}
e=lambda x:mp.exp(2j*mp.pi*x)
def gauss(char,q):return sum(char(n)*e(mp.mpf(n)/q) for n in range(q))
def Z(tau,parity,q,s):return (1j)**(-parity)*tau*mp.pi**(s-mp.mpf('.5'))*q**(-s)*mp.gamma((1-s+parity)/2)/mp.gamma((s+parity)/2)
def gen(p):return next(g for g in range(2,p) if len({pow(g,j,p) for j in range(p-1)})==p-1)
def kl(v,p):return sum(e(mp.mpf(x+v*pow(x,-1,p))/p) for x in range(1,p))/mp.sqrt(p)
err=mp.mpf(0); cases=0
for D,res in chars.items():
 chi=lambda n:res.get(n%D,0)
 c=0 if chi(-1)==1 else 1
 tauchi=gauss(chi,D); epschi=tauchi/((1j)**c*mp.sqrt(D))
 err=max(err,abs(tauchi**2-chi(-1)*D))
 for p in (11,13,17):
  if gcd(p,D)>1:continue
  g=gen(p); logs={pow(g,j,p):j for j in range(p-1)}
  rows=[]
  for k in range(1,p-1):
   psi=lambda n,k=k:0 if n%p==0 else e(mp.mpf(k*logs[n%p])/(p-1))
   a=k%2; b=(a+c)%2
   taupsi=gauss(psi,p); tauprod=gauss(lambda n:chi(n)*psi(n),D*p)
   err=max(err,abs(tauprod-chi(p)*psi(D)*tauchi*taupsi))
   r=taupsi/((1j)**a*mp.sqrt(p))*tauprod/((1j)**b*mp.sqrt(D*p))
   rows.append((a,psi,r))
   for t in (mp.mpf('1.25'),mp.mpf('3.75')):
    s=mp.mpf('.5')+1j*t
    E=1 if c==0 else (-1j*mp.tan(mp.pi*s/2) if a==0 else 1j/mp.tan(mp.pi*s/2))
    lhs=Z(taupsi,a,p,s)/Z(tauprod,b,D*p,s)*D**(-s)*psi(D)
    rhs=tauchi*chi(p)/D*E
    err=max(err,abs(lhs-rhs));cases+=1
  for a in (0,1):
   group=[(psi,r) for aa,psi,r in rows if aa==a]; Na=len(group)
   ca=(-1)**(c*a+a)*chi(p)*epschi
   for v in range(1,p):
    lhs=sum(psi(v)/r for psi,r in group)/Na
    vd=v*pow(D,-1,p)%p
    rhs=mp.conj(ca)*(p-1)/(2*Na*mp.sqrt(p))*(kl(vd,p)+(-1)**a*kl((-vd)%p,p))
    if a==0:rhs-=mp.conj(ca)/(p*Na)
    err=max(err,abs(lhs-rhs));cases+=1
assert err < mp.mpf('1e-40')
print(json.dumps({'cases':cases,'maximum_absolute_error':str(err),'precision_digits':mp.mp.dps,'scope':'Finite sanity checks only; proofs are the CRT/gamma/orthogonality algebra in the reports.'},indent=2))
