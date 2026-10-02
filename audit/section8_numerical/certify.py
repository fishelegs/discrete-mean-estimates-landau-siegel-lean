"""Exact-rational rectangular interval + Taylor certificate.
No floating point enters any bound. Bounds enclose model integrals, NOT original
character sums. The analytic approximation bridges are separate proof obligations.
"""
from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path

class R:
 def __init__(self,a=0,b=None):
  if isinstance(a,R): self.a,self.b=a.a,a.b; return
  self.a=F(a); self.b=self.a if b is None else F(b)
  assert self.a<=self.b
 def __add__(self,o):
  o=R(o);return R(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return R(-self.b,-self.a)
 def __sub__(self,o):return self+-R(o)
 def __rsub__(self,o):return R(o)+-self
 def __mul__(self,o):
  o=R(o);p=[x*y for x in [self.a,self.b] for y in [o.a,o.b]];return R(min(p),max(p))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=R(o);assert o.a*o.b>0;return self*R(1/o.b,1/o.a)
 def __rtruediv__(self,o):return R(o)/self
 def __pow__(self,n):
  assert n>=0;r=R(1)
  for _ in range(n):r=r*self
  return r
 def mag(self):return max(abs(self.a),abs(self.b))
 def inflate(self,e):return R(self.a-e,self.b+e)

class C:
 def __init__(self,a=0,b=0):
  if isinstance(a,C): self.r,self.i=a.r,a.i;return
  self.r,self.i=R(a),R(b)
 def __add__(self,o):o=C(o);return C(self.r+o.r,self.i+o.i)
 __radd__=__add__
 def __neg__(self):return C(-self.r,-self.i)
 def __sub__(self,o):return self+-C(o)
 def __rsub__(self,o):return C(o)+-self
 def __mul__(self,o):o=C(o);return C(self.r*o.r-self.i*o.i,self.r*o.i+self.i*o.r)
 __rmul__=__mul__
 def __truediv__(self,o):
  # Used only for real interval denominators.
  o=R(o);return C(self.r/o,self.i/o)
 def conj(self):return C(self.r,-self.i)
 def mag(self):return self.r.mag()+self.i.mag() # rigorous norm upper bound
 def inflate(self,e):return C(self.r.inflate(e),self.i.inflate(e))

def padd(p,q):
 r=[C(0) for _ in range(max(len(p),len(q)))]
 for n,a in enumerate(p):r[n]=r[n]+a
 for n,a in enumerate(q):r[n]=r[n]+a
 return r

def pmul(p,q):
 r=[C(0) for _ in range(len(p)+len(q)-1)]
 for i,a in enumerate(p):
  for j,b in enumerate(q):r[i+j]=r[i+j]+a*b
 return r

def pscale(p,x):return [a*x for a in p]
def pint(p):return [C(0)]+[a/(n+1) for n,a in enumerate(p)]
def peval(p,x):
 r=C(0)
 for a in reversed(p):r=r*x+a
 return r

def pnorm(p,H):return sum(a.mag()*H**n for n,a in enumerate(p))

class M:
 """Polynomial plus uniform complex norm remainder on [0,H]."""
 def __init__(self,p=0,e=0,H=F('.004')):
  self.p=p if isinstance(p,list) else [C(p)];self.e=F(e);self.H=F(H)
 def __add__(self,o):
  if not isinstance(o,M):o=M(o,H=self.H)
  assert self.H==o.H
  return M(padd(self.p,o.p),self.e+o.e,self.H)
 __radd__=__add__
 def __neg__(self):return M(pscale(self.p,-1),self.e,self.H)
 def __sub__(self,o):return self+-o if isinstance(o,M) else self+-M(o,H=self.H)
 def __rsub__(self,o):return -self+o
 def __mul__(self,o):
  if not isinstance(o,M):o=M(o,H=self.H)
  assert self.H==o.H
  err=pnorm(self.p,self.H)*o.e+pnorm(o.p,self.H)*self.e+self.e*o.e
  return M(pmul(self.p,o.p),err,self.H)
 __rmul__=__mul__
 def __truediv__(self,o):
  inv=1/R(o);return self*C(inv)
 def integral(self,L=None):
  L=self.H if L is None else F(L);assert 0<=L<=self.H
  return peval(pint(self.p),L).inflate(L*self.e)
 def integral_tail(self):
  # Primitive of the polynomial, subtract at H; actual integral from t to H.
  prim=pint(self.p);return M(padd([peval(prim,self.H)],pscale(prim,-1)),self.H*self.e,self.H)

def exp_affine(a,b,H,N=14):
 """exp(i*pi*(a+b*t)), a,b rational, 0<=t<=H."""
 a,b,H=F(a),F(b),F(H)
 z=[C(0,PI*a),C(0,PI*b)]
 s=[C(1)];power=[C(1)]
 for k in range(1,N+1):
  power=pmul(power,z);s=padd(s,pscale(power,F(1,factorial(k))))
 mx=PI.b*max(abs(a),abs(a+b*H))
 assert mx < N+2
 tail=mx**(N+1)/factorial(N+1)/(1-mx/F(N+2))
 return M(s,tail,H)

PI=R('3.14159265358979323846','3.14159265358979323847')
I=C(0,1)
c=F('.504');r6=F('.498');r7=F('.5');H=F('.004');h6=F('.002')
i2=C('.94977','-1.38995');i3=C('-1.00635','-.22789');i4=C('-.68738','1.60688')
weights={1:F('.5'),2:F(2),3:F('1.5')}; pp={1:6,2:3,3:2}
# Direct, literal expressions (8.13)--(8.18): q + (u+i*pi*v*t)exp(-i*pi*m*t).
g_data={(1,6):(F(8,3),F(-5,3),F(-1,2)),(2,6):(F(4,3),F(-1,3),F(1,2)),(3,6):(F(8,9),F(1,9),F(1,6)),(1,7):(F(24,25),F(1,25),F(1,10)),(2,7):(F(12,25),F(13,25),F(3,10)),(3,7):(F(8,25),F(17,25),F(-3,10))}
def affine(a,b,H):return M([C(a),C(b)],H=H)
def ff(j,k,a,b,H,N=14):
 mu=F(3,2) if k==6 else F(5,2)
 return affine(1+C(0,PI*(mu-j)*a),C(0,PI*(mu-j)*b),H)*exp_affine(mu*a,mu*b,H,N)
def gg(j,k,a,b,H,N=14):
 mu=F(3,2) if k==6 else F(5,2);q,u,v=g_data[j,k]
 return q+affine(u+C(0,PI*v*a),C(0,PI*v*b),H)*exp_affine(-mu*a,-mu*b,H,N)
def ww1(j,U):return affine(-1,C(0,PI*(F(3,2)-j)),U)*exp_affine(0,F(-3,2),U)
def ww2(j,U):
 # Integral_t^H v exp(i*3*pi*v/2) dv, with H fixed .004 and t<=U.
 expr=affine(0,1,H)*exp_affine(0,F(3,2),H)
 tail=expr.integral_tail()
 tail=M(tail.p,tail.e,U)
 return affine(-1,C(0,PI*(F(9,2)-j)),U)*exp_affine(0,F(3,2),U)+tail*C(-pp[j]*PI**2)

def enc(x):
 if isinstance(x,C):return {'re':enc(x.r),'im':enc(x.i)}
 d=10**18
 def dec(n):
  sign='-' if n<0 else '';a=abs(n);return f'{sign}{a//d}.{a%d:018d}'
 lo=x.a*d; hi=x.b*d
 ilo=lo.numerator//lo.denominator;ihi=-((-hi.numerator)//hi.denominator)
 return {'lower':str(x.a),'upper':str(x.b),'decimal_outer':[dec(ilo),dec(ihi)]}

results={}
def save(name,val):results[name]=enc(val);print(name,enc(val)['re']['decimal_outer'] if isinstance(val,C) else enc(val)['decimal_outer'],flush=True)
A=C(0);B=C(0)
for j,q in weights.items():
 for k,U,r,io in [(6,h6,r6,i3),(7,H,r7,i4)]:
  aa=(ff(j,k,U,-1,U)*ww2(j,U)).integral()
  bb=(gg(j,k,U,-1,U)*ww1(j,U)).integral()
  save(f'IA_{j}{k}',aa);save(f'IB_{j}{k}',bb)
  A=A+aa*io.conj()*q/(c*r*PI)
  B=B+bb*io*q/(c*r*PI)
E2=(-i3.conj()*(h6/r6)-i4.conj()*F('.008')-i4.conj()*C(0,2*PI)/250**2)*4/(c*PI)
for name,val in [('A',A),('B_conjugated',B.conj()),('E2',E2),('Delta_A',A-E2),('Delta_Bconj',B.conj()-E2),('Delta_total',A+B.conj()-E2*2)]:save(name,val)
D=A+B.conj()-E2*2
assert F('0.00000327768')<D.r.a and D.r.b<F('0.00000327769')
assert F('0.00000121298')<D.i.a and D.i.b<F('0.00000121299')
assert D.r.mag()**2+D.i.mag()**2<F('0.0000035')**2
assert 2*D.r.b<F('0.000006556')
# Failure of the individually printed epsilon/10 (Section12 second integral).
e=results['IA_17']
assert (R(e['re']['lower'],e['re']['upper'])+H).b < -F('0.000001')
# Failure of individually printed epsilon/2 at (12.15), using a rectangle lower bound.
d=A-E2
assert d.r.a>0 and d.i.a>0 and d.r.a**2+d.i.a**2>F('.000005')**2
# Independent extension: Section8 (8.19)--(8.24), directly from the six printed tables.
# N=40 handles |phase|<4; same exact-rational general Taylor engine as above.
def fg_integral(k,l,U,offf=F(0),offg=F(0)):
 total=C(0)
 for j,q in weights.items():
  total=total+(ff(j,k,offf,1,U,N=40)*gg(j,l,offg,1,U,N=40)).integral()*q
 return total
b11=fg_integral(6,6,c)/(c*c*PI)
b22=fg_integral(7,7,r7)/(r7*r7*PI)
b21=fg_integral(7,6,r7,offg=H)/(r7*c*PI)
b12=fg_integral(6,7,r7,offf=H)/(r7*c*PI)
c11=b11+b11.conj();c22=b22+b22.conj();c12=b12+b21.conj()
c1model=b11+i2*b21+i2.conj()*b12+b22*C(i2.r**2+i2.i**2)
c1model=c1model+c1model.conj()
for name,val in [('c11',c11),('c22',c22),('c12',c12),('c1',c1model)]:save(name,val)
assert F('7.05010466')<c1model.r.a and c1model.r.b<F('7.05010468')
assert F('-.45747159')<c12.r.a and c12.r.b<F('-.45747157')
assert F('-.20138345')<c12.i.a and c12.i.b<F('-.20138342')
assert c12.i.b<F('-.18179')-F('.0195')
assert c1model.r.a>F('6.9955')+F('.0546')
Path(__file__).with_name('rational-enclosures.json').write_text(json.dumps(results,indent=2)+'\n')
print('PASS: exact rational enclosure assertions; no floating point used')
