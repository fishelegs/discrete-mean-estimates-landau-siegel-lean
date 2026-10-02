# Interval arithmetic engine copied read-only from frozen Section 18 audit.
# Only the initial definitions are retained; no source audit execution or writes.
"""Fresh fixed-point directed-interval/Taylor certificate; Python stdlib only.
All computational numbers are rational intervals with denominator 10**55.
"""
from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path
S=10**55
class R:
 def __init__(self,x=0,hi=None):
  if isinstance(x,R):self.lo,self.hi=x.lo,x.hi;return
  if hi is not None:self.lo,self.hi=x,hi;return
  x=F(str(x));self.lo=(x.numerator*S)//x.denominator;self.hi=-((-x.numerator*S)//x.denominator)
 @staticmethod
 def raw(a,b):return R(a,b)
 def __add__(x,y):
  y=R(y);return R.raw(x.lo+y.lo,x.hi+y.hi)
 __radd__=__add__
 def __neg__(x):return R.raw(-x.hi,-x.lo)
 def __sub__(x,y):return x+-R(y)
 def __rsub__(x,y):return R(y)+-x
 def __mul__(x,y):
  y=R(y);a=[x.lo*y.lo,x.lo*y.hi,x.hi*y.lo,x.hi*y.hi];return R.raw(min(a)//S,-((-max(a))//S))
 __rmul__=__mul__
 def __truediv__(x,y):
  y=R(y);assert y.lo*y.hi>0
  a=[F(x.lo*S,y.lo),F(x.lo*S,y.hi),F(x.hi*S,y.lo),F(x.hi*S,y.hi)];lo=min(a);hi=max(a)
  return R.raw(lo.numerator//lo.denominator,-((-hi.numerator)//hi.denominator))
 def __rtruediv__(x,y):return R(y)/x
 def __pow__(x,n):
  assert n>=0;v=R(1)
  for _ in range(n):v=v*x
  return v
 def absmax(x):return R.raw(max(abs(x.lo),abs(x.hi)),max(abs(x.lo),abs(x.hi)))
 def show(x,d=30):
  def st(n):
   neg=n<0;n=abs(n);return ('-'if neg else '')+str(n//10**d)+'.'+str(n%10**d).zfill(d)
  scale=10**(55-d);return [st(x.lo//scale),st(-((-x.hi)//scale))]
 def dump(x):return {'lo':str(x.lo),'hi':str(x.hi),'scale':'1e55','decimal':x.show()}
class C:
 def __init__(self,x=0,y=0):
  if isinstance(x,C):self.r,self.i=x.r,x.i;return
  self.r,self.i=R(x),R(y)
 def __add__(x,y):y=C(y);return C(x.r+y.r,x.i+y.i)
 __radd__=__add__
 def __neg__(x):return C(-x.r,-x.i)
 def __sub__(x,y):return x+-C(y)
 def __rsub__(x,y):return C(y)+-x
 def __mul__(x,y):y=C(y);return C(x.r*y.r-x.i*y.i,x.r*y.i+x.i*y.r)
 __rmul__=__mul__
 def __truediv__(x,y):
  y=C(y);d=y.r*y.r+y.i*y.i;return C((x.r*y.r+x.i*y.i)/d,(x.i*y.r-x.r*y.i)/d)
 def __rtruediv__(x,y):return C(y)/x
 def conj(x):return C(x.r,-x.i)
 def dump(x):return {'real':x.r.dump(),'imag':x.i.dump()}
Z=C();ONE=C(1);ii=C(0,1)
def atan_inv(n,N):
 total=F(0)
 for k in range(N):total+=F((-1)**k,(2*k+1)*n**(2*k+1))
 nxt=F((-1)**N,(2*N+1)*n**(2*N+1));a=R(total);b=R(total+nxt)
 return R.raw(min(a.lo,b.lo),max(a.hi,b.hi))
# Machin identity pi=16 atan(1/5)-4 atan(1/239), with alternating-tail enclosures.
pi=16*atan_inv(5,50)-4*atan_inv(239,15)
N=80
class P:
 def __init__(self,a):self.a=[C(x)for x in a]
 def __add__(x,y):
  if not isinstance(y,P):y=P([y])
  return P([(x.a[k]if k<len(x.a)else Z)+(y.a[k]if k<len(y.a)else Z) for k in range(max(len(x.a),len(y.a)))])
 __radd__=__add__
 def __neg__(x):return P([-a for a in x.a])
 def __sub__(x,y):return x+-poly(y)
 def __rsub__(x,y):return poly(y)+-x
 def __mul__(x,y):
  if not isinstance(y,P):return P([a*C(y)for a in x.a])
  a=[Z for _ in range(len(x.a)+len(y.a)-1)]
  for j,b in enumerate(x.a):
   for k,c in enumerate(y.a):a[j+k]=a[j+k]+b*c
  return P(a)
 __rmul__=__mul__
 def __truediv__(x,y):return P([a/y for a in x.a])
 def integ(x):return P([0]+[a/(k+1)for k,a in enumerate(x.a)])
 def eval(x,t):
  v=Z
  for a in x.a[::-1]:v=v*t+a
  return v
 def integral(x,t):return x.integ().eval(t)
def poly(x):return x if isinstance(x,P)else P([x])
t=P([0,1])
def expconst(angle):
 w=C(0,angle);term=ONE;s=ONE
 for k in range(1,N+1):term=term*w/k;s=s+term
 # Ratio of successive absolute exponential terms <= M/(N+2) < 1/2.
 M=R(angle).absmax();assert M.hi<40*S
 err=2*(M**(N+1))/factorial(N+1);rad=R.raw(-err.hi,err.hi)
 return s+C(rad,rad)
def explin(a,shift=0,end=1):
 # exp(i*pi*a*(t+shift)); real |t| <= end; remainder stored as constant interval.
 w=C(0,pi*a);co=[ONE]
 for k in range(1,N+1):co.append(co[-1]*w/k)
 M=(pi*a*R(end)).absmax();assert M.hi<40*S
 err=2*(M**(N+1))/factorial(N+1);rad=R.raw(-err.hi,err.hi)
 co[0]=co[0]+C(rad,rad)
 return P(co)*expconst(pi*a*R(shift))
