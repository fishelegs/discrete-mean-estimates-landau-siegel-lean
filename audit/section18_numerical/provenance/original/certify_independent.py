"""Fresh fixed-point directed-interval/Taylor certificate; Python stdlib only.
All computational numbers are rational intervals with denominator 10**55.
"""
from fractions import Fraction as F
from math import factorial
import json
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
r1=R('.504');r2=R('.5');r3=R('.498');h=R('.004');q=[R('.5'),R(2),R('1.5')]
i2=C('.94977','-1.38995');i3=C('-1.00635','-.22789');i4=C('-.68738','1.60688')
def f(j,k,shift=0,sgn=1,end=1):
 a=R('1.5')if k==1 else R('2.5');u=t*sgn+shift
 return (u*C(0,pi*(a-j))+1)*explin(a*sgn,R(shift)/sgn,end)
def g(j,k,shift=0,sgn=1,end=1):
 a=R('1.5')if k==1 else R('2.5');u=t*sgn+shift
 A=([F(8,3),F(4,3),F(8,9)]if k==1 else [F(24,25),F(12,25),F(8,25)])[j-1]
 B=([-F(5,3),-F(1,3),F(1,9)]if k==1 else [F(1,25),F(13,25),F(17,25)])[j-1]
 D=([-F(1,2),F(1,2),F(1,6)]if k==1 else [F(1,10),F(3,10),-F(3,10)])[j-1]
 return (u*C(0,pi*D)+B)*explin(-a*sgn,R(shift)/sgn,end)+A

def b(k,l,sk,sl,end,den):
 return sum(((f(j,k,sk,end=end)*g(j,l,sl,end=end)).integral(end)*q[j-1]for j in range(1,4)),Z)/C(pi*den)
b11=b(1,1,0,0,r1,r1*r1);b22=b(2,2,0,0,r2,r2*r2);b12=b(1,2,h,0,r2,r1*r2);b21=b(2,1,0,h,r2,r1*r2);b33=b(1,1,0,0,r3,r3*r3)
c11=2*b11.r;c22=2*b22.r;c12=b12+b21.conj();c33=2*b33.r

def e(j,k):
 r=[0,r1,r2,r3][k];a=R('2.5')if k==2 else R('1.5');z=C(0,pi*(a*a*r));v=C(j)/z
 return (1-C(j)/C(a)+v)*expconst(pi*a*r)-v
bstar=(t*explin(R('1.5'),end=h)).integral(h)/C(r1)
EE=[C(j)/C('.756')*(explin(R('-1.5'),-r1,end=h)-expconst(pi*R('.75'))).integral(h)for j in range(1,4)]
# Note: explin(-1.5,-r1) means exp(1.5*pi*i*(r1-t)).
E1=[-C(pi)*bstar*sum((f(j,k,r,sgn=-1,end=R('.496')).integral(R('.496'))*([3,6,3][j-1])/C(r)for j in range(1,4)),Z)for k,r in [(1,r3),(2,r2)]]
E2=[C(4)/C(r1*pi)*C(-R('.002')/r3),C(4)/C(r1*pi)*(C('-.008')-C(0,2*pi)/C(250**2))]
W1=[];W2=[]
for j in range(1,4):
 W1.append(explin(R('-1.5'),end=h)*(t*C(0,pi*(R('1.5')-j))-1))
 integ=(t*explin(R('1.5'),end=h)).integ()
 W2.append(explin(R('1.5'),end=h)*(t*C(0,pi*(R('4.5')-j))-1)+(P([integ.eval(h)])-integ)*C(-pi*pi*[6,3,2][j-1]))
EX=[]
for k,r,d in [(1,r3,R('.002')),(2,r2,h)]:
 A=sum(((f(j,k,d,-1,d)*W2[j-1]).integral(d)*q[j-1]for j in range(1,4)),Z)/C(r1*r*pi)
 B=sum(((g(j,k,d,-1,d)*W1[j-1]).integral(d)*q[j-1]for j in range(1,4)),Z)/C(r1*r*pi)
 EX.append(A+B.conj())

def matrix(den,high,tail):
 c34=b(2,1,R('.002'),0,r3,R(den)*r3)+b(1,2,0,R('.002'),r3,R(den)*r3).conj()
 M=[[Z for _ in range(4)]for _ in range(4)];M[0][0]=C(c11);M[1][1]=C(c22);M[0][1]=c12.conj();M[1][0]=c12
 M[2][2]=C(c33);M[3][3]=C(c22);M[2][3]=c34.conj();M[3][2]=c34
 K=[[Z for _ in range(2)]for _ in range(2)]
 for u,ku in enumerate([1,2]):
  for v,kv in enumerate([3,2]):
   ej=[e(j,ku)-(EE[j-1]if tail=='printed'else -C(0,pi*j)*bstar)if u==0 and tail!='collapsed'else e(j,ku)for j in range(1,4)]
   K[u][v]=-ii*(sum((ej[j-1]*e(j,kv)*w for j,w in [(1,3),(2,3),(3,1)]),Z)+expconst(pi*R(['.756','1.25'][u]))*expconst(pi*R(['.747','1.25'][v])))
   if u==0:K[u][v]=K[u][v]+(E1[v]if tail!='collapsed'else Z)+(2*E2[v]if high=='printed'else EX[v])
   M[v+2][u]=K[u][v];M[u][v+2]=K[u][v].conj()
 return M,K,c34

def ldl(M,order=[1,2,3,0]):
 n=4;A=[[M[i][j]for j in order]for i in order];L=[[Z for _ in range(n)]for _ in range(n)];D=[]
 for j in range(n):
  dj=A[j][j]-sum((L[j][k]*L[j][k].conj()*C(D[k])for k in range(j)),Z)
  assert dj.i.lo<=0<=dj.i.hi
  D.append(dj.r);assert dj.r.lo>0
  L[j][j]=ONE
  for i in range(j+1,n):L[i][j]=(A[i][j]-sum((L[i][k]*L[j][k].conj()*C(D[k])for k in range(j)),Z))/C(D[j])
 return D
res={'method':'fixed point directed intervals; scale 1e55; Taylor degree 80; Machin pi with exact alternating tails','pi':pi.dump(),'c11':c11.dump(),'c22':c22.dump(),'c12':c12.dump(),'c33':c33.dump(),'bstar':bstar.dump(),'printed_tail':[x.dump()for x in EE],'upstream_tail':[(-C(0,pi*j)*bstar).dump()for j in range(1,4)],'E1':[x.dump()for x in E1],'E2':[x.dump()for x in E2],'EX':[x.dump()for x in EX]}
z=[ONE,i2,i3,i4]
printed_cancel=sum((z[v+2].conj()*(ii*sum((EE[j-1]*e(j,kv)*w for j,w in [(1,3),(2,3),(3,1)]),Z)+E1[v]) for v,kv in enumerate([3,2])),Z)
upstream_cancel=sum((z[v+2].conj()*(ii*sum((-C(0,pi*j)*bstar*e(j,kv)*w for j,w in [(1,3),(2,3),(3,1)]),Z)+E1[v]) for v,kv in enumerate([3,2])),Z)
assert printed_cancel.r.hi < R('-.00007').lo
assert (upstream_cancel.r.absmax()**2+upstream_cancel.i.absmax()**2).hi < R('.0000000001').lo
res['printed_cancellation_remainder']=printed_cancel.dump()
res['upstream_cancellation_remainder']=upstream_cancel.dump()
print('printed cancellation',printed_cancel.r.show(22),printed_cancel.i.show(22),flush=True)
print('upstream cancellation',upstream_cancel.r.show(22),upstream_cancel.i.show(22),flush=True)
for den in ['.504','.5']:
 for high in ['printed','exact']:
  for tail in ['printed','collapsed','upstream']:
   M,K,c34=matrix(den,high,tail)
   C1=sum((z[u].conj()*M[u][v]*z[v]for u in [0,1]for v in [0,1]),Z)
   C2=sum((z[u].conj()*M[u][v]*z[v]for u in [2,3]for v in [2,3]),Z)
   C3=sum((z[u]*z[v+2].conj()*K[u][v]for u in [0,1]for v in [0,1]),Z)
   total=C1.r+C2.r+2*C3.r;piv=ldl(M)
   key=den+':'+high+':'+tail
   res[key]={'c1':C1.dump(),'c2':C2.dump(),'c3':C3.dump(),'total':total.dump(),'c34':c34.dump(),'matrix':[[x.dump()for x in row]for row in M],'ordered_LDL_pivots':[x.dump()for x in piv],'minimum_with_first_coefficient_1':piv[-1].dump()}
   assert total.lo>R('.05').hi and piv[-1].lo>R('.024').hi
   print(key,'total',total.show(22),'minimum',piv[-1].show(22),flush=True)
json.dump(res,open('/tmp/section18-quadratic-audit/certified.json','w'),indent=2)
print('PASS: all twelve branches total > .05 and global constrained model minimum > .024')
