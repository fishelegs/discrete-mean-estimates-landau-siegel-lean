from fractions import Fraction as Q
import mpmath as m
m.mp.dps=80
I=m.mpc(0,1); pi=m.pi
def R(x):
 x=Q(x);return m.mpf(x.numerator)/x.denominator
# Literal coefficient tables (8.13)-(8.18): each term (frequency/pi, polynomial).
f={
(1,6):[(Q(3,2),[1,I*pi/2])],(2,6):[(Q(3,2),[1,-I*pi/2])],(3,6):[(Q(3,2),[1,-3*I*pi/2])],
(1,7):[(Q(5,2),[1,3*I*pi/2])],(2,7):[(Q(5,2),[1,I*pi/2])],(3,7):[(Q(5,2),[1,-I*pi/2])]}
g={
(1,6):[(Q(0),[R('8/3')]),(Q(-3,2),[-R('5/3'),-I*pi/2])],
(2,6):[(Q(0),[R('4/3')]),(Q(-3,2),[-R('1/3'),I*pi/2])],
(3,6):[(Q(0),[R('8/9')]),(Q(-3,2),[R('1/9'),I*pi/6])],
(1,7):[(Q(0),[R('24/25')]),(Q(-5,2),[R('1/25'),I*pi/10])],
(2,7):[(Q(0),[R('12/25')]),(Q(-5,2),[R('13/25'),3*I*pi/10])],
(3,7):[(Q(0),[R('8/25')]),(Q(-5,2),[R('17/25'),-3*I*pi/10])]}
def shift(terms,a):
 a=R(a);out=[]
 for freq,p in terms:
  z=m.exp(I*pi*R(freq)*a)
  out.append((freq,[(p[0]+(p[1]*a if len(p)>1 else 0))*z]+([p[1]*z] if len(p)>1 else [])))
 return out
def moments(freq,T,N):
 T=R(T)
 if freq==0:return [T**(k+1)/(k+1) for k in range(N)]
 v=I*pi*R(freq); e=m.exp(v*T);out=[(e-1)/v]
 for k in range(1,N):out.append(T**k*e/v-k*out[-1]/v)
 return out
def product_integral(F,G,T):
 out=0
 for fr,p in F:
  for gr,q in G:
   c=[sum(p[i]*q[k-i] for i in range(len(p)) if 0<=k-i<len(q)) for k in range(len(p)+len(q)-1)]
   out+=sum(a*b for a,b in zip(c,moments(fr+gr,T,len(c))))
 return out
weights=[Q(1,2),Q(2),Q(3,2)]
def B(k,l,T,a=0,b=0):return sum(R(w)*product_integral(shift(f[j,k],a),shift(g[j,l],b),T) for j,w in enumerate(weights,1))
x=R('63/125');y=R('1/2'); off=Q(1,250)
b11=B(6,6,Q(63,125))/(x*x*pi);b22=B(7,7,Q(1,2))/(y*y*pi)
b12=B(6,7,Q(1,2),off,0)/(x*y*pi);b21=B(7,6,Q(1,2),0,off)/(x*y*pi)
c11=2*m.re(b11);c22=2*m.re(b22);c12=b12+m.conj(b21)
iota=R('94977/100000')-I*R('138995/100000')
c1=c11+iota*m.conj(c12)+m.conj(iota)*c12+abs(iota)**2*c22
for n in ['b11','b22','b12','b21','c11','c22','c12','c1']:
 print(n,m.nstr(globals()[n],75))
# Direct quadrature of literal table as a cross-check within this implementation.
def ev(terms,z):return sum(sum(co*z**k for k,co in enumerate(p))*m.exp(I*pi*R(fr)*z) for fr,p in terms)
q12=sum(R(w)*m.quad(lambda z:ev(f[j,6],z+R(off))*ev(g[j,7],z),[0,y]) for j,w in enumerate(weights,1))/(x*y*pi)
q21=sum(R(w)*m.quad(lambda z:ev(f[j,7],z)*ev(g[j,6],z+R(off)),[0,y]) for j,w in enumerate(weights,1))/(x*y*pi)
print('closed_vs_direct_quad',m.nstr(abs(b12-q12)+abs(b21-q21),10))
