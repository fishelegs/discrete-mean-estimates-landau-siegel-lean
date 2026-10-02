"""Independent Section8 model: limiting-beta parameterization and numerical quadrature.
Exploratory high-precision calculation; the separate interval_closed_forms.py is
an interval check. Neither is a Lean integral proof. All cross shifts are +.004.
"""
import mpmath as mp
mp.mp.dps=70
pi=mp.pi; I=mp.mpc(0,1)
def q(a,b=1):return mp.mpf(a)/b
weights={1:q(1,2),2:q(2),3:q(3,2)}
def F(j,mu,z):
 b=I*pi*q(mu*2-9,2) # mu6->3/2; mu7->5/2
 return (1+(b-I*pi*j)*z)*mp.exp(b*z)
def G(j,mu,z):
 b=I*pi*q(mu*2-9,2)
 prod=-pi*pi*{1:6,2:3,3:2}[j]
 return prod/b**2+(1-prod/b**2-(prod-b*I*pi*(6-j)+b*b)*z/b)*mp.exp(-b*z)
def integral(mu,nu,U,a=0,b=0):
 return sum(weights[j]*mp.quad(lambda z:F(j,mu,z+a)*G(j,nu,z+b),[0,U]) for j in weights)
P1=q(63,125);P2=q(1,2);h=q(1,250)
b11=integral(6,6,P1)/(P1*P1*pi);b22=integral(7,7,P2)/(P2*P2*pi)
b12=integral(6,7,P2,h,0)/(P1*P2*pi);b21=integral(7,6,P2,0,h)/(P1*P2*pi)
c11=2*mp.re(b11);c22=2*mp.re(b22);c12=b12+mp.conj(b21)
iota=q(94977,100000)-I*q(138995,100000)
c1=c11+iota*mp.conj(c12)+mp.conj(iota)*c12+abs(iota)**2*c22
for name in ['b11','b22','b12','b21','c11','c22','c12','c1']:
 print(name,mp.nstr(globals()[name],60))
assert mp.re(c1)>7
