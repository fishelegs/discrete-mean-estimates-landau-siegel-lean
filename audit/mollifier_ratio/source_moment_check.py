"""Independent diagnostic from source d3,d4,d5,d6 integrals, not A/B code.
Source /tmp/zhang-2211.02515-source.tex (10.12)-(10.17), lines 2953-3168.
This is mpmath diagnostic evidence, not a rigorous error certificate.
"""
from pathlib import Path
from fractions import Fraction
import json
import mpmath as m
m.mp.dps=85
r1,r2,r3,h,half=map(m.mpf,['.504','.5','.498','.004','.002'])
pi=m.pi; I=m.j
q=[m.mpf('.5'),m.mpf(2),m.mpf('1.5')]
ab=[6,3,2]
def integral(f,a,b):return m.quad(f,[m.mpf(a),m.mpf(b)])
def f(j,tau,z):return (1+I*pi*(tau-j)*z)*m.exp(I*pi*tau*z)
def g(j,tau,z):
 a,b=[(2,3),(3,1),(1,2)][j-1]
 return a*b/tau**2+(1-a*b/tau**2-I*pi*(a-tau)*(b-tau)*z/tau)*m.exp(-I*pi*tau*z)
def y1(j,z):return I*pi*(6-j)*(z-r2)-pi*pi*ab[j-1]/2*((r1-z)**2-2*(r2+half-z)**2)
def y2(j,z):return I*pi*(6-j)*(r1-z)-pi*pi*ab[j-1]/2*(r1-z)**2
t1=m.mpf('1.5');t2=m.mpf('2.5')
def d3(j,i2):
 return -ab[j-1]*pi/500*integral(lambda z:f(j,t1,h+z)/r1+i2*f(j,t2,z)/r2,0,r2)+500/(r1*pi)*integral(lambda z:f(j,t1,z)-f(j,t1,half+z),0,half)+500/(r1*pi)*(integral(lambda z:f(j,t1,r1-z)*y1(j,z),r2,r2+half)+integral(lambda z:f(j,t1,r1-z)*y2(j,z),r2+half,r1))
def d4(j):
 return 500/(r1*pi)*integral(lambda z:g(j,t1,z)-g(j,t1,half+z),0,half)-500*I*j/r1*integral(lambda z:g(j,t1,half+z)*(half-z)+g(j,t1,z)*z,0,half)
def d5(j,i3,i4):
 return -500*i3/(r3*pi)*integral(lambda z:g(j,t1,z),0,half)+1000*i4/pi*integral(lambda z:g(j,t2,z)-g(j,t2,half+z),0,half)-500*I*j*i3/r3*integral(lambda z:(half-z)*g(j,t1,z),0,half)-1000*I*j*i4*integral(lambda z:(half-z)*g(j,t2,half+z)+z*g(j,t2,z),0,half)
def d6(j,i3,i4):
 return -500*i3/(r3*pi)*integral(lambda z:f(j,t1,z),0,half)-ab[j-1]*pi/500*integral(lambda z:i3*f(j,t1,half+z)/r3+i4*f(j,t2,h+z)/r2,0,m.mpf('.496'))+1000*i4/pi*integral(lambda z:f(j,t2,z)-f(j,t2,half+z),0,half)+500/pi*integral(lambda z:(i3*f(j,t1,z)/r3+i4*f(j,t2,half+z)/r2)*y1(j,r2+half-z),0,half)+1000*i4/pi*integral(lambda z:f(j,t2,z)*y2(j,r1-z),0,half)
L=[sum(q[j-1]*(d3(j,0)+m.conj(d4(j))) for j in [1,2,3]),sum(q[j-1]*(d3(j,1)-d3(j,0)) for j in [1,2,3]),sum(q[j-1]*(d5(j,1,0)+m.conj(d6(j,1,0))) for j in [1,2,3]),sum(q[j-1]*(d5(j,0,1)+m.conj(d6(j,0,1))) for j in [1,2,3])]
cert=json.loads(Path(__file__).with_name('ratio-certificate.json').read_text())
def inside(v,iv):return m.mpf(iv['lo'])/10**55<=v<=m.mpf(iv['hi'])/10**55
out=[]
for i,(x,box) in enumerate(zip(L,cert['ell']),1):
 assert inside(x.real,box['real']) and inside(x.imag,box['imag'])
 out.append({'coefficient':i,'real':m.nstr(x.real,70),'imag':m.nstr(x.imag,70),'inside_interval':True})
R=32/(pi*h)+88*pi*h/3
assert inside(R,cert['J_norm'])
print(json.dumps({'precision':m.mp.dps,'source_integral_coefficients':out,'R':m.nstr(R,70),'PASS':'All four independently transcribed Section 10 source coefficients are contained in the frozen intervals'},indent=2))
