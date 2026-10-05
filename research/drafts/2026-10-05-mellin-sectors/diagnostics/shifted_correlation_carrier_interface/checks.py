#!/usr/bin/env python3
"""Finite interface diagnostics only, not a shifted-convolution theorem."""
import json,math
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import mpmath as mp
from sympy import divisors,mobius,kronecker_symbol
HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True,'actual_arithmetic_expansion_constructed':False}
assert 519-400==119 and 400+6-519==-113
assert 519+405-400==524
assert F(1,8*16)-F(1,256)==F(1,256)
assert 2*400-395==405
out['exact_carrier_variation_and_rectangle_exponents']='PASS'
mp.mp.dps=32
bet=[mp.mpc(0,'.011'),mp.mpc(0,'.021'),mp.mpc(0,'.032')]
@lru_cache(None)
def chi(n):return int(kronecker_symbol(5,n))
@lru_cache(None)
def ups(n):return sum(int(mobius(d))*int(mobius(n//d))*chi(n//d) for d in divisors(n))
@lru_cache(None)
def nu(n,dual):return sum(mp.exp((1 if dual else -1)*bet[0]*mp.log(d))*chi(n//d) for d in divisors(n))
@lru_cache(None)
def d23(n,dual):return sum(mp.exp((1 if dual else -1)*(bet[1]*mp.log(d)+bet[2]*mp.log(n//d))) for d in divisors(n))
z1=mp.mpc('.05','.17');wr1=mp.mpc('-.05','.10');wn1=mp.mpc('-.05','-.30')
z2=mp.mpc('.05','-.13');wr2=mp.mpc('-.05','-.18');wn2=mp.mpc('-.05','.55')
kn1=z1+wr1;kn2=z2+wr2;kp1=z1+wn1;kp2=z2+wn2
on1=mp.mpc('.05','.23');on2=mp.mpc('.05','-.37');op1=mp.mpc('.05','-.19');op2=mp.mpc('.05','.29')
def etas(bit,k1,k2,w1,w2):return (k1+w1,k2+w2) if not bit else (k2+mp.conj(w2),k1+mp.conj(w1))
def q(u,dual):return 1-u if dual else u
errors=[];cases=0
for i in [0,1]:
 for j in [0,1]:
  enA,enB=etas(i,kn1,kn2,on1,on2);epA,epB=etas(j,kp1,kp2,op1,op2)
  for d in [1,4]:
   for e in [1,4]:
    for m,n,mm,nn in [(1,2,3,1),(2,3,1,2),(3,2,2,3),(1,1,3,3)]:
     for t in [mp.mpf('0'),mp.mpf('3.7')]:
      s=mp.mpf('.5')+1j*t;u1=s+kn1;u2=s+kp1;v1=s+kn2;v2=s+kp2
      w1=ups(d)*nu(m,i)*d23(n,j)*d**(z1-u1)*m**(-q(u1,i)-on1)*n**(-q(u2,j)-op1)
      w2=ups(e)*nu(mm,i)*d23(nn,j)*e**(z2-v1)*mm**(-q(v1,i)-on2)*nn**(-q(v2,j)-op2)
      direct=w1*mp.conj(w2)
      M,MM=(mm,m) if i else (m,mm);N,NN=(nn,n) if j else (n,nn)
      k=d*M*N;ell=e*MM*NN
      aa=ups(d)*d**(-wr1)*nu(M,0)*M**(-enA)*d23(N,0)*N**(-epA)
      bb=ups(e)*e**(-wr2)*nu(MM,0)*MM**(-enB)*d23(NN,0)*NN**(-epB)
      grouped=aa*mp.conj(bb)/mp.sqrt(k*ell)*mp.exp(1j*t*mp.log(mp.mpf(ell)/k))
      er=abs(direct-grouped);assert er<mp.mpf('1e-25');errors.append(float(er));cases+=1
out['exact_transported_shifted_coefficients']={'all_four_branches':True,'cases':cases,'max_error':max(errors),'status':'PASS'}

# Representative normalized common-base gamma product, retaining its phase.
tc=mp.mpf('70');H=mp.mpf('6');W=mp.mpf('2');delta=H/W**2
zeta=mp.mpc('.05','.21');omega=mp.mpc('.05','-.17')
def rawG(t):
 s=mp.mpf('.5')+1j*t
 return mp.gamma((s+zeta)/2)/mp.gamma(s/2)*mp.gamma((1-s+omega)/2)/mp.gamma((1-s)/2)
G0=rawG(tc)
def G(t):return rawG(t)/G0
norm=2*mp.sqrt(mp.pi)*W

def time_integrand(t,theta):return mp.exp(-(t-tc)**2/(4*W**2)+1j*t*theta)*G(t)/norm
def T(theta):return mp.quad(lambda t:time_integrand(t,theta),[tc-H,tc,tc+H])
def Td(theta):return mp.quad(lambda t:1j*t*time_integrand(t,theta),[tc-H,tc,tc+H])
saddle=[]
for theta in [-delta/32,delta/32]:
 y=2*W**2*theta
 def A(th):return mp.quad(lambda x:mp.exp(-x*x/(4*W**2))*G(tc+x+2j*W**2*th)/norm,[-H,0,H])
 def E(th):
  yy=2*W**2*th
  right=mp.quad(lambda r:1j*time_integrand(tc+H+1j*r,th),[0,yy])
  left=mp.quad(lambda r:1j*time_integrand(tc-H+1j*r,th),[0,yy])
  return left-right
 def rhs(th):return mp.exp(1j*tc*th-W**2*th**2)*A(th)+E(th)
 e0=abs(T(theta)-rhs(theta));e1=abs(Td(theta)-mp.diff(rhs,theta))
 assert e0<mp.mpf('1e-24') and e1<mp.mpf('1e-23')
 saddle.append({'theta':str(theta),'kernel_error':float(e0),'derivative_error':float(e1)})
out['actual_variable_saddle_kernel_and_derivative']={'cases':saddle,'both_endpoints_retained':True,'status':'PASS'}

# Antiderivative identity used only in the CONDITIONAL density transfer.
anti=[]
for qv in range(5):
 for rho in [mp.mpc('.1','.3'),mp.mpc('-.07','-.2')]:
  zz=1j*mp.mpc('70','.5')+rho;dd=mp.mpf('.13')
  poly=lambda x:mp.exp(zz*x)*sum((-1)**r*math.factorial(qv)/math.factorial(qv-r)*x**(qv-r)/zz**(r+1) for r in range(qv+1))
  exact=poly(dd)-poly(-dd)
  numerical=mp.quad(lambda x:x**qv*mp.exp(zz*x),[-dd,0,dd])
  er=abs(exact-numerical);assert er<mp.mpf('1e-26');anti.append(float(er))
out['conditional_density_endpoint_antiderivatives']={'cases':len(anti),'max_error':max(anti),'status':'PASS'}

# Endpoint-inclusive Stieltjes identity, with atoms at BOTH endpoints and
# a subtracted continuous density. The kernel can be any C1 function.
dd=mp.mpf('.4');atoms=[(-dd,mp.mpc(1,2)),(-dd/2,mp.mpc(-2,1)),(mp.mpf(0),mp.mpc('.5','-.3')),(dd,mp.mpc(2,-1))]
M=lambda x:mp.mpc('.2','.1')+mp.mpc('-.3','.05')*x
Mint=lambda x:mp.mpc('.2','.1')*(x+dd)+mp.mpc('-.3','.05')*(x*x-dd*dd)/2
K=lambda x:mp.exp(3j*x-4*x*x)
Kd=lambda x:(3j-8*x)*K(x)
FE=lambda x:sum(v for a,v in atoms if a<=x)-Mint(x)
left=sum(v*K(a) for a,v in atoms)-mp.quad(lambda x:K(x)*M(x),[-dd,0,dd])
points=[a for a,v in atoms]
intpart=0
for lo,hi in zip(points,points[1:]):
 const=sum(v for a,v in atoms if a<=lo)
 intpart+=mp.quad(lambda x:Kd(x)*(const-Mint(x)),[lo,hi])
right=K(dd)*FE(dd)-intpart
err=abs(left-right);assert err<mp.mpf('1e-26')
out['endpoint_inclusive_cumulative_remainder_identity']={'error':float(err),'status':'PASS'}

# The two actual integer progression parameterizations and p-unit masks.
progressions=0
for p in [5,7,11]:
 for k in range(1,45):
  for ell in range(1,45):
   if k==ell or (k*ell)%p==0:continue
   assert ((ell-k)%p==0)==any(ell==k+h*p for h in range(-9,10) if h)
   assert ((ell+k)%p==0)==any(ell==h*p-k for h in range(1,19))
   progressions+=1
out['exact_positive_negative_shift_progressions']={'cases':progressions,'status':'PASS'}
out['status']='PASS'
s=json.dumps(out,indent=2,sort_keys=True)+'\n';(HERE/'CHECKS.json').write_text(s);print(s,end='')
