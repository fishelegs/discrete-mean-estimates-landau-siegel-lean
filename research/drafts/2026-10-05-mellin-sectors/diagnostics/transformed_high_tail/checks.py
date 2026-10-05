#!/usr/bin/env python3
"""Finite checks of literal contour transport and infinite-tail proof interfaces."""
import cmath,itertools,json,math
from functools import lru_cache
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
ROOT=Path(__file__).resolve().parent
out={'diagnostic_only':True,'sample_does_not_assume_A2022':True}
assert 2076*12-400+9*36==24836 and 5-12==-7
assert F(4)+F(1,2)==F(9,2) and 2*519==1038
out['exact_conductor_and_final_exponents']='PASS'
# Disjoint selected rectangles; endpoints are checked exactly with integers.
geo=0;retained_far=0;Y=20
intervals={-1:(Y/2,Y)}
intervals.update({j:(2**j*Y,2**(j+1)*Y) for j in range(7)})
rectangles=[(j,j) for j in range(7)]+[(j,j-1) for j in range(7)]+[(j-1,j) for j in range(7)]
for x,y in itertools.product(range(1,321),repeat=2):
 high=max(x,y)>Y
 hits=sum(intervals[a][0]<x<=intervals[a][1] and intervals[b][0]<y<=intervals[b][1] for a,b in rectangles)
 assert hits<=1
 if hits:assert high
 if high and not hits:assert max(x,y)>=2*min(x,y)
 if hits and max(x,y)>F(5,4)*min(x,y):retained_far+=1
 geo+=1
out['exact_disjoint_high_grid']={'pairs':geo,'retained_far_pairs':retained_far,'low_boundary_square_excluded':True,'status':'PASS'}
@lru_cache(None)
def fac(n):
 ans=[];p=2
 while p*p<=n:
  if n%p==0:
   e=0
   while n%p==0:n//=p;e+=1
   ans.append((p,e))
  p+=1
 if n>1:ans.append((n,1))
 return tuple(ans)
def tau(n,q):return math.prod(math.comb(e+q-1,q-1) for p,e in fac(n))
def divisors(n):return [d for d in range(1,n+1) if n%d==0]
def mu(n):return 0 if any(e>1 for p,e in fac(n)) else (-1)**len(fac(n))
def chi(n):return 0 if n%3==0 else (1 if n%3==1 else -1)
@lru_cache(None)
def ups(n):return sum(mu(d)*mu(n//d)*chi(n//d) for d in divisors(n))
alpha=.025;bet=[.011j,.021j,.032j]
z1=alpha+.17j;wr1=-alpha+.10j;wn1=-alpha-.30j
z2=alpha-.13j;wr2=-alpha-.18j;wn2=-alpha+.55j
J=3
on1=J+.23j;on2=J-.37j;op1=J-.19j;op2=J+.29j
@lru_cache(None)
def nu(n,dual=0):return sum(d**((1 if dual else -1)*bet[0])*chi(n//d) for d in divisors(n))
@lru_cache(None)
def d23(n,dual=0):return sum(cmath.exp((1 if dual else -1)*(bet[1]*math.log(d)+bet[2]*math.log(n//d))) for d in divisors(n))
def etas(bit,k1,k2,w1,w2):return (k1+w1,k2+w2) if not bit else (k2+w2.conjugate(),k1+w1.conjugate())
def coeff(k,en,ep,wr,X):return sum(ups(d)*d**(-wr)*nu(m)*m**(-en)*d23(k//d//m)*(k//d//m)**(-ep) for d in divisors(k) if d<=X for m in divisors(k//d))

caps=0;errs=[]
for i,j in itertools.product([0,1],repeat=2):
 ens=etas(i,z1+wr1,z2+wr2,on1,on2);eps=etas(j,z1+wn1,z2+wn2,op1,op2)
 for en,ep,wr in zip(ens,eps,[wr1,wr2]):
  assert abs(en.real-J)<1e-14 and abs(ep.real-J)<1e-14
  for k in range(1,101):
   val=coeff(k,en,ep,wr,3)
   assert abs(val)<=3**(J+alpha)*k**(-J)*tau(k,6)+1e-12
   assert tau(k,6)**2<=tau(k,36);caps+=1
 X=3;N=9;t=1.3;s=.5+1j*t
 ts=list(itertools.product(range(1,X+1),range(1,N+1),range(1,N+1)))
 def wc(v,copy):
  d,m,n=v
  z,wr,wn,on,op=(z1,wr1,wn1,on1,op1) if copy==1 else (z2,wr2,wn2,on2,op2)
  un=s+z+wr;up=s+z+wn;qn=1-un if i else un;qp=1-up if j else up
  return ups(d)*nu(m,i)*d23(n,j)*d**(z-un)*m**(-qn-on)*n**(-qp-op)
 ww1={v:wc(v,1) for v in ts};ww2={v:wc(v,2) for v in ts}
 AC={k:coeff(k,ens[0],eps[0],wr1,X) for k in range(4,7)}
 BC={k:coeff(k,ens[1],eps[1],wr2,X) for k in range(7,10)}
 for p,g in [(5,2),(7,3)]:
  logs={pow(g,r,p):r for r in range(p-1)}
  def char(h,k):return 0j if k%p==0 else cmath.exp(2j*math.pi*h*logs[k%p]/(p-1))
  for a in [0,1]:
   direct=0j
   for (d,m,n),(e,mm,nn) in itertools.product(ts,repeat=2):
    x=d*m**(1-i)*n**(1-j)*mm**i*nn**j;y=e*m**i*n**j*mm**(1-i)*nn**(1-j)
    if not(4<=x<=6 and 7<=y<=9) or x%p==0 or y%p==0:continue
    K=(p-1)/2*(int((x-y)%p==0)+(-1)**a*int((x+y)%p==0))-int(a==0)
    direct+=ww1[d,m,n]*ww2[e,mm,nn].conjugate()*K
   poly=0j
   for h in range(1,p-1):
    if h%2!=a:continue
    aa=sum(AC[k]*char(h,k)*k**(-.5-1j*t) for k in AC)
    bb=sum(BC[k]*char(h,k)*k**(-.5-1j*t) for k in BC)
    poly+=aa*bb.conjugate()
   er=abs(direct-poly);assert er<1e-10;errs.append(er)
for jt in [2,12]:
 for i,j in itertools.product([0,1],repeat=2):
  ens=etas(i,z1+wr1,z2+wr2,jt+.23j,jt-.37j)
  eps=etas(j,z1+wn1,z2+wn2,jt-.19j,jt+.29j)
  for en,ep,wr in zip(ens,eps,[wr1,wr2]):
   assert en.real==jt and ep.real==jt
   for k in range(1,101):
    val=coeff(k,en,ep,wr,3)
    assert abs(val)<=3**(jt+alpha)*k**(-jt)*tau(k,6)+1e-24;caps+=1
out['literal_fixed_J_coefficients']={'cases':caps,'J_values':[2,3,12],'all_four_branches':True,'status':'PASS'}
out['actual_full_K_fixed_J_rectangle_identity']={'cases':len(errs),'max_error':max(errs),'status':'PASS'}
mp.mp.dps=40
gamma=[]
for j in [1,2,12]:
 for sig in [mp.mpf(1)/4,mp.mpf(3)/4]:
  for T in [-1000,-5,0,3,100,1000000]:
   for x in [-100,-T,-3,0,2,100]:
    b=mp.mpf('.017');u=mp.mpf(T)+b;xx=mp.mpf(x)
    logratio=mp.re(mp.loggamma(sig+j/2+1j*(u+xx)/2)-mp.loggamma(sig+1j*u/2))
    logenv=(mp.mpf(j)/2)*mp.log(1+abs(u))+(mp.mpf(j)/2+mp.mpf(1)/4)*mp.log(1+abs(xx))+mp.pi*abs(xx)/4
    norm=mp.exp(logratio-logenv)
    assert norm<mp.exp(20*j*mp.log(j+2));gamma.append(float(norm))
out['global_gamma_ratio_including_canceled_heights']={'cases':len(gamma),'maximum_normalized_ratio':max(gamma),'J_values':[1,2,12],'status':'PASS'}
shell=0
for j in [2,6,12]:
 for B in [100,1000,10000]:
  a=2**(-(2*j-1))*math.exp(36/B)
  upper=1/(1-a)
  partial=sum(2.0**(-(2*j-1)*r)*(1+r/B)**36 for r in range(151))
  assert partial<=upper+1e-14;shell+=1
out['infinite_shell_polynomial_majorant']={'cases':shell,'proof_majorant':'(1+r/B)^36 <= exp(36r/B), geometric ratio <1','status':'PASS'}
parts=0
for x,y in itertools.product(range(1,101),repeat=2):
 M=10;Y0=40
 ll=x>M and y>M;middle=ll and x<=Y0 and y<=Y0;highll=ll and max(x,y)>Y0
 assert ll==bool(middle+highll) and not(middle and highll)
 if max(x,y)>Y0 and not highll:assert max(x,y)/min(x,y)>Y0/M
 parts+=1
out['bounded_middle_bookkeeping']={'cases':parts,'restricted_principal_retained':True,'status':'PASS'}
out['status']='PASS'
ss=json.dumps(out,sort_keys=True,indent=2)+'\n';(ROOT/'CHECKS.json').write_text(ss);print(ss,end='')
