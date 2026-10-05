#!/usr/bin/env python3
"""Finite consistency checks, not asymptotic certification or an A2022 example."""
import cmath, itertools, json, math
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
ROOT=Path(__file__).resolve().parent
out={'diagnostic_only':True,'sample_does_not_assume_A2022':True}
assert -395+9*35==-80 and -80+402-400==-78
assert F(928,15)+2==F(958,15)<F(959,15)<64
out['exact_power_ledger']='PASS'

# Rational e^delta=5/4 makes all test boundaries exact, including integers.
geom=0;inside_far=0
for M in [4,5,20,25]:
 for x in range(1,101):
  for y in range(1,101):
   sl=x<=M<y
   rect=F(4*M,5)<=x<=M and M<y<=F(5*M,4)
   assert not rect or sl
   if sl and not rect: assert F(y,x)>F(5,4)
   if rect and F(y,x)>F(5,4):inside_far+=1
   geom+=1
assert inside_far>0
out['complete_rectangle_replacement']={'cases':geom,'retained_far_rectangle_pairs':inside_far,'status':'PASS'}

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
# Verify exact finite majorant preceding every asymptotic harmonic estimate.
hyp=0
for q in [2,3,6,36]:
 for x in [10,31,100,301]:
  Q=0
  while (Q+1)**q<=(2*x)**(q-1):Q+=1
  for h in [1,3,x//2,x]:
   lhs=sum(tau(n,q) for n in range(x,x+h+1))
   rhs=q*sum(tau(u,q-1)*(F(h,u)+1) for u in range(1,Q+1))
   assert lhs<=rhs
   hyp+=1
out['closed_interval_largest_factor_hyperbola']={'cases':hyp,'q_includes_36':True,'status':'PASS'}

alpha=.025;bet=[.011j,.021j,.032j]
z1=alpha+.17j;wr1=-alpha+.10j;wn1=-alpha-.30j
z2=alpha-.13j;wr2=-alpha-.18j;wn2=-alpha+.55j
on1=alpha+.23j;on2=alpha-.37j;op1=alpha-.19j;op2=alpha+.29j
@lru_cache(None)
def nu(n,dual=0):return sum(d**((1 if dual else -1)*bet[0])*chi(n//d) for d in divisors(n))
@lru_cache(None)
def d23(n,dual=0):return sum(cmath.exp((1 if dual else -1)*(bet[1]*math.log(d)+bet[2]*math.log(n//d))) for d in divisors(n))
def etas(bit,k1,k2,w1,w2):return (k1+w1,k2+w2) if not bit else (k2+w2.conjugate(),k1+w1.conjugate())
def coeff(k,en,ep,wr,X):return sum(ups(d)*d**(-wr)*nu(m)*m**(-en)*d23(k//d//m)*(k//d//m)**(-ep) for d in divisors(k) if d<=X for m in divisors(k//d))
caps=0;errs=[];kern=0
for i,j in itertools.product([0,1],repeat=2):
 ens=etas(i,z1+wr1,z2+wr2,on1,on2);eps=etas(j,z1+wn1,z2+wn2,op1,op2)
 for en,ep,wr in zip(ens,eps,[wr1,wr2]):
  for k in range(1,101):
   val=coeff(k,en,ep,wr,81)
   assert abs(val)<=81**alpha*tau(k,6)+1e-10
   assert tau(k,6)**2<=tau(k,36)
   caps+=1
 # Direct original tuple expansion on a mixed finite rectangle.
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
   polynomial=0j
   for h in range(1,p-1):
    if h%2!=a:continue
    aa=sum(AC[k]*char(h,k)*k**(-.5-1j*t) for k in AC)
    bb=sum(BC[k]*char(h,k)*k**(-.5-1j*t) for k in BC)
    polynomial+=aa*bb.conjugate()
   er=abs(direct-polynomial);assert er<1e-8;errs.append(er)
   reverse=sum(BC[y]*AC[x].conjugate()*(x*y)**(-.5)*cmath.exp(1j*t*math.log(x/y))*((p-1)/2*(int((x-y)%p==0)+(-1)**a*int((x+y)%p==0))-int(a==0)) for x in AC for y in BC if x%p and y%p)
   assert abs(reverse-polynomial.conjugate())<1e-8;kern+=1
out['finite_G_coefficient_caps']={'cases':caps,'all_four_branches':True,'status':'PASS'}
out['literal_full_K_mixed_rectangle_identity']={'cases':len(errs),'max_error':max(errs),'both_parities_and_unit_masks':True,'status':'PASS'}
out['conjugate_mixed_rectangles']={'cases':kern,'status':'PASS'}
parts=0
for x,y in itertools.product(range(1,41),repeat=2):
 ss=x<=20 and y<=20;sl=x<=20<y;ls=y<=20<x;ll=x>20 and y>20
 assert sum([ss,sl,ls,ll])==1
 eq=ll and x==y;far=ll and abs(math.log(y/x))>math.log(1.25);near=ll and not eq and not far
 assert sum([ss,sl,ls,eq,far,near])==1;parts+=1
out['exact_remaining_LL_partition']={'cases':parts,'full_K_retained':True,'status':'PASS'}
out['status']='PASS'
ss=json.dumps(out,sort_keys=True,indent=2)+'\n';(ROOT/'CHECKS.json').write_text(ss);print(ss,end='')
