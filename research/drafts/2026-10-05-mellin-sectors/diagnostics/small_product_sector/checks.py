#!/usr/bin/env python3
"""Finite diagnostics, not an asymptotic or formal certificate."""
import cmath
import json
import math
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
from sympy import divisors, mobius, primitive_root

HERE=Path(__file__).resolve().parent
out={"diagnostic_only":True}

assert F(13)-F(4)-F(1,2)-7==F(3,2)
assert 4*F(3,2)==6
assert 13-14==-1
assert -8-14==-22
assert 5+14==19 and 5+8==13
assert 1+1-2*2==-2
assert 2+1-2*2==-1
assert F(928,15)+2==F(958,15)
assert F(32,5)+4==F(52,5)
assert F(958,15)+F(1,15)==F(959,15)<64
assert 12-2*2==8
assert F(1,2)+F(1,2)==1
out['exact_exponents']='PASS'

prime_cases=0
for B in [31,100,1000]:
 for p in [2,3,7,53,1009]:
  lp=math.log(p)
  for real_factor in [-2,-1,0,1,2]:
   a=real_factor/B
   for b in [-2.1,0,.1,1.7]:
    for K in [0,1,7]:
     beta=1j*K/B
     for q in [-1,0,1]:
      ref=(1+q)*(1-cmath.exp(1j*b*lp))
      actual=cmath.exp(-beta*lp)+q-(1+q)*cmath.exp((a+1j*b)*lp)
      assert abs(actual-ref)<=(K+4)*lp/B*p**(2/B)+1e-12
      ba=2+abs(actual);br=2+abs(ref)
      assert ba<=6*p**(2/B)+1e-12
      assert abs(ba*ba-br*br)<=12*(K+4)*lp/B*p**(4/B)+1e-10
      bound=4+(1+q)*(146/15-32/5*math.cos(b*lp))
      assert br*br<=bound+1e-12
      prime_cases+=1
out['positive_negative_shift_prime_checks']={'cases':prime_cases,'status':'PASS'}

def chi(n,D):
 r=n%D
 if r==0:return 0
 if D==3:return 1 if r==1 else -1
 if D==5:return 1 if r in (1,4) else -1
 raise ValueError(D)

def conv(a,b,n):return sum(a[d]*b[n//d] for d in divisors(n))

identity_count=0
max_head=0.0; max_dual=0.0
for D in [3,5]:
 lim=90; X=5; Y=29; S=7; B=41; alpha=1/B; xi=2/B
 mu=[0]+[int(mobius(n)) for n in range(1,lim+1)]
 muc=[0]+[mu[n]*chi(n,D) for n in range(1,lim+1)]
 ups=[0]+[conv(mu,muc,n) for n in range(1,lim+1)]
 ch=[0]+[chi(n,D) for n in range(1,lim+1)]
 beta=[1j*math.pi/B,-.7j/B,.2j/B]
 powers=[[0]+[cmath.exp(-bj*math.log(n)) for n in range(1,lim+1)] for bj in beta]
 nub=[0]+[conv(powers[0],ch,n) for n in range(1,lim+1)]
 d23=[0]+[conv(powers[1],powers[2],n) for n in range(1,lim+1)]
 p=7;g=int(primitive_root(p));logs={pow(g,e,p):e for e in range(p-1)}
 for character_index in [1,2]:
  def psi(n):return 0j if n%p==0 else cmath.exp(2j*math.pi*character_index*logs[n%p]/(p-1))
  for v,omega,T in [(.1,-.3,.7),(-1.2,.9,4.1),(0,0,-2.3)]:
   z=alpha+1j*v;w=alpha+1j*omega;u=.5+xi+1j*T
   for dual in [False,True]:
    shift=z+w-(2*xi if dual else 0)
    c=[0]+[sum(ups[d]*cmath.exp(shift*math.log(d))*nub[r//d] for d in divisors(r) if d<=X) for r in range(1,Y+1)]
    direct=0j;compressed=0j
    for r in range(1,Y+1):
     for n in range(1,S+1):
      k=r*n
      coeff=c[r]*d23[n]*cmath.exp((w-(2*xi if dual else 0))*math.log(n))
      compressed+=coeff*psi(k)*cmath.exp((-u-w+(2*xi if dual else 0))*math.log(k))
      for d in divisors(r):
       if d>X:continue
       m=r//d
       direct+=ups[d]*cmath.exp(z*math.log(d))*nub[m]*d23[n]*psi(k)*cmath.exp(-u*math.log(k))*cmath.exp(((2*xi if dual else 0)-w)*math.log(m))
    error=abs(direct-compressed)
    assert error<2e-12,(D,character_index,v,omega,dual,error)
    if dual:max_dual=max(max_dual,error)
    else:max_head=max(max_head,error)
    identity_count+=1
out['exact_head_dual_mellin_coefficient_identities']={'cases':identity_count,'max_head_error':max_head,'max_dual_error':max_dual,'both_psi_chi_parities':True,'status':'PASS'}

partition_checks=0
for D in [3,5]:
 M=70;X=5;R=13;S=7
 for a in [0,1]:
  for k in range(1,M+1):
   full=0j;parts=[0j,0j,0j];small=0j;inter=0j
   for d in divisors(k):
    if d>X:continue
    for m in divisors(k//d):
     n=k//d//m;r=d*m
     # A nonconstant complex weight tests the partition independently of positivity.
     weight=cmath.exp((-.03+1j*(a+.2))*(m*n))
     term=(int(mobius(d))+1j*chi(m,D))*weight*(1+.17j*n)
     full+=term
     index=0 if r<=R else (1 if n<=S else 2)
     parts[index]+=term
     if n<=S:small+=term
     if n<=S and r<=R:inter+=term
   assert abs(sum(parts)-full)<1e-11
   assert abs(small-inter-parts[1])<1e-11
   partition_checks+=1
out['disjoint_sector_and_literal_intersection']={'checks':partition_checks,'status':'PASS'}

mp.mp.dps=40
fe_checks=[]
for D in [3,5]:
 p=7;q=p*D;g=int(primitive_root(p));logs={pow(g,e,p):e for e in range(p-1)}
 for j in [1,2]:
  a=j%2;ac=(a+(1 if D==3 else 0))%2
  def psi(n):return mp.mpc(0) if n%p==0 else mp.exp(2j*mp.pi*j*logs[n%p]/(p-1))
  def mix(n):return chi(n,D)*psi(n)
  def Lfun(s,mod,fun):return mod**(-s)*sum(fun(n)*mp.zeta(s,mp.mpf(n)/mod) for n in range(1,mod+1) if fun(n)!=0)
  def eps(mod,fun,parity):return sum(fun(n)*mp.exp(2j*mp.pi*n/mod) for n in range(1,mod+1))/(1j**parity*mp.sqrt(mod))
  u=mp.mpf('.54')+.7j;beta=.013j
  ep=eps(p,psi,a);ec=eps(q,mix,ac)
  assert abs(abs(ep)-1)<mp.mpf('1e-35')
  assert abs(abs(ec)-1)<mp.mpf('1e-35')
  scalar=ep*ec*(mp.mpf(p)/mp.pi)**(mp.mpf('.5')-u-beta)*(mp.mpf(q)/mp.pi)**(mp.mpf('.5')-u)
  scalar*=mp.gamma((1-u-beta+a)/2)/mp.gamma((u+beta+a)/2)
  scalar*=mp.gamma((1-u+ac)/2)/mp.gamma((u+ac)/2)
  lhs=Lfun(u+beta,p,psi)*Lfun(u,q,mix)
  rhs=scalar*Lfun(1-u-beta,p,lambda n:mp.conj(psi(n)))*Lfun(1-u,q,lambda n:mp.conj(mix(n)))
  err=abs(lhs-rhs)
  assert err<mp.mpf('1e-30'),(D,j,err)
  fe_checks.append({'D':D,'psi_parity':a,'chi_psi_parity':ac,'error':float(err)})
out['actual_mixed_functional_equation_scalar']=fe_checks

gaussian=[]
for h in [mp.mpf('.2'),mp.mpf('.5')]:
 for x in [mp.mpf('.75'),mp.mpf(1),mp.mpf('1.3')]:
  eta=mp.mpf('.3')
  def integrand(y):
   w=eta+1j*y
   return mp.exp(h*h*w*w/2-w*mp.log(x))/w
  cut=12/h
  val=mp.quad(integrand,[-cut,-20,-5,-1,0,1,5,20,cut])/(2*mp.pi)
  target=mp.erfc(mp.log(x)/(mp.sqrt(2)*h))/2
  error=abs(val-target)
  assert error<mp.mpf('1e-28'),(h,x,error)
  if x==1:assert target==mp.mpf('.5')
  gaussian.append({'h':str(h),'x':str(x),'error':float(error),'endpoint_half_weight':x==1})
out['gaussian_mellin_kernel_and_endpoint']=gaussian

moment=mp.quad(lambda t: mp.sqrt(t)*mp.exp(-t*t/2)*2/mp.sqrt(2*mp.pi),[0,1,mp.inf])
expected=2**mp.mpf('.25')*mp.gamma(mp.mpf('.75'))/mp.sqrt(mp.pi)
assert abs(moment-expected)<mp.mpf('1e-35')
out['gaussian_boundary_moment']={'E_sqrt_abs_Z':float(moment),'status':'PASS'}

# Two-sided endpoint geometry and fixed-ratio largest-factor covering.
geometry=0
for h in [.001,.03,.2]:
 for Z in [-1/h,-.3/h,-1,0,1,.3/h,1/h]:
  M=1000;lo=min(M,M*math.exp(h*Z));hi=max(M,M*math.exp(h*Z))
  assert lo>=M/math.e-1e-9 and hi<=math.e*M+1e-9
  assert hi-lo<=math.e*M*h*abs(Z)+1e-9
  geometry+=1
out['two_sided_fixed_ratio_boundary']={'checks':geometry,'status':'PASS'}

out['status']='PASS'
(HERE/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
