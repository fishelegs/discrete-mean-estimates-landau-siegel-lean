#!/usr/bin/env python3
"""Finite exact coefficient/gamma/kernel tests; not an A2022 numerical example."""
import cmath,json,math,itertools
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import mpmath as mp
from sympy import divisors,mobius,kronecker_symbol
HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True}
assert F(36)+F(292,15)+F(32,5)==F(928,15)
assert F(32,5)+10==F(82,5)
assert F(928,15)+2==F(958,15)
assert F(958,15)+F(1,15)==F(959,15)<64
assert -F(2011,2)+72+288==-F(1291,2)
assert 12-2==10 and 12-4==8
assert F(4,16)<=1
out['exact_energy_Rankin_tail_and_final_exponents']='PASS'

mp.mp.dps=32
alpha=mp.mpf(1)/40;beta=[mp.mpc(0,'.011'),mp.mpc(0,'.021'),mp.mpc(0,'.032')]
z1=alpha+mp.mpc(0,'.17');wr1=-alpha+mp.mpc(0,'.10');wn1=-alpha+mp.mpc(0,'-.30')
z2=alpha+mp.mpc(0,'-.13');wr2=-alpha+mp.mpc(0,'-.18');wn2=-alpha+mp.mpc(0,'.55')
on1=alpha+mp.mpc(0,'.23');on2=alpha+mp.mpc(0,'-.37');op1=alpha+mp.mpc(0,'-.19');op2=alpha+mp.mpc(0,'.29')
@lru_cache(None)
def chi(n):return int(kronecker_symbol(-3,n))
@lru_cache(None)
def ups(n):return sum(int(mobius(d))*int(mobius(n//d))*chi(n//d) for d in divisors(n))
@lru_cache(None)
def nu(n,dual=0):return sum(mp.exp((1 if dual else -1)*beta[0]*mp.log(d))*chi(n//d) for d in divisors(n))
@lru_cache(None)
def d23(n,dual=0):return sum(mp.exp((1 if dual else -1)*(beta[1]*mp.log(d)+beta[2]*mp.log(n//d))) for d in divisors(n))
@lru_cache(None)
def nu0(n):return sum(chi(n//d) for d in divisors(n))
def etas(bit,k1,k2,w1,w2):return (k1+w1,k2+w2) if not bit else (k2+mp.conj(w2),k1+mp.conj(w1))
def cc(r,phi,X):return sum(ups(d)*mp.exp(phi*mp.log(d))*nu(r//d) for d in divisors(r) if d<=X)
def coeff(k,en,ep,wr,X):return sum(ups(d)*mp.exp(-wr*mp.log(d))*nu(m)*mp.exp(-en*mp.log(m))*d23(k//d//m)*mp.exp(-ep*mp.log(k//d//m)) for d in divisors(k) if d<=X for m in divisors(k//d))
errors=[];finite=0
for i in [0,1]:
 for j in [0,1]:
  ens=etas(i,z1+wr1,z2+wr2,on1,on2);eps=etas(j,z1+wn1,z2+wn2,op1,op2)
  for en,ep,wr in zip(ens,eps,[wr1,wr2]):
   phi=en-wr
   assert abs(mp.re(en)-alpha)<mp.mpf('1e-30') and abs(mp.re(ep)-alpha)<mp.mpf('1e-30')
   assert abs(mp.re(phi)-2*alpha)<mp.mpf('1e-30')
   for k in range(1,101):
    direct=coeff(k,en,ep,wr,81)
    grouped=mp.exp(-ep*mp.log(k))*sum(mp.exp((ep-en)*mp.log(r))*cc(r,phi,81)*d23(k//r) for r in divisors(k))
    er=abs(direct-grouped);assert er<mp.mpf('1e-23');errors.append(float(er))
    tail=abs(cc(k,phi,k)-cc(k,phi,81))
    upper=100**(2*alpha)*sum(nu0(d)*len(divisors(k//d)) for d in divisors(k) if 81<d<=100)
    assert tail<=upper+mp.mpf('1e-24');finite+=1
out['exact_c_phi_grouping_all_four_branches']={'cases':len(errors),'max_error':max(errors),'literal_sample_cutoff':81,'status':'PASS'}
out['finite_inverse_restoration_pointwise_majorant']={'cases':finite,'sample_does_not_assume_A2022':True,'status':'PASS'}

corners=0;maxphi=0
for vals in itertools.product([-1,1],repeat=6):
 v1,y1,x1,v2,y2,x2=vals
 for i in [0,1]:
  pa,pb=(v1+x1,v2+x2) if not i else (v2+y2-x2-y1,v1+y1-x1-y2)
  assert abs(pa)<=4 and abs(pb)<=4
  maxphi=max(maxphi,abs(pa),abs(pb));corners+=1
out['combined_reciprocal_height_box']={'corner_cases':corners,'maximum_in_units_of_V0':maxphi,'ratio_to_L5':str(F(maxphi,16)),'status':'PASS'}

primechecks=0;higher=0
for p in [2,3,5,11,101]:
 for h in [-1,0,1]:
  for v in [-2,-.3,0,.17,1.2]:
   phi=2*alpha+1j*v;phase=mp.exp(1j*v*mp.log(p));bref=2+(1+h)*abs(1-phase);y=1-mp.cos(v*mp.log(p))
   reference=4+(1+h)*(mp.mpf(146)/15-mp.mpf(32)/5*mp.cos(v*mp.log(p)))
   assert bref*bref<=reference+mp.mpf('1e-25')
   cp=p**(-beta[0])+h-(1+h)*p**phi;bact=2+abs(cp)
   assert abs(bact*bact-bref*bref)<=12*(1+4)*alpha*mp.log(p)*p**(4*alpha)+mp.mpf('1e-24')
   primechecks+=1
   cs=[]
   for e in range(9):
    cv=0j
    for d in range(min(2,e)+1):
     up=[1,-(1+h),h][d]
     nn=sum(p**(-beta[0]*r)*h**(e-d-r) for r in range(e-d+1))
     cv+=up*p**(d*phi)*nn
    cs.append(cv)
    bb=sum(abs(cs[r])*(e-r+1) for r in range(e+1))
    assert bb<=p**(2*alpha*e)*math.comb(e+5,5)+mp.mpf('1e-22');higher+=1
out['shifted_prime_majorant_and_uniform_higher_powers']={'prime_cases':primechecks,'higher_power_cases':higher,'status':'PASS'}

ratios=[]
for a in [0,1]:
 for c in [0,1]:
  for T in [-1000,1000]:
   for x in [-20,-3,0,.2,3,20]:
    q=mp.mpf('.5')+1j*T;om=alpha+1j*x
    # Positive conductor sample tests only the analytic kernel inequality.
    C=mp.exp(40)*mp.sqrt(5)/mp.pi
    lg=0
    for shift,par in [(beta[0],a),(0,(a+c)%2)]:
     lg+=mp.re(mp.loggamma((q+shift+par+om)/2)-mp.loggamma((q+shift+par)/2))
    ratio=mp.exp(alpha*mp.log(C)+alpha**2-mp.mpf(x)**2/2+lg)
    assert ratio<mp.exp(10);ratios.append(float(ratio))
out['sharp_inner_gamma_Gaussian_envelope']={'cases':len(ratios),'maximum_normalized_ratio':max(ratios),'all_parities_and_height_signs':True,'status':'PASS'}

# Exact full-K rectangle and common-polynomial representation after relabeling.
M=6;X=3;t=mp.mpf('1.3');s=mp.mpf('.5')+1j*t
recterrs=[]
for i in [0,1]:
 for j in [0,1]:
  ens=etas(i,z1+wr1,z2+wr2,on1,on2);eps=etas(j,z1+wn1,z2+wn2,op1,op2)
  AC={k:complex(coeff(k,ens[0],eps[0],wr1,X)) for k in range(1,M+1)}
  BC={k:complex(coeff(k,ens[1],eps[1],wr2,X)) for k in range(1,M+1)}
  ts=[(d,m,n) for d in range(1,X+1) for m in range(1,M+1) for n in range(1,M+1)]
  def wc(tup,copy):
   d,m,n=tup
   z,wr,wn,on,op=(z1,wr1,wn1,on1,op1) if copy==1 else (z2,wr2,wn2,on2,op2)
   un=s+z+wr;up=s+z+wn;qn=1-un if i else un;qp=1-up if j else up
   return complex(ups(d)*nu(m,i)*d23(n,j)*d**(z-un)*m**(-qn-on)*n**(-qp-op))
  ww1={v:wc(v,1) for v in ts};ww2={v:wc(v,2) for v in ts}
  for p,g in [(5,2),(7,3)]:
   logs={pow(g,r,p):r for r in range(p-1)}
   def char(h,k):return 0j if k%p==0 else cmath.exp(2j*math.pi*h*logs[k%p]/(p-1))
   for a in [0,1]:
    direct=0j
    for d,m,n in ts:
     for e,mm,nn in ts:
      x=d*m**(1-i)*n**(1-j)*mm**i*nn**j;y=e*m**i*n**j*mm**(1-i)*nn**(1-j)
      if x>M or y>M or x%p==0 or y%p==0:continue
      K=(p-1)/2*(int((x-y)%p==0)+(-1)**a*int((x+y)%p==0))-int(a==0)
      direct+=ww1[d,m,n]*ww2[e,mm,nn].conjugate()*K
    polynomial=0j
    for h in range(1,p-1):
     if h%2!=a:continue
     aa=sum(AC[k]*char(h,k)*k**(-.5-1j*float(t)) for k in AC)
     bb=sum(BC[k]*char(h,k)*k**(-.5-1j*float(t)) for k in BC)
     polynomial+=aa*bb.conjugate()
    er=abs(direct-polynomial);assert er<1e-8;recterrs.append(er)
out['actual_full_kernel_small_rectangle_bilinear_identity']={'cases':len(recterrs),'max_error':max(recterrs),'principal_subtraction_retained':True,'status':'PASS'}

partitions=0
for i in [0,1]:
 for j in [0,1]:
  for vals in itertools.product(range(1,4),repeat=6):
   d,m,n,e,mm,nn=vals;x=d*m**(1-i)*n**(1-j)*mm**i*nn**j;y=e*m**i*n**j*mm**(1-i)*nn**(1-j)
   ss=x<=5 and y<=5;comp=not ss;eq=x==y;far=abs(math.log(y/x))>.3
   masks=[ss,comp and eq,comp and far,comp and not eq and not far]
   assert sum(masks)==1;partitions+=1
out['full_kernel_high_mixed_near_remaining_partition']={'tuple_cases':partitions,'restricted_principal_not_removed':True,'status':'PASS'}
out['status']='PASS'
ss=json.dumps(out,indent=2,sort_keys=True)+'\n';(HERE/'CHECKS.json').write_text(ss);print(ss,end='')
