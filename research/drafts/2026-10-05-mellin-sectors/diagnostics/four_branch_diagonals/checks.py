#!/usr/bin/env python3
"""Finite tests only; REPORT.md supplies the arithmetic and analytic proof."""
import cmath,json,math
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import mpmath as mp
from sympy import divisors,factorint,mobius,kronecker_symbol
HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True}
assert 4*9+2*16==68
assert F(4)+F(1,2)==F(9,2)
assert 68-68==0
assert F(959,15)<64
out['exact_arithmetic_and_prime_width_exponents']='PASS'

local_checks=0;perturb_checks=0
for chi in [-1,0,1]:
 for phase in [-30,-7,-1,-.01,0,.03,2,9,30]:
  nu=[abs(sum(cmath.exp(-1j*phase*r)*chi**(e-r) for r in range(e+1))) for e in range(13)]
  ups=[1,1+chi,abs(chi)]+[0]*10
  aa=[]
  for e in range(13):
   val=sum(ups[d]*nu[m]*(e-d-m+1) for d in range(e+1) for m in range(e-d+1))
   aa.append(val)
   assert val<=math.comb(e+5,5)+1e-9
   local_checks+=1
  a0=2*(1+chi)+2
  assert abs(aa[1]-(1+chi+abs(cmath.exp(-1j*phase)+chi)+2))<1e-12
  assert a0*a0<=4+16*(1+chi)
  assert aa[1]**2<=4+16*(1+chi)+12*abs(phase)+1e-10
  perturb_checks+=1
out['actual_local_coefficients_higher_powers_and_ramification']={'cases':local_checks,'prime_perturbation_cases':perturb_checks,'status':'PASS'}

mp.mp.dps=32
@lru_cache(None)
def chi(disc,n):return int(kronecker_symbol(disc,n))
@lru_cache(None)
def ups(disc,n):return sum(int(mobius(d))*int(mobius(n//d))*chi(disc,n//d) for d in divisors(n))
@lru_cache(None)
def tau(k,n):
 val=1
 for e in factorint(n).values():val*=math.comb(e+k-1,k-1)
 return val
@lru_cache(None)
def nu(disc,n,sign=1):return sum(mp.exp(-sign*mp.mpc(0,'.017')*mp.log(d))*chi(disc,n//d) for d in divisors(n))
@lru_cache(None)
def arith(disc,k):return sum(abs(ups(disc,d))*abs(nu(disc,m))*tau(2,k//d//m) for d in divisors(k) for m in divisors(k//d))
rankin=0;conj=0;mult=0
X=12;Qnu=mp.mpf('10');Q=mp.mpf('7');delta=mp.mpf('.1');J=4
th=lambda x:min(mp.mpf(1),x**(-J))
for disc in [-3,5,8,12]:
 for k in range(1,121):
  a=arith(disc,k)
  assert a<=tau(6,k)+mp.mpf('1e-25')
  weighted=sum(abs(ups(disc,d))*abs(nu(disc,m))*tau(2,k//d//m)*th(m/Qnu)*th((k//d//m)/Q) for d in divisors(k) if d<=X for m in divisors(k//d))
  bound=(X*Qnu*Q/k)**(delta/2)*a
  assert weighted<=bound+mp.mpf('1e-25')
  assert abs(nu(disc,k,-1)-mp.conj(nu(disc,k,1)))<mp.mpf('1e-26')
  rankin+=1;conj+=1
 for m in range(1,11):
  for n in range(1,11):
   if math.gcd(m,n)==1:
    assert abs(arith(disc,m*n)-arith(disc,m)*arith(disc,n))<mp.mpf('1e-25')
    mult+=1
out['single_Rankin_weight_and_full_arithmetic_majorant']={'cases':rankin,'status':'PASS'}
out['dual_coefficient_conjugacy_and_multiplicativity']={'conjugacy_cases':conj,'multiplicativity_cases':mult,'status':'PASS'}

swaps=0
for i in [0,1]:
 for j in [0,1]:
  for d in [1,2,3]:
   for e in [1,2,3]:
    for m in [1,2,3,4]:
     for n in [1,2,3,4]:
      for mm in [1,2,3,4]:
       for nn in [1,2,3,4]:
        x=d*m**(1-i)*n**(1-j)*mm**i*nn**j
        y=e*m**i*n**j*mm**(1-i)*nn**(1-j)
        M,MM=(mm,m) if i else (m,mm)
        N,NN=(nn,n) if j else (n,nn)
        assert (x==y)==(d*M*N==e*MM*NN)
        old=th(m/Qnu)*th(mm/Qnu)*th(n/Q)*th(nn/Q)
        new=th(M/Qnu)*th(MM/Qnu)*th(N/Q)*th(NN/Q)
        assert abs(old-new)<mp.mpf('1e-28')
        swaps+=1
out['four_equality_swaps_and_symmetric_decay']={'cases':swaps,'status':'PASS'}

fibers=0
for p in [5,7,11]:
 for a in [0,1]:
  for i in [0,1]:
   for j in [0,1]:
    tuples=[(d,m,n) for d in range(1,4) for m in range(1,5) for n in range(1,5) if d*m*n%p]
    ws={v:complex(v[0]+v[1]-2*v[2],(v[0]*v[1]+v[2])%5-2) for v in tuples}
    grouped={}
    for d,m,n in tuples:
     lam=F(d)*F(m)**(1-2*i)*F(n)**(1-2*j)
     grouped[lam]=grouped.get(lam,0j)+ws[d,m,n]
    const=F(p-1,2)-int(a==0)
    fiber_value=float(const)*sum(abs(v)**2 for v in grouped.values())
    direct=0j
    for d,m,n in tuples:
     for e,mm,nn in tuples:
      x=d*m**(1-i)*n**(1-j)*mm**i*nn**j
      y=e*m**i*n**j*mm**(1-i)*nn**(1-j)
      if x==y:
       K=(p-1)/2*(int((x-y)%p==0)+(-1)**a*int((x+y)%p==0))-int(a==0)
       direct+=K*ws[d,m,n]*ws[e,mm,nn].conjugate()
    assert abs(direct-fiber_value)<1e-8 and direct.real>=0 and abs(direct.imag)<1e-10
    fibers+=1
out['full_kernel_positive_rational_fibers']={'cases':fibers,'status':'PASS'}

windows=0
for lo in [F(10),F(101,10),F(103,10),F(100)]:
 for width in [F(1,10),F(1),F(23,10),F(10)]:
  hi=lo+width
  ints=[k for k in range(math.floor(lo)-1,math.ceil(hi)+1) if lo<k<hi]
  assert len(ints)<=width+1
  assert sum(ints)<=hi*(width+1)
  windows+=1
out['literal_open_interval_width_and_endpoint']={'cases':windows,'status':'PASS'}

rankinfactors=[]
for L in [3,5,10,20]:
 B=mp.mpf(L)**9
 logt=mp.log(2*mp.pi)+519*mp.log(L);logh=405*mp.log(L)
 logtime=logt+mp.log(1+mp.exp(logh-logt)+mp.exp(-logt))
 logQ=B+mp.log(2)+logtime
 logfactor=(mp.mpf('4.5')*L+2*logQ)/B
 assert logfactor<3
 rankinfactors.append(float(logfactor))
out['global_actual_scale_Rankin_factor']={'log_factors':rankinfactors,'status':'PASS'}

out['status']='PASS'
s=json.dumps(out,indent=2,sort_keys=True)+'\n';(HERE/'CHECKS.json').write_text(s);print(s,end='')
