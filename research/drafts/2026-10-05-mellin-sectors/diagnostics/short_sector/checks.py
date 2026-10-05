#!/usr/bin/env python3
"""Finite diagnostics; these do not certify the asymptotic source proof."""
import cmath
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp
from sympy import divisors, mobius, primitive_root

HERE = Path(__file__).resolve().parent
out = {"diagnostic_only": True}

assert F(36)+2*F(146,15)+F(32,5)==F(928,15)
assert F(928,15)+2==F(958,15)
assert F(958,15)+F(1,15)==F(959,15)<64
assert F(32,5)+2==F(42,5)
assert -F(2011,2)+72==-F(1867,2)
assert -F(1867,4)+16*9==-F(1291,4)
assert F(35,36)*2==F(35,18)
assert 2-F(35,18)==F(1,18)
assert F(35,36)*5==F(175,36)
assert F(8,2)+2==6
out["exact_exponents"]="PASS"

prime_cases=0
minimum_gap=100.0
for q in [-1,0,1]:
    phases=[j*math.pi/400 for j in range(-800,801)]
    phases += [math.acos(-7/18),-math.acos(-7/18)]
    for phase in phases:
        d=abs(1-cmath.exp(1j*phase))
        lhs=(2+(1+q)*d)**2
        rhs=4+(1+q)*(146/15-32/5*math.cos(phase))
        assert lhs<=rhs+3e-13,(q,phase,lhs,rhs)
        minimum_gap=min(minimum_gap,rhs-lhs)
        prime_cases+=1
out["prime_majorant"]={"cases":prime_cases,"minimum_gap":minimum_gap,"ramified_included":True}

perturb_cases=0
for B in [31,100,1000]:
    alpha=1/B
    for p in [2,3,7,53,1009,10**12+39]:
        lp=math.log(p)
        for K in [0,1,7]:
            beta=1j*K/B
            for v in [-2,-.01,0,.73,10]:
                u=cmath.exp(1j*v*lp)
                for q in [-1,0,1]:
                    actual=cmath.exp(-beta*lp)+q-(1+q)*p**alpha*u
                    ref=(1+q)*(1-u)
                    bound=(K+2)*lp/B*p**alpha
                    assert abs(actual-ref)<=bound+1e-12
                    actual_b=2+abs(actual)
                    ref_b=2+abs(ref)
                    assert actual_b<=6*p**alpha+1e-12
                    assert abs(actual_b**2-ref_b**2)<=12*(K+2)*lp/B*p**(2*alpha)+1e-11
                    # Direct local convolution against numerator (1-wT)(1-qwT).
                    w=p**alpha*u
                    nu=[sum(cmath.exp(-beta*lp*j)*q**(e-j) for j in range(e+1)) for e in range(9)]
                    cv=[]
                    for e in range(9):
                        c=nu[e]
                        if e>=1:c-=(1+q)*w*nu[e-1]
                        if e>=2:c+=q*w*w*nu[e-2]
                        cv.append(c)
                        assert abs(c)<=p**(e*alpha)*math.comb(e+3,3)+1e-8
                        bz=sum(abs(cv[j])*(e-j+1) for j in range(e+1))
                        assert bz<=p**(e*alpha)*math.comb(e+5,5)+1e-7
                    assert abs(cv[1]-actual)<1e-10
                    perturb_cases+=1
out["shifted_prime_and_power_checks"]={"cases":perturb_cases,"orders":8,"status":"PASS"}

divisor_checks=0
for e in range(0,101):
    t2=e+1;t4=math.comb(e+3,3);t6=math.comb(e+5,5)
    assert t2**4<=math.comb(e+15,15)
    assert t4*t4*t2<=math.comb(e+31,31)
    assert t6*t6<=math.comb(e+35,35)
    divisor_checks+=3
out["divisor_inequalities"]={"checks":divisor_checks,"status":"PASS"}

def chi(n,D):
    r=n%D
    if r==0:return 0
    if D==3:return 1 if r==1 else -1
    if D==5:return 1 if r in (1,4) else -1
    raise ValueError(D)

def conv(a,b,n):return sum(a[d]*b[n//d] for d in divisors(n))

tuple_checks=0
finite_tail_checks=0
max_tuple_error=0.0
max_original_mask_error=0.0
for D in [3,5]:
    M=84; X=5; R=23; B=37; alpha=1/B
    mu=[0]+[int(mobius(n)) for n in range(1,M+1)]
    muc=[0]+[mu[n]*chi(n,D) for n in range(1,M+1)]
    ups=[0]+[conv(mu,muc,n) for n in range(1,M+1)]
    one=[0]+[1]*M
    ch=[0]+[chi(n,D) for n in range(1,M+1)]
    nu=[0]+[conv(one,ch,n) for n in range(1,M+1)]
    betas=[1j*math.pi/B,1j*.4/B,-1j*.7/B]
    powers=[[0]+[cmath.exp(-b*math.log(n)) for n in range(1,M+1)] for b in betas]
    nub=[0]+[conv(powers[0],ch,n) for n in range(1,M+1)]
    d23=[0]+[conv(powers[1],powers[2],n) for n in range(1,M+1)]
    tau2=[0]+[len(divisors(n)) for n in range(1,M+1)]
    tau4=[0]+[conv(tau2,tau2,n) for n in range(1,M+1)]
    tau6=[0]+[conv(tau4,tau2,n) for n in range(1,M+1)]
    for v in [-2.1,0,.017,1.3]:
        z=alpha+1j*v
        uz=[0]+[ups[n]*cmath.exp(z*math.log(n)) for n in range(1,M+1)]
        ux=[0]+[uz[n] if n<=X else 0 for n in range(1,M+1)]
        c=[0]+[conv(uz,nub,n) for n in range(1,M+1)]
        cx=[0]+[conv(ux,nub,n) for n in range(1,M+1)]
        for r in range(1,R+1):
            tail=sum(nu[d]*tau2[r//d] for d in divisors(r) if X<d<=R)
            assert abs(cx[r]-c[r])<=math.e*tail+1e-11
            assert abs(cx[r])<=math.e*tau4[r]+1e-11
            finite_tail_checks+=1
        for k in range(1,M+1):
            short=sum(cx[r]*d23[k//r] for r in divisors(k) if r<=R)
            long=sum(cx[r]*d23[k//r] for r in divisors(k) if r>R)
            full=sum(cx[r]*d23[k//r] for r in divisors(k))
            direct=0j
            # Compare the exact Mellin integrand of (1.3) with (1.1).
            for d in divisors(k):
                if d>X:continue
                for m in divisors(k//d):
                    n=k//d//m
                    if d*m<=R:
                        direct+=ups[d]*nub[m]*d23[n]*cmath.exp(-z*math.log(m*n))
            error=abs(direct-short*cmath.exp(-z*math.log(k)))
            max_tuple_error=max(max_tuple_error,error)
            assert error<1e-10
            assert abs(short+long-full)<1e-10
            coarse=sum(abs(cx[r])*tau2[k//r] for r in divisors(k) if r<=R)
            assert coarse<=math.e*tau6[k]+1e-10
            tuple_checks+=1
out["finite_masks_and_original_tuple_identity"]={"tuple_checks":tuple_checks,"tail_checks":finite_tail_checks,"max_error":max_tuple_error,"status":"PASS"}

parity_checks=0
for p in [5,7,11,13]:
    g=int(primitive_root(p))
    logs={pow(g,e,p):e for e in range(p-1)}
    def char(j,n):
        return 0j if n%p==0 else cmath.exp(2j*math.pi*j*logs[n%p]/(p-1))
    for a in [0,1]:
        chars=[j for j in range(1,p-1) if j%2==a]
        for k in range(1,2*p+1):
            for l in range(1,2*p+1):
                actual=sum(char(j,k)*char(j,l).conjugate() for j in chars)
                target=0 if (k*l)%p==0 else (p-1)/2*((k-l)%p==0)+(0 if (k*l)%p==0 else (-1)**a*(p-1)/2*((k+l)%p==0))-(1 if a==0 and (k*l)%p!=0 else 0)
                assert abs(actual-target)<1e-11
                if k==l and k%p:
                    assert target==(p-1)/2-(a==0)
                parity_checks+=1
out["both_parity_projector_and_actual_diagonal"]={"checks":parity_checks,"status":"PASS"}

# Test the exact largest-factor covering rather than guessing its asymptotic constant.
cover_checks=0
for j in [2,3,4,6,36]:
    for n in range(2,160):
        # Selected ordered factorizations, padded with ones, include ties and a single large factor.
        for d in divisors(n):
            coords=[d,n//d]+[1]*(j-2)
            largest=max(coords)
            remaining=n//largest
            assert remaining**j<=n**(j-1)
            cover_checks+=1
out["largest_factor_covering"]={"checks":cover_checks,"status":"PASS"}

mp.mp.dps=35
gamma_checks=0
largest_log_normalized=-mp.inf
for B in [100,1000]:
    alpha=mp.mpf(1)/B
    L=mp.mpf(B)**(mp.mpf(1)/9)
    logC=2*B+L/2-2*mp.log(mp.pi)
    for t in [3,20,200]:
        for a in [0,1]:
            for parity_chi in [0,1]:
                aa=[a,a,a,(a+parity_chi)%2]
                shifts=[mp.mpf('.1')/B,mp.mpf('-.2')/B,mp.mpf('.3')/B,mp.mpf('0')]
                for v in [0,alpha,-alpha,mp.mpf('.1'),-1,1,-t,t,-t-1,-t+1]:
                    z=alpha+1j*v
                    logratio=mp.mpf('0')
                    for aj,bj in zip(aa,shifts):
                        base=(mp.mpf('.5')+aj+1j*(t+bj))/2
                        logratio+=mp.re(mp.loggamma(base+z/2)-mp.loggamma(base))
                    # |H4| |z| exp(v^2/2), computed without numerical overflow.
                    logged=alpha**2-v*v/2+alpha*logC+logratio
                    assert mp.isfinite(logged)
                    largest_log_normalized=max(largest_log_normalized,logged)
                    gamma_checks+=1
out["original_four_gamma_envelope_samples"]={"cases":gamma_checks,"max_log_normalized":float(largest_log_normalized),"note":"Finite samples only; uniform proof is REPORT section 8"}

def V4(line,x,a,parity_chi):
    p=mp.mpf(7); D=mp.mpf(5); t=mp.mpf(8)
    betas=[mp.mpf('.013'),mp.mpf('-.021'),mp.mpf('.031'),mp.mpf(0)]
    aa=[a,a,a,(a+parity_chi)%2]
    bases=[(mp.mpf('.5')+aj+1j*(t+bj))/2 for aj,bj in zip(aa,betas)]
    lc=mp.log(p*p*mp.sqrt(D)/(mp.pi**2*x))
    def f(v):
        z=mp.mpf(line)+1j*v
        lg=z*z+lc*z+sum(mp.loggamma(b+z/2)-mp.loggamma(b) for b in bases)
        return mp.exp(lg)/z
    return mp.quad(f,[-16,-8,-3,-1,0,1,3,8,16])/(2*mp.pi)

contour=[]
for a,pc in [(0,0),(0,1),(1,0),(1,1)]:
    left=V4('.2',3,a,pc)
    right=V4('2',3,a,pc)
    error=abs(left-right)
    assert error<mp.mpf('1e-20'),(a,pc,error)
    contour.append({"psi_parity":a,"chi_parity":pc,"error":float(error)})
out["actual_V4_positive_contour_shift"]=contour

out["status"]="PASS"
(HERE/"CHECKS.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
