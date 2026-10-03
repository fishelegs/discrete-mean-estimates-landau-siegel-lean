#!/usr/bin/env python3
"""Independent finite regression checks; no Lean or asymptotic certification."""
from fractions import Fraction as F
from math import gcd, comb
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent

def factor(n):
    ans = []
    q = 2
    while q*q <= n:
        if n % q == 0:
            k = 0
            while n % q == 0:
                n //= q
                k += 1
            ans.append((q,k))
        q += 1
    if n > 1:
        ans.append((n,1))
    return ans

def divisors(n):
    a = [1]
    for p,k in factor(n):
        a = [x*p**j for x in a for j in range(k+1)]
    return a

def mobius(n):
    a = factor(n)
    return 0 if any(k>1 for _,k in a) else (-1)**len(a)

def tau(n,r):
    ans = 1
    for _,k in factor(n):
        ans *= comb(k+r-1,r-1)
    return ans

# Local Euler factors, independently of the convolution implementation in
# the candidate: nu(p^k)=1+x+...+x^k; upsilon=(1-z)(1-xz).
tables = {
    3:{1:1,2:-1}, 4:{1:1,3:-1}, 5:{1:1,2:-1,3:-1,4:1},
    7:{1:1,2:1,3:-1,4:1,5:-1,6:-1},
    8:{1:1,3:-1,5:-1,7:1}, 12:{1:1,5:-1,7:-1,11:1},
    13:{i:(1 if i in {1,3,4,9,10,12} else -1) for i in range(1,13)},
}

def local_coefficients(n,table,D):
    v,u = 1,1
    for p,k in factor(n):
        x = table.get(p % D,0)
        v *= sum(x**j for j in range(k+1))
        u *= (-(1+x) if k==1 else x if k==2 else 0)
    return v,u

counts = {"unequal_cutoff_coefficients":0,"equal_cutoff_coefficients":0,
          "ramified_deletions":0,"local_divisor_inequalities":0,
          "phase_zero_identities":0,"nonzero_product_splittings":0,
          "reflection_evaluations":0,"toy_lattice_samples":0}
for D,table in tables.items():
    cap = 5000
    vu = [(0,0)]+[local_coefficients(n,table,D) for n in range(1,cap+1)]
    for n in range(1,cap+1):
        v,u = vu[n]
        assert v>=abs(u)
        assert sum(vu[d][1]*vu[n//d][0] for d in divisors(n)) == (n==1)
        if n % D == 0:
            m=n//D
            expected = mobius(D)*vu[m][1] if gcd(m,D)==1 else 0
            assert u == expected
            counts["ramified_deletions"] += 1
    for Y,X in [(2,5),(3,10),(4,17),(5,26),(6,37)]:
        assert X > Y*Y
        for n in range(1,X*Y+1):
            ds=divisors(n)
            c=sum(vu[d][1]*vu[n//d][0] for d in ds if d<=X and n//d<=Y)-(n==1)
            major=sum(vu[d][0]*vu[n//d][0] for d in ds if Y<d<=X and n//d<=X)
            assert abs(c)<=major  # stronger than candidate's factor 2
            if n<=Y:
                assert c==0
            elif n<=X:
                assert c == -sum(vu[d][1]*vu[n//d][0] for d in ds if n//d>Y)
            else:
                assert all(d>Y for d in ds if d<=X and n//d<=Y)
            counts["unequal_cutoff_coefficients"]+=1
        for n in range(1,X*X+1):
            ds=divisors(n)
            c=sum(vu[d][1]*vu[n//d][0] for d in ds if d<=X and n//d<=X)-(n==1)
            major=sum(vu[d][0]*vu[n//d][0] for d in ds if Y<d<=X and n//d<=X)
            assert abs(c)<=2*major
            counts["equal_cutoff_coefficients"]+=1

for x in [-1,0,1]:
    for k in range(25):
        v=sum(x**i for i in range(k+1))
        for j in range(1,12):
            t=comb(k+2*j-1,2*j-1)
            assert v*v*t*t<=comb(k+16*j*j-1,16*j*j-1)
            assert v*v*t<=comb(k+8*j-1,8*j-1)
            assert comb(k+2*j-1,2*j-1)**2<=comb(k+4*j*j-1,4*j*j-1)
            counts["local_divisor_inequalities"]+=1

def add(z,w): return (z[0]+w[0],z[1]+w[1])
def sub(z,w): return (z[0]-w[0],z[1]-w[1])
def mul(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def conj(z): return (z[0],-z[1])
def norm2(z): return z[0]*z[0]+z[1]*z[1]
def scale(a,z): return (a*z[0],a*z[1])
def div(z,w): return scale(1/norm2(w),mul(z,conj(w)))
Z=(F(0),F(0)); O=(F(1),F(0))
zs=[(F(a,2),F(b,3)) for a,b in [(-3,1),(2,-4),(0,0),(1,0),(0,3),(2,2)]]
units=[O,scale(-1,O),(F(0),F(1)),(F(3,5),F(4,5)),(F(-5,13),F(12,13))]
for phi in units:
    assert norm2(phi)==1
    for f in zs:
        for m in zs:
            u=div(mul(phi,m),conj(m)) if m!=Z else O
            assert norm2(u)==1
            e=scale(-1,add(f,mul(phi,conj(f))))
            assert e==mul(phi,conj(e))
            s=add(f,scale(F(1,2),e))
            b=sub(mul(m,s),O); r=sub(mul(m,f),O)
            assert add(s,mul(phi,conj(s)))==Z
            assert add(O,u)==scale(-1,add(b,mul(u,conj(b))))
            assert add(O,u)==scale(-1,add(add(r,mul(u,conj(r))),mul(e,m)))
            assert norm2(add(O,u))<=4*norm2(b)
            for sx in zs:
                rx=sub(mul(m,sx),O)
                zx=mul(phi,mul(m,conj(sx)))
                assert zx==mul(u,conj(add(O,rx)))
                assert norm2(sub(zx,u))==norm2(rx)
            counts["phase_zero_identities"]+=1
        for seed in zs:
            prod=add(seed,mul(phi,conj(seed)))
            e=sub(prod,add(f,mul(phi,conj(f))))
            assert e==mul(phi,conj(e))
            s=add(f,scale(F(1,2),e))
            assert add(s,mul(phi,conj(s)))==prod
            counts["nonzero_product_splittings"]+=1

# E^dagger(s)=conj(E(1-conj(s))) is a holomorphic polynomial, not E(conj(s)).
def evaluate(coeffs,s):
    v=Z
    for c in reversed(coeffs): v=add(c,mul(s,v))
    return v
coeffs=[zs[0],zs[3],zs[5]]
ref=[Z]*len(coeffs)
for k,c in enumerate(coeffs):
    for j in range(k+1):
        ref[j]=add(ref[j],scale(F(comb(k,j)*(-1)**j),conj(c)))
for s in zs+[(F(1,2),F(t)) for t in range(-4,5)]:
    assert evaluate(ref,s)==conj(evaluate(coeffs,sub(O,conj(s))))
    if s[0]==F(1,2): assert evaluate(ref,s)==conj(evaluate(coeffs,s))
    counts["reflection_evaluations"]+=1

# Formal roots of unity: for prime N=23 each 1<=k<=21 permutes all exponents,
# so the sum is the cyclotomic polynomial 1+z+...+z^22, exactly zero at zeta23.
N=23
for k in range(1,22): assert sorted((k*j)%N for j in range(N))==list(range(N))
for j in range(N):
    for q in range(-23,24):
        t=F(2*q+1,2)-F(j,N)
        assert (t+F(j,N))%1==F(1,2)
        assert (F(2*(q+1)+1,2)-F(j,N))-t==1
        counts["toy_lattice_samples"]+=1

base=9+36*F(2,4)+77
trial=base+81*F(2,6)
assert sum([F(1,4),F(1,4),F(1,6),F(1,6),F(1,12),F(1,12)])==1
e4=-F(2011,4)+4*2**2+4*2
e12=-F(2011,4)+4*6**2+4*6
budget={"base_loss":base,"trial_loss":trial,"e4":e4,"e12":e12,
        "base_inverse":base+2*e4,"trial_inverse":trial+2*e12,
        "base_AFE":base+8-2*179,"trial_AFE":trial+24-2*179,
        "H_cubed_length_P_exponent":F(504,1000)*3,
        "H_fourth_length_P_exponent":F(504,1000)*4,
        "unequal_cutoff_twelfth_power_length_D_exponent":24*6,
        "equal_cutoff_twelfth_power_length_D_exponent":40*6,
        "annulus_shift_height_alpha_multiple":F(1,4)+3,
        "rectangle_width_over_radius_interval":F(1,2)/F(1,8)}
assert budget["base_loss"]==104 and budget["trial_loss"]==131
assert budget["trial_AFE"]==-203 and budget["trial_inverse"]==-F(1077,2)
assert budget["H_cubed_length_P_exponent"]<2<budget["H_fourth_length_P_exponent"]
result={"status":"PASS_FINITE_ONLY","independence":"New checker using prime-local Euler coefficients and rational complex arithmetic; candidate checker was read, not executed or imported.",
        "counts":counts,"budgets":{k:str(v) for k,v in budget.items()},
        "scope":"Finite regression checks only; no verification of an analytic asymptotic, assumption (A), actual L-zero data, Lean build, Z2, or main theorem."}
(HERE/"INDEPENDENT_RESULTS.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
