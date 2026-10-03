#!/usr/bin/env python3
"""Independent finite checks. This script writes only its stdout."""
from fractions import Fraction as F
from pathlib import Path
import cmath
import hashlib
import json
import math
import subprocess
import sys
import mpmath as mp
import sympy as sp

# Universal algebra, not a sample of values.
f,g,fd,gd,z,e = sp.symbols('f g fd gd z e')
delta, deltad = f*g-1, fd*gd-1
normalized = (f+z*fd+e)/f
remainder = (z*g*(delta-deltad)-e*g*gd)/(1+delta)
assert sp.cancel(z*g-gd-gd*(normalized-2)-remainder) == 0

# Universal FE pairing with a symbolic branch relation B^-2=Hp/H^3.
b,zp,zc,r,q,a,j = sp.symbols('b zp zc r q a j', nonzero=True)
Q = zc*zp**3/b**2*q
assert sp.cancel((-sp.I*r*b/zp*g*Q - (-sp.I*r/b*zp*gd*q))
                 -(-sp.I*r/b*zp*q*(zp*zc*g-gd))) == 0
assert sp.cancel((-sp.I*r*b/(zp*zc)*g*Q - (-sp.I*r/b*zp/zc*gd*q))
                 -(-sp.I*r/b*zp/zc*q*(zp*zc*g-gd))) == 0

holder = [F(1,4),F(1,4),F(1,6),F(1,6),F(1,6)]
assert sum(holder) == 1
w1 = 9+sum(F(36,4) for _ in range(4))
w2 = 9+sum(x*y for x,y in zip(holder,[36,36,36,81,81]))
budgets = {
 'delta_normalized': -227+w1+77,
 'afe_normalized': -179+w2+77,
 'bad_family_normalized': F(36,2)+2*F(81,6)-F(739,6)+F(5*77,6),
 'delta_kappa_normalized': F(-640,2)+2*F(36,4)+77,
 'G_sixth_log_power': F(36),
 'A_B_J_sixth_log_power': F(81),
 'matrix_precision_for_L_minus_8_norm_and_gain': F(-16),
}
assert list(budgets.values())[:4] == [-105,-42,-14,-225]
gaps = [F(9995,10000)+F(502,1000)+F(499,1000)-2,
        F(1005,1000)-F(504,1000)-F(500,1000),
        F(1005,1000)+F(502,1000)-1-F(504,1000),
        F(1005,1000)+F(500,1000)-F(504,1000)-1]
assert gaps == [F(1,2000),F(1,1000),F(3,1000),F(1,1000)]

# Fourier identities over Q[zeta_p], with integer residue-count vectors.
# At a prime p, an integer polynomial of degree<p vanishes at zeta_p
# precisely when all its coefficients are equal.
fourier_cases = 0
for p in [5,7,11,13]:
    inv = {n:pow(n,-1,p) for n in range(1,p)}
    for aa in range(1,p):
        for hh in range(p):
            plus = [0]*p
            minus = [0]*p
            for u in range(1,p):
                plus[(aa*inv[u]+hh*u)%p] += 1
                for x in range(1,p):
                    for y in range(1,p):
                        minus[(x+y+aa*u*inv[x]*inv[y]+hh*u)%p] += 1
            if hh:
                for u in range(1,p):
                    plus[(u+aa*hh*inv[u])%p] -= 1
                    minus[(u-aa*inv[hh]*inv[u])%p] -= p
                minus[0] += 1
            else:
                plus[0] += 1
                minus[0] += 1
            assert len(set(plus)) == 1
            assert len(set(minus)) == 1
            fourier_cases += 2

def char(D,n):
    base={3:{1:1,2:-1},4:{1:1,3:-1},5:{1:1,2:-1,3:-1,4:1},
          8:{1:1,3:-1,5:-1,7:1},12:{1:1,5:-1,7:-1,11:1}}
    if D==24:
        return char(3,n)*char(8,n)
    return base[D].get(n%D,0)
def root(q,k):
    return cmath.exp(2j*math.pi*(k%q)/q)

# CRT formula tested on every coordinate basis F=1_{u=b}, stronger than
# only testing the two trace functions; this includes h divisible by p or D.
crt_cases=0
crt_max=0.0
for D in [3,4,5,8,12,24]:
    for p in [5,7,11,13]:
        if math.gcd(D,p)!=1:
            continue
        tau=sum(char(D,u)*root(D,u) for u in range(D))
        for h in range(D*p):
            c=tau*char(D,p)*char(D,h)
            for v in range(p):
                lhs=sum(char(D,u)*root(D*p,h*u) for u in range(v,D*p,p))
                rhs=c*root(p,h*pow(D,-1,p)*v)
                crt_max=max(crt_max,abs(lhs-rhs))
                crt_cases+=1
assert crt_max<1e-10

# Actual degree-one functional equations, with nonreal primitive psi,
# both parities, real chi and conductor Dp, and the prescribed dual shifts.
mp.mp.dps=38
mpmax=mp.mpf(0)
mpcases=0
for D,p,generator,k in [(3,5,2,1),(4,5,2,2),(8,7,3,1),(3,7,3,2)]:
    psi=[mp.mpc(0)]*p
    for n in range(p-1):
        psi[pow(generator,n,p)]=mp.exp(2j*mp.pi*k*n/(p-1))
    twist=[char(D,n)*psi[n%p] for n in range(D*p)]
    def Z(v,table):
        q=len(table)
        parity=0 if abs(table[-1]-1)<mp.mpf('1e-30') else 1
        tau=sum(table[n]*mp.exp(2j*mp.pi*n/q) for n in range(q))
        eps=tau/(mp.j**parity*mp.sqrt(q))
        return eps*(q/mp.pi)**(mp.mpf('.5')-v)*mp.gamma((1-v+parity)/2)/mp.gamma((v+parity)/2)
    for sigma in ['.5','.507']:
        s=mp.mpc(sigma,mp.mpf('9.25'))
        beta=[mp.mpc(0,'.003'),mp.mpc(0,'.005'),mp.mpc(0,'.008')]
        Q=mp.dirichlet(s,twist)*mp.fprod(mp.dirichlet(s+bb,psi) for bb in beta)
        Qd=mp.dirichlet(1-s,[mp.conj(t) for t in twist])*mp.fprod(
            mp.dirichlet(1-s-bb,[mp.conj(t) for t in psi]) for bb in beta)
        Gamma=Z(s,twist)*mp.fprod(Z(s+bb,psi) for bb in beta)
        err=abs(Q-Gamma*Qd)/max(1,abs(Q))
        mpmax=max(mpmax,err)
        assert err<mp.mpf('1e-28')
        mpcases+=1

root=Path(__file__).resolve().parent
report=root/'DERIVATION.md'
replayed=json.loads(subprocess.check_output([sys.executable,'-B',str(root/'check_budgets_and_transforms.py')],text=True))
expected=json.loads((root/'CANDIDATE_CHECKS.json').read_text())
for key in ['status','budgets','exact_gaussian_rational_defect_cases','fourier_cases','CRT_completion_cases','conductors','primes']:
    assert replayed[key]==expected[key]
assert replayed['max_fourier_error']<1e-10 and replayed['max_CRT_completion_error']<1e-10
print(json.dumps({
 'status':'PASS',
 'candidate_sha256':hashlib.sha256(report.read_bytes()).hexdigest(),
 'candidate_replay_exact_algebra_and_counts':True,
 'candidate_floating_checks_within_declared_tolerance':True,
 'symbolic_universal_defect_identity':True,
 'symbolic_T_and_C_pairing':True,
 'exact_rational_budgets':{k:str(v) for k,v in budgets.items()},
 'exact_support_gaps':[str(x) for x in gaps],
 'exact_integer_cyclotomic_Fourier_cases':fourier_cases,
 'CRT_coordinate_basis_cases':crt_cases,
 'CRT_max_error':crt_max,
 'actual_dirichlet_FE_cases':mpcases,
 'actual_dirichlet_FE_max_relative_error':str(mpmax),
 'limitations':'Finite and algebraic checks only; no large-D mean, Gram lower bound, Lean build, or final theorem validation.'
},indent=2,sort_keys=True))
