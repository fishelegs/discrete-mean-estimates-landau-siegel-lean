"""Exact algebra and finite cyclotomic regression checks; not analytic proofs.

The general proofs and hypotheses are in REVIEW.md.  No floating-point Gauss
sum is used here.  Finite character identities are reduced in Q[x]/Phi_L(x).
"""
from fractions import Fraction as F
from math import comb, gcd, lcm
from pathlib import Path
import hashlib
import json
import sympy as sp

x, j, z, y = sp.symbols('x j z y')
results = {}
poly = (j+1)*(j+2)*(j+3)/6 - (j+1)**2
results['tau_square_difference_exact'] = str(sp.factor(poly))
assert sp.expand(poly-j*(j-1)*(j+1)/6) == 0
results['d4_convolution_d4_generating_function'] = str((1-z)**-4*(1-z)**-4)
assert sp.cancel((1-z)**-4*(1-z)**-4-(1-z)**-8) == 0
# Reflection has reduced the parity correction to these rational functions,
# with y=exp(-pi*t).  These are identities, not a numerical t sample.
E0 = (1-sp.I*y)/(1+sp.I*y)
E1 = (1+sp.I*y)/(1-sp.I*y)
for a, E in enumerate((E0, E1)):
    Ec = sp.conjugate(E).subs(sp.conjugate(y),y)
    assert sp.cancel(E*Ec-1) == 0
    assert sp.cancel((E-1)*(Ec-1)-4*y*y/(1+y*y)) == 0
results['odd_parity_abs_E_squared'] = '1'
results['odd_parity_abs_E_minus_1_squared'] = '4*y^2/(1+y^2)'
results['two_adic_d8_factors'] = {str(v):comb(v+7,7) for v in [0,2,3]}

M, N = F(499,1000), F(503,1000)
exponents = {
    'length_product': M+N,
    'mqw_bracket_third': -F(3,16)*(M+N)+F(11,64),
    'normalized_first': -F(1,2)+N/2,
    'normalized_second': -1+(M+N)/2,
    'normalized_third': -F(1,2)+(M+N)/2-F(3,16)*(M+N)+F(11,64),
    'actual_R_P_exponent': 2-M-N,
    'stationary_absolute_certificate_P_exponent': F(1,2)-F(2,125),
    'merged_R_times_larger_poly_P_exponent':2-M,
}
assert M<=N+F(1,4) and M+N<=F(5,4)
assert exponents['normalized_third']==-F(3,200)
results['exact_exponents']={k:str(v) for k,v in exponents.items()}
results['deletion_log_power'] = 12+4*9
results['prime_positive_mass_power'] = -2011+77
results['sufficient_per_prime_K_strict_upper_bound'] = 2011-77-16

class Cyc:
    def __init__(self,L):
        self.L=L
        self.phi=sp.Poly(sp.cyclotomic_poly(L,x),x,domain=sp.QQ)
    def reduce(self,terms):
        # terms maps exponent to rational coefficient before cyclotomic reduction
        d={}
        for exponent,c in terms.items():
            exponent%=self.L
            d[exponent]=d.get(exponent,0)+c
        return sp.Poly.from_dict({(k,):v for k,v in d.items() if v},x,domain=sp.QQ).rem(self.phi)
    def root(self,k): return self.reduce({k:1})
    def conj(self,p): return self.reduce({-m[0]:c for m,c in p.terms()})
    def mul(self,p,q): return (p*q).rem(self.phi)
    def zero(self): return self.reduce({})

def gen(p):
    return next(g for g in range(2,p) if len({pow(g,k,p) for k in range(p-1)})==p-1)

crt_cases=0
root_kernel_cases=0
congruence_kernel_cases=0
target_kernel_cases=0
discriminants=(-3,-4,5,8,-8,12,-20,24,-24)
for delta in discriminants:
    D=abs(delta)
    chi=lambda n:int(sp.kronecker_symbol(delta,n))
    for p in (5,7,11):
        if gcd(D,p)!=1: continue
        C=Cyc(lcm(D*p,p-1))
        g=gen(p)
        logs={pow(g,k,p):k for k in range(p-1)}
        tc=C.reduce({n*C.L//D:chi(n) for n in range(D)})
        assert C.mul(tc,tc)==C.reduce({0:chi(-1)*D})
        for k in range(1,p-1):
            def psiroot(n):return k*logs[n%p]*C.L//(p-1)
            tp=C.reduce({})
            tprod=C.reduce({})
            for n in range(1,p):tp+=C.root(psiroot(n)+n*C.L//p)
            tp=tp.rem(C.phi)
            for n in range(D*p):
                if n%p and chi(n):tprod+=chi(n)*C.root(psiroot(n)+n*C.L//(D*p))
            tprod=tprod.rem(C.phi)
            rhs=chi(p)*C.mul(C.root(psiroot(D)),C.mul(tc,tp))
            assert (tprod-rhs).is_zero
            crt_cases+=1

        # Remove the constant c_a and sqrt(p) from the displayed root identity:
        # sum_psi bar(psi(D))*bar(tau(psi))^2*psi(v)
        # = (p-1)/2*(S(v/D)+(-1)^a*S(-v/D))-delta_{a=0}.
        C=Cyc(p*(p-1))
        def psi(k,n):return C.root(k*logs[n%p]*C.L//(p-1))
        taus={k:sum((C.mul(psi(k,n),C.root(n*C.L//p)) for n in range(1,p)),C.zero()).rem(C.phi) for k in range(1,p-1)}
        def S(v):return sum((C.root((u+v*pow(u,-1,p))*C.L//p) for u in range(1,p)),C.zero()).rem(C.phi)
        for a in (0,1):
            ks=[k for k in range(1,p-1) if k%2==a]
            for v in range(1,p):
                # C_1 has no root factor after the contour cancellation.
                plain=sum((psi(k,v) for k in ks),C.zero()).rem(C.phi)
                orth=sp.Rational(p-1,2)*(int(v%p==1)+(-1)**a*int(v%p==p-1))-int(a==0)
                assert (plain-C.reduce({0:orth})).is_zero
                congruence_kernel_cases+=1
                vd=v*pow(D,-1,p)%p
                lhs=sum((C.mul(psi(k,vd),C.mul(C.conj(taus[k]),C.conj(taus[k]))) for k in ks),C.zero()).rem(C.phi)
                rhs=(sp.Rational(p-1,2)*(S(vd)+(-1)**a*S(-vd))-C.reduce({0:int(a==0)})).rem(C.phi)
                assert (lhs-rhs).is_zero
                root_kernel_cases+=1
                # T_1's single Gauss sum, with constants removed.
                Dv=D*v%p
                lhs=sum((C.mul(psi(k,Dv),taus[k]) for k in ks),C.zero()).rem(C.phi)
                inv=pow(Dv,-1,p)
                rhs=(sp.Rational(p-1,2)*(C.root(inv*C.L//p)+(-1)**a*C.root(-inv*C.L//p))+C.reduce({0:int(a==0)})).rem(C.phi)
                assert (lhs-rhs).is_zero
                target_kernel_cases+=1
results['finite_exact_cyclotomic_checks']={
    'signed_fundamental_discriminants':list(discriminants),'primes':[5,7,11],
    'crt_nonprincipal_character_cases':crt_cases,
    'inverse_root_parity_kernel_cases':root_kernel_cases,
    'C1_congruence_kernel_cases':congruence_kernel_cases,
    'T1_single_gauss_kernel_cases':target_kernel_cases,
    'all_remainders_zero':True,
    'scope':'Finite regression checks, not proofs of universal identities or analytic mean estimates.'}
bundle_root=Path(__file__).resolve().parent.parent
input_dir=bundle_root/'phase-mechanism-repair'
results['input_sha256']={p.relative_to(bundle_root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(input_dir.iterdir()) if p.is_file() and p.suffix in {'.md','.py','.json'}}
out=Path(__file__).with_name('exact-checks.json')
out.write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
