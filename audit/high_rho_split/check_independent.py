#!/usr/bin/env python3
"""Independent finite checks. No candidate code imports; no Lean/build calls."""
from fractions import Fraction as F
from math import comb, gcd, isqrt, prod
from itertools import permutations
import json
import mpmath as mp
import sympy as sp

EXPECTED = '406fc6bb49533adbbce81142924a2ad4d11517c532a5361094a4074c7f5b409b'

N = 1536
divs = [[] for _ in range(N+1)]
for d in range(1,N+1):
    for n in range(d,N+1,d):
        divs[n].append(d)
factorizations = [{}] + [sp.factorint(n) for n in range(1,N+1)]
mu = [0] + [int(sp.mobius(n)) for n in range(1,N+1)]
delta = [0,1] + [0]*(N-1)
def convolution(a,b):
    return [0]+[sum(a[d]*b[n//d] for d in divs[n]) for n in range(1,N+1)]
def tau(r,n):
    return prod(comb(int(e)+r-1,r-1) for e in factorizations[n].values())
def mult_from_local(local):
    return [0]+[prod(local(int(p),int(e)) for p,e in factorizations[n].items())
                for n in range(1,N+1)]
Q = [0]*(N+1)
Qi = [0]*(N+1)
for t in range(1,isqrt(N)+1):
    Q[t*t]=1
    Qi[t*t]=mu[t]
assert convolution(Q,Qi)==delta

arithmetic_checks=0
negative=ramified=boundary_differences=0
discriminants=(-3,-4,5,8,12,13,17,24)
cutoffs=(1,2,5,17,64)
for disc in discriminants:
    D=abs(disc)
    chi=[0]+[int(sp.kronecker_symbol(disc,n)) for n in range(1,N+1)]
    nu=[0]+[sum(chi[d] for d in divs[n]) for n in range(1,N+1)]
    ups=convolution(mu,[mu[n]*chi[n] for n in range(N+1)])
    def clocal(p,e):
        return 2 if chi[p]==1 else int(chi[p]==0 and e==1)
    def cilocal(p,e):
        return 2*(-1)**e if chi[p]==1 else ((-1)**e if chi[p]==0 else 0)
    c=mult_from_local(clocal)
    ci=mult_from_local(cilocal)
    assert convolution(Q,c)==nu
    assert convolution(Qi,ci)==ups
    assert convolution(c,ci)==delta
    assert convolution(ups,nu)==delta
    radD=prod(int(p) for p in sp.factorint(D))
    alpha=[n*n for n in range(N+1)]
    eta=convolution(mu,alpha)
    chi_alpha=convolution(chi,alpha)
    for X in cutoffs:
        tail=[nu[n] if n>X else 0 for n in range(N+1)]
        head=[nu[n] if 1<=n<=X else 0 for n in range(N+1)]
        rho=convolution(ups,tail)
        rho_complement=convolution(ups,head)
        # Four-variable square/rare factorization, retaining u^2 z > X.
        square_rare_tail=[0]+[sum(c[n//(u*u)] for u in range(1,isqrt(n)+1)
                               if n%(u*u)==0) if n>X else 0
                             for n in range(1,N+1)]
        assert square_rare_tail==tail
        assert convolution(convolution(Qi,ci),square_rare_tail)==rho
        assert convolution(eta,tail)==convolution(chi_alpha,rho)
        weak=convolution(ups,[nu[n] if n>=X else 0 for n in range(N+1)])
        boundary_differences+=sum(x!=y for x,y in zip(rho,weak))
        for n in range(1,N+1):
            arithmetic_checks+=1
            assert rho[n]==delta[n]-rho_complement[n]
            assert abs(rho[n])<=nu[n]*tau(2,n)
            assert n>X or rho[n]==0
            negative+=rho[n]<0
            rare=ram=1
            inert=1
            odd=False
            for ell,j in factorizations[n].items():
                ell,j=int(ell),int(j)
                if chi[ell]==-1:
                    inert*=ell**j
                    odd |= (j%2==1)
                else:
                    rare*=ell**j
                if chi[ell]==0:
                    ram*=ell**j
            if odd:
                assert rho[n]==0
                continue
            t=isqrt(inert)
            assert t*t*rare==n
            literal=sum(mu[r]*ups[d]*nu[rare//d]
                        for r in divs[t] for d in divs[rare]
                        if (t//r)**2*(rare//d)>X)
            assert literal==rho[n]
            B=nu[rare]*tau(2,rare)
            assert abs(rho[n])<=B*tau(3,t)
            if rho[n]:
                assert ram<=X*radD
                ramified+=ram>1
assert negative>0 and ramified>0 and boundary_differences>0

j=sp.symbols('j', nonnegative=True)
ratios={
    'tau2_squared_le_tau4': sp.expand((j+4)*(j+1)**2-(j+1)*(j+2)**2),
    'tau3_at_square_le_tau6': sp.expand((j+6)*(2*j+1)*(j+1)-(j+1)*(2*j+3)*(j+2)),
}
for poly in ratios.values():
    assert all(x>=0 for x in sp.Poly(poly,j).all_coeffs())
for e in range(1001):
    assert 2*e+1<=comb(e+2,2)
    assert (2*e+1)**2*comb(2*e+2,2)<=comb(e+53,53)
    assert (e+1)**4*comb(e+2,2)<=comb(e+47,47)

# Exact common-scale ordering: U is product of the three smallest.
geometry=0
for scales in permutations((1,2,3,5,8)):
    U=prod(sorted(scales)[:3])
    assert U**5<=prod(scales)**3
    r,s,w,m,z=scales
    assert min(r,s,w)**3<=r*s*w
    assert min(m,z)**3<=z*m*m
    geometry+=1

mp.mp.dps=45
gauss_error=mp.mpf(0)
moment_checks=0
for p in (3,5,7,11,13,17,19):
    g=int(sp.primitive_root(p))
    logs={pow(g,j,p):j for j in range(p-1)}
    def character(j,n):
        return mp.mpc(0) if n%p==0 else mp.exp(2j*mp.pi*j*logs[n%p]/(p-1))
    images={}
    for j0 in range(1,p-1):
        images.setdefault(2*j0%(p-1),[]).append(j0)
        gauss=sum(character(j0,n)*mp.exp(2j*mp.pi*n/p) for n in range(p))
        gauss_error=max(gauss_error,abs(abs(gauss)/mp.sqrt(p)-1))
    assert images[0]==[(p-1)//2]
    assert max(map(len,images.values()))<=2
    coeff=lambda n: mp.mpc((n%5)-2,(n%3)-1)/n
    vals=[sum(coeff(n)*character(j0,n) for n in range(4,30)) for j0 in range(p-1)]
    lhs=sum(abs(vals[2*j0%(p-1)])**4 for j0 in range(1,p-1))
    rhs=2*sum(abs(v)**4 for v in vals[1:])+abs(vals[0])**4
    assert lhs<=rhs+mp.mpf('1e-35')
    moment_checks+=1
    for disc in (-3,-4,5,8):
        D=abs(disc)
        if gcd(D,p)>1:
            continue
        for j0 in (1,(p-1)//2):
            q=D*p
            gauss=sum(int(sp.kronecker_symbol(disc,n))*mp.conj(character(j0,n))*
                      mp.exp(2j*mp.pi*n/q) for n in range(q))
            gauss_error=max(gauss_error,abs(abs(gauss)/mp.sqrt(q)-1))
assert gauss_error<mp.mpf('1e-35')

# Independent numerical checks of both exact normalized substitutions.
def amp(v):
    return mp.exp(-1/((v-mp.mpf('.5'))*(2-v))) if mp.mpf('.5')<v<2 else mp.mpf(0)
fourier_error=mp.mpf(0)
fourier_checks=0
for q in (7,35):
    for tau0 in ('-6','-.4','0','.4','6'):
        tau=mp.mpf(tau0); Y=mp.mpf('2.3'); h=3
        for sigma in (-1,1):
            left=mp.quad(lambda x:x**(-mp.mpf('.5')+1j*tau)*amp(x/Y)*
                         mp.exp(-2j*mp.pi*sigma*h*x/q),[Y/2,Y,2*Y])/mp.sqrt(q)
            if abs(tau)>=1:
                b=abs(tau); eta=mp.sign(tau); y=2*mp.pi*h*Y/(q*b)
                V=mp.sqrt(b/(2*mp.pi))*mp.quad(
                    lambda z:z**(-mp.mpf('.5'))*amp(z/y)*
                    mp.exp(1j*b*(eta*mp.log(z)-sigma*z+eta)),[y/2,y,2*y])
                right=h**(-mp.mpf('.5'))*(q*b/(2*mp.pi*mp.e*h))**(1j*tau)*V
            else:
                y=h*Y/q
                W=mp.quad(lambda z:z**(-mp.mpf('.5')+1j*tau)*amp(z/y)*
                          mp.exp(-2j*mp.pi*sigma*z),[y/2,y,2*y])
                right=h**(-mp.mpf('.5'))*(mp.mpf(q)/h)**(1j*tau)*W
            fourier_error=max(fourier_error,abs(left-right))
            fourier_checks+=1
assert fourier_error<mp.mpf('1e-35')

def high(k):
    return -F(49,200)+max(F(0),-F(112,125)+F(2,5)*k)/2+max(F(0),F(1103,1000)-F(3,5)*k)/2
hp=[F(21,20),F(1103,600),F(56,25),F(301,100)]
hv=[high(k) for k in hp]
assert max(hv)==-F(17,2000)
def low(k):
    return F(1,400)-k/4+max(F(0),-F(663,1000)+F(2,3)*k)
lp=[F(99,100),F(1989,2000),F(21,20)]
lv=[low(k) for k in lp]
assert max(lv)==-F(223,1000)
assert F(201,400)-F(251,500)==F(1,2000)
assert F(3,5)*(3+F(201,400))==F(4203,2000)
assert F(4203,2000)+F(1,1000)<F(2103,1000)
assert F(4203,2000)-1+F(1,1000)+F(2,8000)+F(2,10000)<F(1104,1000)
assert (3+2*F(201,400))/3==F(267,200)
assert F(267,200)+F(1,1000)+F(3,8000)+F(3,10000)<F(1337,1000)
assert 30+(1-400001)*F(1,8000)==-20
assert 30-500000*F(1,10000)==-20
assert F(225,2)+F(324,4)+F(324,4)+77+72+36==F(919,2)<500
assert F(324+972,2)+77+72==797<1000
assert F(17,2000)-F(1,200)==F(7,2000)>0

out={
    'result':'PASS',
    'scope':'Independent finite arithmetic, normalized transform samples, and exact budgets; written review supplies analytic proof. No Lean/compiler execution.',
    'candidate_sha256':EXPECTED,
    'discriminants':list(discriminants),'integers_per_case':N,'strict_cutoffs':list(cutoffs),
    'integer_cutoff_checks':arithmetic_checks,'negative_rho_examples':negative,
    'nonzero_ramified_examples':ramified,'strict_vs_weak_boundary_differences':boundary_differences,
    'universal_ratio_polynomials':{k:str(v) for k,v in ratios.items()},
    'local_envelopes_checked_through':1000,'scale_orderings_checked':geometry,
    'squaring_family_moment_checks':moment_checks,
    'normalized_gauss_max_error':str(gauss_error),
    'normalized_fourier_checks':fourier_checks,'normalized_fourier_max_error':str(fourier_error),
    'high_points':list(map(str,hp)),'high_values':list(map(str,hv)),
    'low_points':list(map(str,lp)),'low_values':list(map(str,lv)),
    'high_log_cost':'919/2 < 500','low_log_cost':'797 < 1000',
    'final_power_slack':'7/2000','fourier_tail_power':'-20','mellin_tail_power':'-20',
}
print(json.dumps(out,indent=2))
