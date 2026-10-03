#!/usr/bin/env python3
"""Independent finite/symbolic checks; not an analytic or Lean proof."""
from fractions import Fraction as Q
from math import comb, gcd, isqrt, pi, sqrt
import cmath
import mpmath as mp
import sympy as sp

mp.mp.dps = 60

def check_close(a, b, label, tol=2e-10):
    assert abs(a-b) < tol, (label, a, b, abs(a-b))

budgets = {}
for sx, sy in [(0,0), (1,0), (0,1), (1,1)]:
    second = 9*25 + sx*(2*5*2+2**2)
    sixth = 9*9 + sy*(2*3*6+6**2)
    exponent = Q(second,2)+Q(sixth,6)-Q(739,3)+Q(154,3)
    budgets[(sx,sy)] = exponent
assert budgets == {(0,0): -69, (1,0): -57, (0,1): -57, (1,1): -45}
assert Q(504,1000)*3 == Q(189,125) < 2
assert -114+36+77 == -1
assert Q(144,2)+Q(81,6)+Q(81,6)-Q(739,6)+Q(5*77,6) == 40
print('Exact budgets:', budgets, '; naive left C1 2/6/6/6 budget = +40')

def divisors(n):
    return [d for d in range(1,n+1) if n%d == 0]

def factors(n):
    result = {}
    p = 2
    while p*p <= n:
        while n%p == 0:
            result[p] = result.get(p,0)+1
            n //= p
        p += 1
    if n>1:
        result[n] = result.get(n,0)+1
    return result

def dk(k,n):
    out=1
    for exponent in factors(n).values():
        out *= comb(exponent+k-1,k-1)
    return out

for k,r,Y in [(5,2,11),(3,6,13),(2,1,7)]:
    for n in range(1,501):
        finite = sum(dk(k,n//d)*dk(r,d) for d in divisors(n) if d<=Y)
        smooth = sum(dk(k,n//d)*dk(r,d) for d in divisors(n)
                     if all(p<=Y for p in factors(d)))
        local = 1
        for p,j in factors(n).items():
            local *= comb(j+(k+r if p<=Y else k)-1,(k+r if p<=Y else k)-1)
        assert finite<=smooth==local
print('1500 finite checks of short-divisor multiplicative majorization passed')

def e(x):
    return cmath.exp(2j*pi*float(x))

def generator(p):
    return next(g for g in range(2,p) if len({pow(g,j,p) for j in range(p-1)})==p-1)

root_checks = 0
for disc in [-8,12,13]:
    D=abs(disc)
    chi=lambda n: complex(sp.kronecker_symbol(disc,n))
    c=0 if chi(-1)==1 else 1
    tc=sum(chi(n)*e(Q(n,D)) for n in range(D))
    ec=tc/(1j**c*sqrt(D))
    for p in [11,17,29]:
        if gcd(D,p)!=1:
            continue
        g=generator(p)
        logs={pow(g,j,p):j for j in range(p-1)}
        def psi(k,n):
            return 0 if n%p==0 else e(Q(k*logs[n%p],p-1))
        tau={k:sum(psi(k,n)*e(Q(n,p)) for n in range(1,p)) for k in range(p-1)}
        roots={}
        for k in range(1,p-1):
            a=k%2; b=(a+c)%2
            tt=sum(chi(n)*psi(k,n)*e(Q(n,D*p)) for n in range(D*p))
            et=tt/(1j**b*sqrt(D*p))
            roots[k]=tau[k]*et/(1j**a*sqrt(p))
            check_close(tt,chi(p)*psi(k,D)*tc*tau[k],('CRT',disc,p,k))
        def kl(x):
            return sum(e(Q(u+x*pow(u,-1,p),p)) for u in range(1,p))/sqrt(p)
        for a in [0,1]:
            ks=[k for k in range(1,p-1) if k%2==a]
            Na=len(ks)
            ca=(-1)**(c*a+a)*chi(p)*ec
            da=(-1)**(c*a)*chi(p)*ec
            for v in range(1,p):
                direct={j:sum(roots[k]**j*psi(k,v) for k in ks)/Na for j in [-1,0,1]}
                rhs0=(p-1)/(2*Na)*((v==1)+(-1)**a*(v==p-1))-(a==0)/Na
                x=v*pow(D,-1,p)%p
                rhsm=ca.conjugate()*(p-1)/(2*Na*sqrt(p))*(kl(x)+(-1)**a*kl(-x))-(a==0)*ca.conjugate()/(p*Na)
                x=pow(D*v,-1,p)
                rhsp=ca*(p-1)/(2*Na*sqrt(p))*(kl(x)+(-1)**a*kl(-x))-(a==0)*ca/(p*Na)
                for j,rhs in [(-1,rhsm),(0,rhs0),(1,rhsp)]:
                    check_close(direct[j],rhs,('root',disc,p,a,v,j)); root_checks+=1
                direct_gauss=sum(tau[(-k)%(p-1)]*psi(k,v) for k in ks)
                gauss=(p-1)/2*(e(Q(v,p))+(-1)**a*e(Q(-v,p)))+(a==0)
                check_close(direct_gauss,gauss,('single conjugate Gauss',disc,p,a,v)); root_checks+=1
                direct_t=sum(roots[k]/(tau[k]/(1j**a*sqrt(p)))*psi(k,v) for k in ks)/Na
                gauss_t=da*(1j**(-a))/(Na*sqrt(p))*((p-1)/2*(e(Q(x,p))+(-1)**a*e(Q(-x,p)))+(a==0))
                check_close(direct_t,gauss_t,('T1 single Gauss',disc,p,a,v)); root_checks+=1
print(root_checks,'independent root/Gauss identities passed, including discriminants -8,12,13')

A,B,F,G,J,Z=sp.symbols('A B F G J Z', complex=True)
conj=sp.conjugate
U=-G*conj(F)*A
W=Z*conj(B)
H=lambda x,y: x*conj(y)
C0=lambda x,y: x*y/Z
Dmix=G*A*B*conj(F)/Z
checks=[H(A,W)-C0(A,B), H(A,U)+conj(H(G*A,F*A)),
        H(W,U)+conj(Dmix), H(W,J)-conj(C0(J,B)), H(U,J)+H(G*A,F*J)]
for expression in checks:
    assert sp.simplify(sp.expand(expression).subs(conj(Z),1/Z)) == 0
assert sp.simplify((U*F/A+conj(F)).subs(G,1/F)) == 0
print('Symbolic full-Q Gram/target conjugations and exact-null model passed')

def logh(z,a,q):
    return (mp.mpf('.5')-z)*mp.log(q/mp.pi)+mp.loggamma((1-z+a)/2)-mp.loggamma((z+a)/2)

q=mp.exp(1000); alpha=mp.pi/1000; s=mp.mpc('.6',100)
betas=[1j*alpha,2j*alpha,3j*alpha]
for a in [0,1]:
    inc=sum(logh(s+b,a,q)-logh(s,a,q) for b in betas)
    Eb=mp.exp(inc); Bb=mp.exp(-inc/2)
    assert abs(Bb**2*Eb-1)<mp.mpf('1e-50')
    assert abs(1/mp.sqrt(Eb)/Bb+1)<mp.mpf('1e-50')
print('Branch regression: naive principal E^(-1/2) has the wrong sign in both parities')

for a in [0,1]:
    for disc in [-8,12,13]:
        D=abs(disc); c=0 if sp.kronecker_symbol(disc,-1)==1 else 1
        b=(a+c)%2
        # After CRT, the quotient identity reduces to this gamma identity.
        z=mp.mpc('.4',17)
        Echi=1 if c==0 else (-1j*mp.tan(mp.pi*z/2) if a==0 else 1j/mp.tan(mp.pi*z/2))
        hratio=mp.exp(logh(z,a,mp.mpf(11))-logh(z,b,mp.mpf(11*D)))
        want=(-1)**c*(1j**(a-b))*(mp.mpf(D)**(z-mp.mpf('.5')))*Echi
        assert abs(hratio-want)<mp.mpf('1e-45')
print('Exact gamma quotient after CRT passed for both parities and non-squarefree conductors')

L2=mp.mpf('1.7'); tcentre=mp.mpf('3.2'); s0=mp.mpc('.5',tcentre)
for sig in [mp.mpf('-.5'),mp.mpf('1.5')]:
    for x in [mp.mpf('.8'),mp.mpf(1),mp.mpf('1.3')]:
        integrand=lambda t: mp.sqrt(mp.pi)/L2*mp.exp((mp.mpc(sig,t)-s0)**2/(4*L2**2))*x**(-mp.mpc(sig,t))/(2*mp.pi)
        result=mp.quad(integrand,[-mp.inf,tcentre,mp.inf])
        target=x**(-s0)*mp.exp(-L2**2*mp.log(x)**2)
        assert abs(result-target)<mp.mpf('1e-45')
print('Six numerical Gaussian Mellin normalization checks passed; no missing 2pi factor')
print('ALL CHECKS PASSED. Finite checks do not establish uniform analytic estimates.')
