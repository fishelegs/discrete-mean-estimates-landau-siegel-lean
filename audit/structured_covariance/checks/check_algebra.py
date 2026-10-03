#!/usr/bin/env python3
"""Finite algebra checks only: no asymptotic theorem and no Lean execution."""
from fractions import Fraction as F
import cmath
import math
import random

budget = F(249, 2) + F(153, 6) - F(739, 3) + F(2*77, 3)
assert budget == -45
assert 9*5**2 + 2*5*2 + 2**2 == 249
assert 9*3**2 + 2*3*6 + 6**2 == 153
assert F(504,1000)*3 == F(189,125) < 2
assert -114 + 36 + 77 == -1
print('Moment and precision budgets: -45 and -1; cubic support exponent 1.512 < 2')

def e(x):
    return cmath.exp(2j*math.pi*x)

def primitive_root(p):
    for g in range(2,p):
        if len({pow(g,j,p) for j in range(p-1)}) == p-1:
            return g
    raise ValueError(p)

def chi_value(D,n):
    n %= D
    if math.gcd(n,D)>1:
        return 0
    if D==3:
        return 1 if n==1 else -1
    if D==4:
        return 1 if n==1 else -1
    if D==5:
        return 1 if n in (1,4) else -1
    if D==8:
        return 1 if n in (1,7) else -1
    raise ValueError(D)

def close(x,y,tag):
    assert abs(x-y)<2e-10, (tag,x,y,abs(x-y))

root_tests=0
for D in (3,4,5,8):
    c = 0 if chi_value(D,-1)==1 else 1
    tau_chi = sum(chi_value(D,n)*e(F(n,D)) for n in range(D))
    eps_chi = tau_chi/(1j**c*math.sqrt(D))
    for p in (7,11,13,17,19,23):
        if math.gcd(p,D)>1:
            continue
        g=primitive_root(p)
        logs={pow(g,j,p):j for j in range(p-1)}
        def psi(k,n):
            return 0 if n%p==0 else e(F(k*logs[n%p],p-1))
        gauss={k:sum(psi(k,n)*e(F(n,p)) for n in range(1,p)) for k in range(p-1)}
        roots={}
        for k in range(1,p-1):
            a=k%2
            b=(a+c)%2
            tau_twist=sum(chi_value(D,n)*psi(k,n)*e(F(n,D*p)) for n in range(D*p))
            eps_psi=gauss[k]/(1j**a*math.sqrt(p))
            eps_twist=tau_twist/(1j**b*math.sqrt(D*p))
            roots[k]=eps_psi*eps_twist
            ca=(-1)**(c*a+a)*chi_value(D,p)*eps_chi
            close(roots[k],ca*psi(k,D)*gauss[k]**2/p,('CRT',D,p,k))
        def kl(x):
            x %= p
            return sum(e(F(u+x*pow(u,-1,p),p)) for u in range(1,p))/math.sqrt(p)
        for a in (0,1):
            ks=[k for k in range(1,p-1) if k%2==a]
            N=len(ks)
            ca=(-1)**(c*a+a)*chi_value(D,p)*eps_chi
            for v in range(1,p):
                r0=sum(psi(k,v) for k in ks)/N
                want0=(p-1)/(2*N)*((v==1)+(-1)**a*(v==p-1))-(a==0)/N
                close(r0,want0,('R0',D,p,a,v))
                rm=sum(roots[k].conjugate()*psi(k,v) for k in ks)/N
                arg=v*pow(D,-1,p)%p
                wantm=ca.conjugate()*(p-1)/(2*N*math.sqrt(p))*(kl(arg)+(-1)**a*kl(-arg))-(a==0)*ca.conjugate()/(p*N)
                close(rm,wantm,('R-1',D,p,a,v))
                rp=sum(roots[k]*psi(k,v) for k in ks)/N
                arg=pow(D*v,-1,p)
                wantp=ca*(p-1)/(2*N*math.sqrt(p))*(kl(arg)+(-1)**a*kl(-arg))-(a==0)*ca/(p*N)
                close(rp,wantp,('R1',D,p,a,v))
                gs=sum(gauss[(-k)%(p-1)]*psi(k,v) for k in ks)
                wantgs=(p-1)/2*(e(F(v,p))+(-1)**a*e(F(-v,p)))+(a==0)
                close(gs,wantgs,('Gauss conjugate',D,p,a,v))
                root_tests+=4
print(f'Passed {root_tests} root/parity/Gauss identities, including even principal corrections')

random.seed(221102515)
for _ in range(100):
    Fv=complex(random.random()+.1,random.random()+.1)
    Gv=1/Fv
    Q=-Gv*Fv.conjugate()
    Z=cmath.exp(2j*math.pi*random.random())
    A=complex(random.random(),random.random())
    B=complex(random.random(),random.random())
    J=complex(random.random(),random.random())
    W=Z*B.conjugate()
    U=Q*A
    close(U*J.conjugate(),-(Gv*A)*(Fv*J).conjugate(),'target')
    Dmix=Z.conjugate()*Gv*A*B*Fv.conjugate()
    close(U*W.conjugate(),-Dmix,'mixed')
    close(A*U.conjugate(),-((Gv*A)*(Fv*A).conjugate()).conjugate(),'G13')
    close(W*U.conjugate(),-Dmix.conjugate(),'G23')
    close(abs(U)**2,abs(A)**2,'norm')
    close(Q*Fv+Fv.conjugate(),0,'compensated null')
print('Passed 600 pointwise Gram, target, norm, and compensation checks')

try:
    import mpmath as mp
except ImportError:
    print('mpmath unavailable; exact-gamma FE quotient check skipped')
else:
    mp.mp.dps=40
    s=mp.mpc('.4','29')
    betas=[mp.mpc(0,'.011'),mp.mpc(0,'.022'),mp.mpc(0,'.033')]
    for a in (0,1):
        for c in (0,1):
            D=5 if c==0 else 3
            p=7
            b=(a+c)%2
            k=2 if a==0 else 1
            g=primitive_root(p)
            logs={pow(g,j,p):j for j in range(p-1)}
            def ps(n):
                return mp.mpc(0) if n%p==0 else mp.e**(2j*mp.pi*k*logs[n%p]/(p-1))
            taup=sum(ps(n)*mp.e**(2j*mp.pi*n/p) for n in range(p))
            tauc=sum(chi_value(D,n)*mp.e**(2j*mp.pi*n/D) for n in range(D))
            taut=chi_value(D,p)*ps(D)*tauc*taup
            def Z(z,j,q,tau):
                return mp.j**(-j)*tau*mp.pi**(z-mp.mpf('.5'))*q**(-z)*mp.gamma((1-z+j)/2)/mp.gamma((z+j)/2)
            zz=Z(s,a,p,taup)
            zt=Z(s,b,D*p,taut)
            E=1 if c==0 else (-mp.j*mp.tan(mp.pi*s/2) if a==0 else mp.j/mp.tan(mp.pi*s/2))
            rhs=tauc*chi_value(D,p)*mp.conj(ps(D))*D**(s-1)*E
            assert abs(zz/zt-rhs)<mp.mpf('1e-35')
            Eb=mp.fprod(Z(s+beta,a,p,taup)/zz for beta in betas)
            lhs=mp.fprod(Z(s+beta,a,p,taup) for beta in betas)/zz
            assert abs(lhs-zz**2*Eb)<mp.mpf('1e-35')
    print('Passed exact gamma/CRT quotient and complete three-over-one FE factor checks')
