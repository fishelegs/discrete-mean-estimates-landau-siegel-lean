#!/usr/bin/env python3
"""Finite algebra/normalization regressions, not uniform analytic or Lean proofs."""
from fractions import Fraction as F
from math import comb, gcd, pi, sqrt
import cmath
import mpmath as mp
import sympy as sp

mp.mp.dps = 50

right_budget = F(144,4)+F(81,6)+F(81,6)-F(739*5,12)+F(77*7,12)
left_budget = F(36,2)+F(81,6)+F(81,6)-F(739,6)+F(77*5,6)
assert right_budget == -200 and left_budget == -14
assert F(999,1000)*2 < 2
assert F(504,1000)*3 < 2
assert F(1005,1000) < 2
gaps = {
    'C1 right': 2-F(999,1000)-F(503,1000)-F(499,1000),
    'C1 left': F(1003,1000)-F(503,1000)-F(499,1000),
    'T1 right': 1+F(504,1000)-F(1005,1000)-F(503,1000),
    'T1 left': F(1005,1000)+F(500,1000)-F(503,1000)-1,
}
assert gaps == {'C1 right': F(-1,1000),'C1 left':F(1,1000),
                'T1 right':F(-1,250),'T1 left':F(1,500)}
print('Exact Holder budgets:', right_budget, left_budget)
print('Exact power gaps, before D/t0 factors:', gaps)

x,y=sp.symbols('x y', nonzero=True)
k=x+y+x*y-1
ks=1/x+1/y+1/(x*y)-1
assert sp.expand(k*ks-(4-(x-1/x)*(y-1/y)))==0
assert abs(abs(1j+1j+1j*1j-1)**2-8)<1e-12
print('Exact Laurent identity |kappa(q)|^2=4+4 sin(theta1)sin(theta2) passed; bound 8 is sharp')

def primepower_values(x,y,count):
    h=[]
    for k in range(count+1):
        h.append(sum(x**a*y**b*(x*y)**(k-a-b)
                     for a in range(k+1) for b in range(k-a+1)))
    return [h[k]-(h[k-1] if k else 0) for k in range(count+1)]

for t in range(1,40):
    x=cmath.exp(1j*t/13);y=cmath.exp(2j*t/13)
    vals=primepower_values(x,y,14)
    for k in range(1,15):
        assert abs(vals[k]) <= (k+1)**2+1e-10
        eta=sum(abs(vals[r])*abs(vals[k-r]) for r in range(k+1))
        assert eta <= comb(k+7,7)+1e-10
print('546 prime-power and positive convolution majorant checks passed')

def factors(n):
    out={};q=2
    while q*q<=n:
        while n%q==0:
            out[q]=out.get(q,0)+1;n//=q
        q+=1
    if n>1:out[n]=1
    return out

def kappa(n):
    out=1+0j
    for q,k in factors(n).items():
        x=cmath.exp(-.017j*float(mp.log(q)));y=cmath.exp(-.034j*float(mp.log(q)))
        out*=primepower_values(x,y,k)[k]
    return out

K={n:kappa(n) for n in range(1,1601)}
for n in range(1,1601):
    divisors=[d for d in range(1,int(sqrt(n))+1) if n%d==0]
    divisors=list(set(divisors+[n//d for d in divisors]))
    finite=sum(K[d]*K[n//d] for d in divisors if d<=40 and n//d<=40)
    positive=sum(abs(K[d])*abs(K[n//d]) for d in divisors)
    assert abs(finite)<=positive+1e-9
print('1600 truncated-square coefficient checks against |kappa|*|kappa| passed')

def e(x):return cmath.exp(2j*pi*float(x))
def generator(p):
    return next(g for g in range(2,p) if len({pow(g,j,p) for j in range(p-1)})==p-1)
def close(x,y,label,tol=2e-9):
    assert abs(x-y)<tol,(label,x,y,abs(x-y))

counts={'CRT':0,'C1 right':0,'C1 left':0,'T1 right':0,'T1 left':0}
for p in [7,11,17,29]:
    g=generator(p);logs={pow(g,j,p):j for j in range(p-1)}
    def psi(k,n):return 0 if n%p==0 else e(F(k*logs[n%p],p-1))
    tau={k:sum(psi(k,n)*e(F(n,p)) for n in range(1,p)) for k in range(p-1)}
    kl2={w:sum(e(F(u+w*pow(u,-1,p),p)) for u in range(1,p))/sqrt(p)
         for w in range(1,p)}
    kl3={w:sum(e(F(u+v+w*pow(u*v,-1,p),p))
                for u in range(1,p) for v in range(1,p))/p for w in range(1,p)}
    for disc in [-8,12,13]:
        D=abs(disc)
        if gcd(D,p)>1:continue
        chi=lambda n:complex(sp.kronecker_symbol(disc,n))
        c=0 if chi(-1)==1 else 1
        tchi=sum(chi(n)*e(F(n,D)) for n in range(D))
        echi=tchi/(1j**c*sqrt(D))
        ep={};ecp={};roots={}
        for k in range(1,p-1):
            a=k%2;b=(a+c)%2
            tcp=sum(chi(n)*psi(k,n)*e(F(n,D*p)) for n in range(D*p))
            close(tcp,tchi*tau[k]*chi(p)*psi(k,D),('CRT',disc,p,k))
            counts['CRT']+=1
            ep[k]=tau[k]/(1j**a*sqrt(p));ecp[k]=tcp/(1j**b*sqrt(D*p))
            roots[k]=ep[k]*ecp[k]
        for a in [0,1]:
            ks=[k for k in range(1,p-1) if k%2==a]
            ca=(-1)**(c*a+a)*chi(p)*echi
            da=(-1)**(c*a)*chi(p)*echi
            for v in range(1,p):
                w=pow(D*v,-1,p);wm=(-w)%p
                direct=sum(psi(k,v) for k in ks)
                rhs=(p-1)/2*((v==1)+(-1)**a*(v==p-1))-(a==0)
                close(direct,rhs,('C1 right',disc,p,a,v));counts['C1 right']+=1
                direct=sum(roots[k]*psi(k,v) for k in ks)
                rhs=ca*(p-1)/(2*sqrt(p))*(kl2[w]+(-1)**a*kl2[wm])-(a==0)*ca/p
                close(direct,rhs,('C1 left',disc,p,a,v));counts['C1 left']+=1
                direct=sum(ecp[k]*psi(k,v) for k in ks)
                rhs=da*1j**(-a)/sqrt(p)*((p-1)/2*(e(F(w,p))+(-1)**a*e(F(-w,p)))+(a==0))
                close(direct,rhs,('T1 right',disc,p,a,v));counts['T1 right']+=1
                direct=sum(roots[k]*ep[k]*psi(k,v) for k in ks)
                rhs=ca*1j**(-a)*((p-1)/(2*sqrt(p))*(kl3[w]+(-1)**a*kl3[wm])+(a==0)/p**1.5)
                close(direct,rhs,('T1 left',disc,p,a,v));counts['T1 left']+=1
print('Direct CRT and primitive parity kernel checks:',counts)

def logh(s,a,q):
    return (mp.mpf('.5')-s)*mp.log(q/mp.pi)+mp.loggamma((1-s+a)/2)-mp.loggamma((s+a)/2)
betas=[mp.mpc(0,'.001'),mp.mpc(0,'.002'),mp.mpc(0,'.003')]
def B(s,a,q):return mp.exp(-sum(logh(s+b,a,q)-logh(s,a,q) for b in betas)/2)
for a in [0,1]:
    for c in [0,1]:
        s=mp.mpc('.5',100);q=mp.mpf(11);D=mp.mpf(8)
        ha=mp.exp(logh(s,a,q));hb=mp.exp(logh(s,(a+c)%2,D*q))
        assert abs(abs(ha)-1)<mp.mpf('1e-45') and abs(abs(hb)-1)<mp.mpf('1e-45')
        Ec=1 if c==0 else (-1j*mp.tan(mp.pi*s/2) if a==0 else 1j/mp.tan(mp.pi*s/2))
        assert abs(abs(Ec)-1)<mp.mpf('1e-45')
        Eb=mp.exp(sum(logh(s+b,a,q)-logh(s,a,q) for b in betas))
        assert abs(B(s,a,q)**2*Eb-1)<mp.mpf('1e-45')
print('Both parities: central gamma moduli, exact Echi modulus, and inherited branch identity passed')

# A finite-window Cauchy rectangle checks orientations using the exact gamma branch.
q=mp.mpf(11);D=mp.mpf(8);t0=mp.mpf(30);H=mp.mpf(3);W=mp.mpf('1.3')
sigma1=mp.mpf('1.5');sigma2=mp.mpf('2.7');x=mp.mpf(100000)
def integrand(s):
    omega=mp.sqrt(mp.pi)/W*mp.exp((s-mp.mpc('.5',t0))**2/(4*W**2))
    return B(s,0,q)*mp.exp(-logh(s,0,q)-logh(s,1,D*q))*x**(-s)*omega
v1=1j*mp.quad(lambda t:integrand(mp.mpc(sigma1,t)),[t0-H,t0+H])
v2=1j*mp.quad(lambda t:integrand(mp.mpc(sigma2,t)),[t0-H,t0+H])
bottom=mp.quad(lambda sig:integrand(mp.mpc(sig,t0-H)),[sigma1,sigma2])
top=mp.quad(lambda sig:integrand(mp.mpc(sig,t0+H)),[sigma1,sigma2])
assert abs(v1-v2-bottom+top)<mp.mpf('1e-40')
print('Exact finite-window Mellin rectangle orientation/regression passed')
print('ALL CHECKS PASSED. These checks do not prove the uniform analytic estimates or a favorable gain.')
