#!/usr/bin/env python3
"""Independent regression checks. These do not prove uniform analytic estimates."""
from fractions import Fraction as F
from math import comb, gcd, pi, sqrt
import cmath
import hashlib
import argparse
from pathlib import Path
import sympy as sp

x,y=sp.symbols('x y', nonzero=True)
k=x+y+x*y-1
ksq=sp.expand(k*(1/x+1/y+1/(x*y)-1))
assert sp.simplify(ksq-(4-(x-1/x)*(y-1/y)))==0
# With x=e^(i theta1), y=e^(i theta2), the second term is 4 sin(theta1) sin(theta2).
d=sp.symbols('d')
assert sp.expand((1-5*d)+2*(1+d)-3*(1-d))==0
print('Exact beta relation and prime coefficient identity passed')

left=F(36,2)+F(81,6)+F(81,6)-F(739,6)+F(77*5,6)
right=F(144,4)+F(81,6)+F(81,6)-F(739*5,12)+F(77*7,12)
assert left==-14 and right==-200
assert 2*F(999,1000)<2
assert 3*F(504,1000)<2
assert F(1005,1000)<2
gaps={
 'C1 right':F(999+503+499,1000)-2,
 'C1 left':F(1003-503-499,1000),
 'T1 right J':F(1005+503-1000-504,1000),
 'T1 left J':F(1005+500-1000-503,1000),
 'T1 right A':F(1005,1000)-1,
 'T1 left A':F(1005,1000)-1,
}
assert all(v>0 for v in gaps.values())
assert F(1003+500-1000-503,1000)==0
print('Exact Holder budgets:', {'left_C1_and_both_T1':str(left),'right_C1':str(right)})
print('Exact power-of-P tail gaps:', {k:str(v) for k,v in gaps.items()})
print('P^1.003 target dual-left endpoint has zero gap and fails to absorb t0')

def close(a,b,label,tol=1e-9):
    assert abs(a-b)<tol,(label,a,b,abs(a-b))

def coeffs(theta1,theta2,upto):
    xx=cmath.exp(1j*theta1); yy=cmath.exp(1j*theta2)
    out=[1]+[0]*upto
    for z in (xx,yy,xx*yy):
        out=[sum(out[j]*z**(n-j) for j in range(n+1)) for n in range(upto+1)]
    return [out[0]]+[out[n]-out[n-1] for n in range(1,upto+1)]

for t1,t2 in [(0,0),(.3,.7),(1.7,2.9),(-2,4)]:
    cs=coeffs(t1,t2,12)
    close(abs(cs[1])**2,4+4*sp.sin(t1)*sp.sin(t2),'prime norm')
    lam=[abs(z) for z in cs]
    lam2=[sum(lam[j]*lam[n-j] for j in range(n+1)) for n in range(len(lam))]
    for n in range(len(cs)):
        assert lam[n]<=comb(n+3,3)+1e-9
        assert lam2[n]<=comb(n+7,7)+1e-8
    close(lam2[1]**2,4*abs(cs[1])**2,'absolute convolution prime')
print('Prime-power d4/d8 majorants and absolute-convolution coefficient checks passed')

def e(x): return cmath.exp(2j*pi*float(x))
def generator(p):
    return next(g for g in range(2,p) if len({pow(g,j,p) for j in range(p-1)})==p-1)

count=0
for disc in [-8,12,13]:
    D=abs(disc); chi=lambda n: complex(sp.kronecker_symbol(disc,n))
    c=0 if chi(-1)==1 else 1
    tc=sum(chi(n)*e(F(n,D)) for n in range(D))
    ec=tc/(1j**c*sqrt(D))
    for p in [11,17,23]:
        if gcd(D,p)>1: continue
        g=generator(p); logs={pow(g,j,p):j for j in range(p-1)}
        def psi(k,n): return 0 if n%p==0 else e(F(k*logs[n%p],p-1))
        tau={k:sum(psi(k,n)*e(F(n,p)) for n in range(1,p)) for k in range(p-1)}
        roots={}
        for k in range(1,p-1):
            a=k%2; b=(a+c)%2
            tt=sum(chi(n)*psi(k,n)*e(F(n,D*p)) for n in range(D*p))
            ep=tau[k]/(1j**a*sqrt(p)); ecp=tt/(1j**b*sqrt(D*p))
            roots[k]=(ep,ecp,ep*ecp)
        for a in [0,1]:
            ks=[k for k in range(1,p-1) if k%2==a]
            ca=(-1)**(c*a+a)*chi(p)*ec
            da=(-1)**(c*a)*chi(p)*ec
            def h3(z):
                return sum(e(F(u+w+z*pow(u*w,-1,p),p)) for u in range(1,p) for w in range(1,p))
            for v in range(1,p):
                z=pow(D*v,-1,p)
                directR=sum(roots[k][1]*psi(k,v) for k in ks)
                wantR=da*1j**(-a)/sqrt(p)*((p-1)/2*(e(F(z,p))+(-1)**a*e(F(-z,p)))+(a==0))
                directL=sum(roots[k][2]*roots[k][0]*psi(k,v) for k in ks)
                wantL=ca*1j**(-a)/(p*sqrt(p))*((p-1)/2*(h3(z)+(-1)**a*h3(-z))+(a==0))
                close(directR,wantR,('T1 right',disc,p,a,v))
                close(directL,wantL,('T1 left',disc,p,a,v))
                count+=2
print(count,'T1 single/triple Gauss identities passed, both parities and nonsquarefree conductors')

# Scalar factors of the four Mellin expansions, checked as Laurent monomials.
ell,m,n,D=sp.symbols('ell m n D', positive=True)
s=sp.symbols('s', real=True)
assert sp.simplify(D**(s-1)*ell**(s-1)*m**(-s)*n**(-s) - (D*ell)**(-1)*(m*n/(D*ell))**(-s))==0
assert sp.simplify(ell**(-s)*m**(-s)*n**(s-1) - n**(-1)*(ell*m/n)**(-s))==0
assert sp.simplify(ell**(s-1)*m**(-s)*n**(s-1) - (ell*n)**(-1)*(m/(ell*n))**(-s))==0
print('C1-left and T1-right/left Mellin scalar factors passed')
parser=argparse.ArgumentParser(description='Finite algebra checks; optional external TeX identity check')
parser.add_argument('--source',type=Path,help='Local extracted arXiv v1 TeX file to hash; omitted means source identity check is skipped')
args=parser.parse_args()
if args.source is None:
    print('Source-file SHA256 check SKIPPED: no --source input supplied; finite algebra checks ran')
else:
    source_digest=hashlib.sha256(args.source.read_bytes()).hexdigest()
    assert source_digest == '5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b', 'External source SHA256 does not match the audited input'
    print('Primary source SHA256:',source_digest)
print('ALL CHECKS PASSED; uniform bounds require the written proof')
