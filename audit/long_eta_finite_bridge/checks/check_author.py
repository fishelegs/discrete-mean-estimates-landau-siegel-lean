#!/usr/bin/env python3
"""Finite algebra/accounting checks; no asymptotic or sign certification."""
from fractions import Fraction
from pathlib import Path
import json, math, hashlib
import mpmath as mp

BASE=Path(__file__).resolve().parent

import argparse
_parser = argparse.ArgumentParser(description=__doc__)
_parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'results' / 'AUTHOR_RERUN.json')
_OUTPUT = _parser.parse_args().output
_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
LIMIT=220
def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]
DIV=[[]]+[divisors(n) for n in range(1,LIMIT+1)]
def factors(n):
    out={}; p=2
    while p*p<=n:
        while n%p==0:
            out[p]=out.get(p,0)+1; n//=p
        p+=1
    if n>1:out[n]=out.get(n,0)+1
    return out
FAC=[{}]+[factors(n) for n in range(1,LIMIT+1)]
def mu(n):
    es=FAC[n].values()
    return 0 if any(e>1 for e in es) else (-1)**sum(es)
def conv(a,b,n):return sum(a[d]*b[n//d] for d in DIV[n])
def tau(k,n):return math.prod(math.comb(e+k-1,k-1) for e in FAC[n].values())
tables={3:[0,1,-1],4:[0,1,0,-1],5:[0,1,-1,-1,1],8:[0,1,0,-1,0,-1,0,1]}
one=[0]+[1]*LIMIT
mob=[0]+[mu(n) for n in range(1,LIMIT+1)]
counts={'convolution':0,'tail':0,'kappa':0,'divisor':0,'fourier':0,'root_cancellation':0}
for mod,table in tables.items():
    chi=[0]+[table[n%mod] for n in range(1,LIMIT+1)]
    nu=[0]+[conv(one,chi,n) for n in range(1,LIMIT+1)]
    # Exact Gaussian integers: arbitrary completely multiplicative unit powers.
    for seed in range(4):
        alpha=[0]+[(1j)**sum(((p+seed)%4)*e for p,e in FAC[n].items()) for n in range(1,LIMIT+1)]
        eta=[0]+[conv(mob,alpha,n) for n in range(1,LIMIT+1)]
        for n in range(1,LIMIT+1):
            assert conv(eta,nu,n)==conv(alpha,chi,n)
            assert abs(eta[n])<=tau(2,n)+1e-12
            counts['convolution']+=1
        for X in [1,2,7,20,50]:
            short=[nu[n] if n<=X else 0 for n in range(LIMIT+1)]
            tail=[nu[n] if n>X else 0 for n in range(LIMIT+1)]
            for n in range(1,LIMIT+1):
                assert conv(eta,short,n)-conv(alpha,chi,n)==-conv(eta,tail,n)
                counts['tail']+=1
        a1=[0]+[(-1)**sum(FAC[n].values()) for n in range(1,LIMIT+1)]
        a2=[0]+[(1j)**sum(FAC[n].values()) for n in range(1,LIMIT+1)]
        kap1=[0]+[conv(eta,a1,n) for n in range(1,LIMIT+1)]
        kap=[0]+[conv(kap1,a2,n) for n in range(1,LIMIT+1)]
        rhs1=[0]+[conv(chi,alpha,n) for n in range(1,LIMIT+1)]
        rhs2=[0]+[conv(rhs1,a1,n) for n in range(1,LIMIT+1)]
        for n in range(1,LIMIT+1):
            assert conv(kap,nu,n)==conv(rhs2,a2,n)
            counts['kappa']+=1

for n in range(1,LIMIT+1):
    assert tau(2,n)**2*tau(3,n)<=tau(12,n)
    assert tau(2,n)**2*tau(3,n)**2<=tau(36,n)
    assert tau(5,n)**2<=tau(25,n)
    assert tau(3,n)**2<=tau(9,n)
    assert tau(2,n)**3<=tau(8,n)
    assert tau(2,n)**4<=tau(16,n)
    assert tau(6,n)**2<=tau(36,n)
    counts['divisor']+=7
for a in range(1,36):
    for b in range(1,36):
        fs=factors(a*b)
        t3ab=math.prod(math.comb(e+2,2) for e in fs.values())
        assert t3ab<=tau(3,a)*tau(3,b)
        counts['divisor']+=1

exponents={
    'eta_weighted_energy':Fraction(9*12),
    'nu_tail_weighted_energy':-Fraction(2011,2)+Fraction(9*36,2),
    'H_weighted_energy':Fraction(9*3),
}
exponents['error_energy']=sum(exponents.values())
exponents['C_energy']=Fraction(9*25)
exponents['per_box_error']=77+(exponents['error_energy']+exponents['C_energy'])/2
exponents['all_box_error']=exponents['per_box_error']+27
assert exponents['error_energy']==-Fraction(1417,2)
assert exponents['per_box_error']==-Fraction(659,4)
assert exponents['all_box_error']==-Fraction(551,4)
assert 77+(225+81)//2==230
assert 230+27==257
strong={
    'eta_weighted_energy':Fraction(9*8),
    'nu_tail_weighted_energy':-Fraction(2011,2)+Fraction(9*16,2),
}
strong['error_energy']=sum(strong.values())
strong['C3_energy']=Fraction(9*36)
strong['per_box_error']=77+(strong['error_energy']+strong['C3_energy'])/2
strong['all_box_error']=strong['per_box_error']+36
assert strong['error_energy']==-Fraction(1723,2)
assert strong['per_box_error']==-Fraction(767,4)
assert strong['all_box_error']==-Fraction(623,4)
assert 77+(324+36)//2==257
assert 257+36==293

length_examples=[]
theta=Fraction(201,400) # .5025
for r,s in [(Fraction(1),Fraction(1)),(Fraction(9,10),Fraction(9,10)),(Fraction(4,5),Fraction(4,5))]:
    n=3-r-s
    c=theta+2-r-s
    d=theta+n
    assert c<2 and d<2
    assert d-c==1
    length_examples.append({'r':str(r),'s':str(s),'n':str(n),'C':str(c),'D':str(d)})
strong_length={'r':str(Fraction(3,5)),'s':str(Fraction(3,5)),
               'n':str(Fraction(9,5)),'C3':str(Fraction(9,5)),
               'D3':str(Fraction(9,5)),'old_D':str(Fraction(9,5)+theta)}
assert Fraction(strong_length['old_D'])>2
# The original example is leading scale only. Keep the fixed profile width.
strong_length['scope']='Leading-scale illustration; both exact T3 conditions remain mandatory.'
strong_length['profile_width']=str(Fraction(1,2000))
strong_length['C3_with_profile_width']=str(Fraction(9,5)+Fraction(1,2000))
strong_length['N_envelope_upper']=str(Fraction(9,5)+Fraction(1,2000))
assert Fraction(strong_length['C3_with_profile_width'])<2

def generator(p):
    for g in range(2,p):
        if len({pow(g,k,p) for k in range(p-1)})==p-1:return g
for p in [5,7,11,13]:
    g=generator(p)
    logs={pow(g,k,p):k for k in range(p-1)}
    for k in range(1,p-1):
        def psi(n):
            return 0j if n%p==0 else complex(mp.exp(2j*mp.pi*k*logs[n%p]/(p-1)))
        a=k%2
        ep=sum(psi(x)*complex(mp.exp(2j*mp.pi*x/p)) for x in range(p))/((1j)**a*math.sqrt(p))
        gp=sum(psi(x).conjugate()*complex(mp.exp(2j*mp.pi*x/p)) for x in range(p))/math.sqrt(p)
        for D,tab in tables.items():
            if math.gcd(D,p)>1:continue
            chi=lambda n:tab[n%D]
            c=0 if chi(-1)==1 else 1
            b=(a+c)%2
            dp=D*p
            ect=sum(chi(x)*psi(x)*complex(mp.exp(2j*mp.pi*x/dp)) for x in range(dp))/((1j)**b*math.sqrt(dp))
            gct=sum(chi(x)*psi(x).conjugate()*complex(mp.exp(2j*mp.pi*x/dp)) for x in range(dp))/math.sqrt(dp)
            assert abs(ep**2*ect*gp**2*gct-(1j)**(2*a+b))<1e-11
            counts['root_cancellation']+=1

mp.mp.dps=45
def phi(x):
    return mp.exp(-1/((x-mp.mpf('0.5'))*(2-x))) if mp.mpf('0.5')<x<2 else mp.mpf(0)
worst=mp.mpf(0)
for p,R,t,h in [(101,80,20,3),(101,80,20,7),(149,120,50,8),(149,120,50,13)]:
    p,R,t,h=map(mp.mpf,(p,R,t,h))
    lhs=mp.quad(lambda x:x**(-mp.mpf('.5')+1j*t)*phi(x/R)*mp.exp(-2j*mp.pi*x*h/p),[R/2,R,2*R])/mp.sqrt(p)
    y=2*mp.pi*h*R/(p*t)
    vt=mp.sqrt(t/(2*mp.pi))*mp.quad(lambda z:z**(-mp.mpf('.5'))*phi(z/y)*mp.exp(1j*t*(mp.log(z)-z+1)),[y/2,y,2*y])
    rhs=h**(-mp.mpf('.5'))*mp.exp(1j*t*mp.log(p*t/(2*mp.pi*mp.e*h)))*vt
    err=abs(lhs-rhs)/max(mp.mpf(1),abs(lhs),abs(rhs))
    worst=max(worst,err)
    assert err<mp.mpf('1e-35')
    counts['fourier']+=1

result={'status':'PASS','scope':'Finite identities and exact exponent checks only; no sign theorem or asymptotic certification.',
        'counts':counts,'exponents':{k:str(v) for k,v in exponents.items()},
        'strong_exponents':{k:str(v) for k,v in strong.items()},
        'length_examples':length_examples,'strong_length_example':strong_length,
        'max_fourier_error':str(worst)}
_OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
