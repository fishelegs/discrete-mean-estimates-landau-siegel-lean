#!/usr/bin/env python3
"""Independent finite audit. Does not import or execute candidate checkers."""
from fractions import Fraction as F
from functools import lru_cache
import cmath, json, math

@lru_cache(None)
def factors(n):
    ans=[]; p=2
    while p*p<=n:
        j=0
        while n%p==0: n//=p; j+=1
        if j: ans.append((p,j))
        p+=1
    if n>1: ans.append((n,1))
    return tuple(ans)

def divisors(n):
    ans=[1]
    for p,j in factors(n):
        ans=[d*p**k for d in ans for k in range(j+1)]
    return ans
def sf(n): return math.prod(p for p,j in factors(n) if j%2)
def mob(n): return 0 if any(j>1 for p,j in factors(n)) else (-1)**len(factors(n))
def tau(n): return math.prod(j+1 for p,j in factors(n))
def chi(n,D):
    return {3:(0,1,-1),4:(0,1,0,-1),5:(0,1,-1,-1,1),
            8:(0,1,0,-1,0,-1,0,1),12:(0,1,0,0,0,-1,0,-1,0,0,0,1)}[D][n%D]
def nu(n,D): return sum(chi(d,D) for d in divisors(n))
def ups(n,D): return math.prod({0:1,1:-1-chi(p,D),2:chi(p,D)}.get(j,0) for p,j in factors(n))
def cx(n,D,X): return sum(nu(e,D)*ups(n//e,D) for e in divisors(n) if e<=X)
def rho(n,D,X): return sum(nu(e,D)*ups(n//e,D) for e in divisors(n) if e>X)
def isprime(n): return n>=2 and factors(n)==((n,1),)

arithmetic=0
for D in (3,4,5,8,12):
    for X in (3,7,11):
        for n in range(1,301):
            assert rho(n,D,X)+cx(n,D,X)==int(n==1)
            assert abs(cx(n,D,X))<=nu(n,D)*tau(n)
            arithmetic+=1
        for ell in range(X+1,38):
            if not isprime(ell) or chi(ell,D)!=1: continue
            for w in range(1,41):
                if w%ell==0: continue
                for j,mult in ((1,2),(2,-1),(3,0),(4,0)):
                    assert rho(ell**j*w,D,X)==mult*cx(w,D,X)
                    arithmetic+=1

factorization=0
for D in (3,4,5,8,12):
    for f in range(1,1800):
        if ups(f,D)==0: continue
        r=t=b=1
        for p,j in factors(f):
            if chi(p,D)==0: r*=p
            elif j==2: t*=p
            else: b*=p
        assert f==r*t*t*b
        assert ups(f,D)==mob(r)*chi(t,D)*(-2)**len(factors(b))
        assert math.gcd(t,b)==1 and D%r==0
        for Z in (2,3,7,13):
            if b<Z: continue
            a=1
            for q,j in factors(b):
                a*=q
                if a>=Z: break
            d=b//a
            pmax=max(p for p,j in factors(a))
            assert a//pmax<Z<=a
            assert d==1 or pmax<min(p for p,j in factors(d))
            for e in range(1,31):
                g=sf(e*r); ga=math.gcd(g,a); gd=math.gcd(g,d)
                assert math.gcd(ga,gd)==1
                assert sf(e*r*t*t*a*d)==g*a*d//(ga*gd)**2
                for H in (1,11,100):
                    assert (sf(e*r*t*t*a*d)>H)==(g*a*d>H*(ga*gd)**2)
                factorization+=1

def chars(p):
    primes=[q for q,j in factors(p-1)]
    gen=next(g for g in range(2,p) if all(pow(g,(p-1)//q,p)!=1 for q in primes))
    logs={pow(gen,k,p):k for k in range(p-1)}
    return [[0]+[cmath.exp(2j*math.pi*k*logs[x]/(p-1)) for x in range(1,p)] for k in range(p-1)]
def ep(x,p): return cmath.exp(2j*math.pi*(x%p)/p)
gauss_cases=0; max_gauss_error=0.0; max_crt_error=0.0; root_cases=0
for p in (3,5,7,11,13,17,19):
    cs=chars(p)
    gs=[sum(ch[x]*ep(x,p) for x in range(1,p)) for ch in cs]
    for parity in (0,1):
        for c in range(p):
            for n in range(p):
                lhs1=sum(gs[k]*cs[k][c]*cs[k][n].conjugate() for k in range(1,p-1) if k%2==parity)
                lhs2=sum(gs[(p-1-k)%(p-1)]*cs[k][c]*cs[k][n].conjugate() for k in range(1,p-1) if k%2==parity)
                if c*n%p==0:
                    rhs1=rhs2=0
                else:
                    z=n*pow(c,-1,p)%p; w=c*pow(n,-1,p)%p
                    rhs1=(p-1)/2*(ep(z,p)+(-1)**parity*ep(-z,p))+int(parity==0)
                    rhs2=(p-1)/2*(ep(w,p)+(-1)**parity*ep(-w,p))+int(parity==0)
                err=max(abs(lhs1-rhs1),abs(lhs2-rhs2))
                max_gauss_error=max(max_gauss_error,err)
                assert err<2e-11
                gauss_cases+=1
    for D in (3,4,5,8,12):
        if D%p==0: continue
        q=D*p
        tg=sum(chi(x,D)*ep(x,D) for x in range(D))
        for k in range(1,p-1):
            ch=cs[k]; a=k%2; b=int(round((1-chi(D-1,D)*((-1)**a))/2))
            gp=sum(chi(x,D)*ch[x%p]*ep(x,q) for x in range(q))
            gb=sum(chi(x,D)*ch[x%p].conjugate()*ep(x,q) for x in range(q))
            crt=chi(p,D)*ch[D%p]*tg*gs[k]
            max_crt_error=max(max_crt_error,abs(gp-crt))
            assert abs(gp-crt)<2e-11
            eps=gs[k]/((1j)**a*math.sqrt(p)); epsc=gp/((1j)**b*math.sqrt(q))
            pure=gs[(p-1-k)%(p-1)]/math.sqrt(p); mixed=gb/math.sqrt(q)
            assert abs(eps**2*epsc*pure*mixed-(1j)**(a+b)*eps)<2e-11
            assert abs(eps**2*epsc*pure**2*mixed-(1j)**(2*a+b))<2e-11
            assert abs(eps**2*epsc*pure**3*mixed-(1j)**(2*a+b)*pure)<2e-11
            root_cases+=1

conductor_cases=0
for D in (3,4,5,8,12):
    tg=sum(chi(b,D)*ep(b,D) for b in range(D))
    for p in (7,11,13):
        if D%p==0: continue
        q=D*p
        for n in range(1,q):
            if math.gcd(n,q)>1: continue
            for a in (1,2,p-1):
                for power in (1,-1):
                    z=n if power==1 else pow(n,-1,q)
                    rhs=sum(chi(b,D)*ep((a*D+b*p)*z,q) for b in range(D))/tg
                    lhs=chi(n,D)*ep(a*z,p)
                    assert abs(lhs-rhs)<2e-11
                    conductor_cases+=1

mask_cases=0; max_mask_error=0.0
for J in (2,5,9,17,31):
    mod=2*J+1
    coeff=[sum(ep(-h*z,mod) for z in range(1,J+1))/mod for h in range(mod)]
    for x in range(1,J+1):
        for y in range(1,J+1):
            got=sum(coeff[h]*ep(h*(y-x),mod) for h in range(mod))
            max_mask_error=max(max_mask_error,abs(got-int(x<y)))
            assert abs(got-int(x<y))<2e-11
            mask_cases+=1
    assert sum(abs(x) for x in coeff)<3*(1+math.log(mod))

def sadd(theta): return max(F(0),min(F(1,2),theta/5,(theta-1)/2))
def smid(theta): return min(theta/16,theta/3-F(1,4))
def slong(theta): return min(F(1,2),theta/5-F(1,4))
def bg(alpha,beta,k1,k2):
    return -(max((k1-1)*alpha-F(1,2),F(1,2)-k1*alpha)+max((k2-1)*beta-F(1,2),F(1,2)-k2*beta))/(2*k1*k2)
def sab(alpha,beta): return (alpha+beta-1-max(F(0),alpha-1)-max(F(0),beta-1))/2
delta=bg(F(3,40),F(3,40),7,7)
assert delta==F(1,1960)
assert slong(F(301,100))==F(44,125)
assert F(301,100)-slong(F(301,100))+F(1,1000)==F(2659,1000)
assert F(99,100)-smid(F(99,100))+F(1,1000)==F(7433,8000)
for i in range(1,601):
    theta=F(i,100)
    assert sadd(theta)<=F(1,2)
    if theta>1: assert theta-1-sadd(theta)>0
    for j in range(1,40):
        assert bg(theta,F(j,20),1,1)<=F(1,2)
        assert sab(theta,F(j,20))<=F(1,2)

budgets={}
for r in (2,3,4):
    cutoff_power=F(r,2)*(F(1,8000)+F(1,10000))
    assert cutoff_power<F(1,1000)
    budgets[str(r)]={'square_root_completion_power':str(cutoff_power),
                     'slack_to_coarse_0.001':str(F(1,1000)-cutoff_power)}

result={'status':'PASS',
        'arithmetic_cases':arithmetic, 'balanced_factorization_cases':factorization,
        'gauss_kernel_cases':gauss_cases, 'gauss_max_error':max_gauss_error,
        'completion_root_cases':root_cases, 'crt_max_error':max_crt_error,
        'prime_conductor_reduction_cases':conductor_cases,
        'order_mask_cases':mask_cases, 'order_mask_max_error':max_mask_error,
        'BG_example':str(delta), 'completion_budgets':budgets,
        'scope':'Finite algebra/numerical Gauss checks and exact rational budgets; no analytic or Lean verification'}
print(json.dumps(result,indent=2))
