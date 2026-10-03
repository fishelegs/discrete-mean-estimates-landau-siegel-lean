#!/usr/bin/env python3
"""Checks extra exact bilinear algebra; no compilation or asymptotic claim."""
from fractions import Fraction as F
import cmath, json, math


def fac(n):
    ans={}; p=2
    while p*p<=n:
        while n%p==0: ans[p]=ans.get(p,0)+1; n//=p
        p+=1
    if n>1: ans[n]=ans.get(n,0)+1
    return ans

def sf(n): return math.prod(p for p,j in fac(n).items() if j%2)
def chi(n,D):
    return ({5:[0,1,-1,-1,1],8:[0,1,0,-1,0,-1,0,1],12:[0,1,0,0,0,-1,0,-1,0,0,0,1]}[D])[n%D]

cases=0
for D in (5,8,12):
    for f in range(1,1500):
        r=t=b=1; val=1; ok=True
        for p,j in fac(f).items():
            ch=chi(p,D)
            local=({1:-(1+ch),2:ch}.get(j,0))
            val*=local
            if local==0: ok=False; break
            if ch==0: r*=p
            elif j==2: t*=p
            else: b*=p
        if not ok: continue
        assert f==r*t*t*b
        assert val==(-1)**len(fac(r))*chi(t,D)*(-2)**len(fac(b))
        ps=sorted(fac(b))
        for Z in (2,5,10,30):
            if b<Z: continue
            a=1
            for q in ps:
                a*=q
                if a>=Z: break
            d=b//a
            assert a//max(fac(a))<Z<=a
            assert d==1 or max(fac(a))<min(fac(d))
            assert math.gcd(a,d)==1
            for e in range(1,25):
                g=sf(e*r)
                assert sf(e*r*t*t*a*d)==g*a*d//math.gcd(g,a*d)**2
                ga,gd=math.gcd(g,a),math.gcd(g,d)
                assert math.gcd(ga,gd)==1
                assert math.gcd(g,a*d)==ga*gd
                cases+=1

max_err=0.0
for J in (4,9,23):
    m=2*J+1
    h=[0]+[int(1<=z<=J) for z in range(1,m)]
    coeff=[sum(h[z]*cmath.exp(-2j*math.pi*k*z/m) for z in range(m))/m for k in range(m)]
    for x in range(1,J+1):
        for y in range(1,J+1):
            approx=sum(coeff[k]*cmath.exp(2j*math.pi*k*(y-x)/m) for k in range(m))
            err=abs(approx-int(y>x)); max_err=max(max_err,err)
            assert err<1e-11
    assert sum(map(abs,coeff))<=3*(1+math.log(m))

alpha=beta=F(3,40); k1=k2=7
delta=-(max((k1-1)*alpha-F(1,2),F(1,2)-k1*alpha)+max((k2-1)*beta-F(1,2),F(1,2)-k2*beta))/(2*k1*k2)
assert delta==F(1,1960)
result={'upsilon_and_balanced_mask_cases':cases,'order_mask_fourier_max_error':max_err,'BG_example_saving':str(delta),'scope':'Finite algebra and exact rational arithmetic; no analytic proof'}
print(json.dumps(result,indent=2))
