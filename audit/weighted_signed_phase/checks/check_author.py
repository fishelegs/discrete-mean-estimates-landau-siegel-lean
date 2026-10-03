import cmath
import itertools
import json
import math
from pathlib import Path
from sympy import primitive_root, kronecker_symbol

ROOT = Path(__file__).resolve().parent

import argparse
_parser = argparse.ArgumentParser(description=__doc__)
_parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'results' / 'AUTHOR_RERUN.json')
_OUTPUT = _parser.parse_args().output
_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
worst = 0.0
counts = {'gauss_moments': 0, 'crt_parity': 0, 'double_fourier': 0}

def check(x, y, label):
    global worst
    err = abs(x-y)
    worst = max(worst, err)
    assert err < 1e-8, (label, x, y, err)
    counts[label] += 1

def chars(p):
    g = int(primitive_root(p))
    logs = {pow(g,k,p):k for k in range(p-1)}
    return [[0j] + [cmath.exp(2j*math.pi*k*logs[n]/(p-1)) for n in range(1,p)]
            for k in range(p-1)]

def ep(x,p): return cmath.exp(2j*math.pi*(x%p)/p)

for p in [5,7,11,13]:
    cs = chars(p)
    tau = [sum(c[n]*ep(n,p) for n in range(1,p)) for c in cs]
    def kl(d,v):
        return p**(-(d-1)/2)*sum(ep(sum(xs)+v*pow(math.prod(xs),-1,p),p)
            for xs in itertools.product(range(1,p),repeat=d-1))
    for a in [0,1]:
        for d in [1,3]:
            for t in range(1,p):
                lhs=sum((tau[k]/((1j)**a*math.sqrt(p)))**d * cs[k][t]
                    for k in range(1,p-1) if k%2==a)
                ti=pow(t,-1,p)
                rhs=(1j)**(-d*a)*((p-1)/(2*math.sqrt(p))*(kl(d,ti)+(-1)**a*kl(d,-ti))
                    +(p**(-d/2) if a==0 else 0))
                check(lhs,rhs,'gauss_moments')
        # The stripped cubic root kernel; no D or i-parity constants.
        def G(c):
            return (p-1)/(2*math.sqrt(p))*(kl(3,c)+(-1)**a*kl(3,-c)) + (p**(-1.5) if a==0 else 0)
        for c in [1,2]:
            for h,k in itertools.product(range(p),repeat=2):
                lhs=sum(G(c*r*s)*ep(h*r+k*s,p) for r,s in itertools.product(range(1,p),repeat=2))
                if h*k%p==0:
                    rhs=0
                else:
                    v=c*pow(h*k,-1,p)
                    rhs=(p-1)*math.sqrt(p)/2*(ep(v,p)+(-1)**a*ep(-v,p)) + (math.sqrt(p) if a==0 else 0)
                check(lhs,rhs,'double_fourier')
    for Delta in [-3,-4,5,-7,8,12]:
        D=abs(Delta)
        if D%p==0: continue
        chi=[int(kronecker_symbol(Delta,n)) for n in range(D)]
        c=0 if Delta>0 else 1
        tchi=sum(chi[n]*ep(n,D) for n in range(D))
        echi=tchi/((1j)**c*math.sqrt(D))
        for j in range(1,p-1):
            a=j%2
            b=(a+c)%2
            tp=sum(chi[n%D]*cs[j][n%p]*ep(n,D*p) for n in range(D*p))
            lhs=tp/((1j)**b*math.sqrt(D*p))
            rhs=(-1)**(a*c)*chi[p%D]*cs[j][D%p]*echi*tau[j]/((1j)**a*math.sqrt(p))
            check(lhs,rhs,'crt_parity')

result={'status':'PASS','counts':counts,'max_absolute_error':worst,
        'scope':'Finite parity/CRT/Fourier regression only; not an analytic estimate or Lean certificate.',
        'exact_exponents':{'right_bound':'-1989/4000 + o(1)',
                           'left_bare_pair_cost':'1 + theta - saving + o(1)',
                           'normalization':'a * sum_p p',
                           'inverse_error_squared':'-1077/2','phase_error_squared':'-203'}}
_OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
