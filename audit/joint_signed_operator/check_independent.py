#!/usr/bin/env python3
"""Independent rational, divisor, and finite-principal regressions.

No candidate code is imported or executed. No repository file is written.
The universal source proofs are in REVIEW.md, not supplied by finite tests.
"""
import cmath
import json
import math
from fractions import Fraction as Q

result = {}

def require(condition, reason):
    if not condition:
        raise AssertionError(reason)

def strq(x):
    x = Q(x)
    return f'{x.numerator}/{x.denominator}'

lo, hi = Q(251,500), Q(201,400)
width = hi-lo
require(width == Q(1,2000), 'Profile width')
Cpaid = 1+width+Q(1,1000)+Q(1,8000)+Q(1,10000)
Ypaid = 3+width+Q(1,1000)
C, Y = Q(501,500), Q(1501,500)
require(Cpaid < C < 2 and Ypaid < Y < 4, 'Whole support exponents')
principal = (C+Y)/2 - 2 - lo
require(principal == -Q(1,2), 'Principal P exponent')
require(30+(1-400001)*Q(1,8000) == -20, 'Fourier tail budget')
require(30-500000*Q(1,10000) == -20, 'Mask Mellin tail budget')
result['support'] = {
    'profile_width': strq(width), 'C_raw_paid': strq(Cpaid),
    'Y_raw_paid': strq(Ypaid), 'C_envelope': strq(C), 'Y_envelope': strq(Y),
    'C_slack': strq(C-Cpaid), 'Y_slack': strq(Y-Ypaid),
    'principal_power_before_absorption': strq(principal),
    'fourier_tail_power': '-20', 'mask_tail_power': '-20'
}

energy = []
divisor_cases = 0
for q in range(3,7):
    r = 9*q*(q+1)//2
    low = -Q(1997,2)+8*q*q
    high = 2*r-2015
    require(high < low, 'High rho tail dominated')
    require(2*r >= 16*q and r >= 4*q, 'Split/ramified convolution monotonicity')
    ED = low+9*q*(q-1)
    completions = 6-q
    EC = 9*(completions+3)**2
    total = 149+(EC+ED)/2
    energy.append({'smooth_completions': completions, 'q': q, 'convolution_order':r,
                   'rho_low':strq(low), 'rho_high':strq(high), 'E_C':strq(EC),
                   'E_D':strq(ED), 'total_log':strq(total)})
    for j in range(257):
        tau = lambda r,e: math.comb(e+r-1,r-1)
        require((j+1)**4*tau(q,j) <= tau(2*r,j), 'split local inequality')
        require((j+1)**2*tau(q,j) <= tau(r,j), 'ramified local inequality')
        require((2*j+1)**2*tau(q,2*j) <= tau(r,j), 'inert local inequality')
        require(tau(q,2*j) <= tau(q*(q+1)//2,j), 'pairing inequality')
        divisor_cases += 4
result['energy'] = energy
result['finite_divisor_regressions'] = {'cases':divisor_cases,'exponents':257,'q':[3,4,5,6]}
require(energy[2]['E_D'] == '-1237/2' and energy[2]['E_C'] == '144/1', 'One completion energy')
principal_log = Q(520)+72-Q(1237,4)
require(principal_log == Q(1131,4), 'Explicit principal log budget')
result['principal_log_before_absorption'] = strq(principal_log)

# Exact affine-envelope certification: every piece is affine between these
# breakpoints, so endpoint inequalities certify the entire closed interval.
zero = Q(0)
d1 = lambda k: Q(501,1000)
d2 = lambda k: (max(zero,Q(103,1000)+Q(2,5)*k)+max(zero,-Q(112,125)+Q(2,5)*k))/2
d3 = lambda k: max(zero,-Q(663,1000)+Q(2,3)*k)
breaks = [zero,Q(1989,2000),Q(4287,2800),Q(56,25),Q(359,160),Q(301,100)]
forms = [lambda k:zero, lambda k:-Q(663,1000)+Q(2,3)*k,
         lambda k:Q(103,2000)+k/5,lambda k:-Q(793,2000)+Q(2,5)*k,
         lambda k:Q(501,1000)]
for a,b,f in zip(breaks,breaks[1:],forms):
    for k in (a,b):
        require(f(k)==min(d1(k),d2(k),d3(k)), 'Affine minimum endpoint')
require(Q(1337,1000)+Q(2,3)*Q(497,500)==Q(5999,3000), 'Conservative paid endpoint')
require(Q(1337,1000)+Q(2,3)*Q(1989,2000)==2, 'Exact zero-loss endpoint')
result['envelope'] = {'breakpoints':[strq(x) for x in breaks],
                      'method':'Exact affine comparisons at all slope and crossing breakpoints',
                      'zero_loss_endpoint':strq(Q(1989,2000))}

# Finite divisor/grouping checks for genuine real primitive characters.
characters = {3:[0,1,-1],4:[0,1,0,-1],5:[0,1,-1,-1,1],
              8:[0,1,0,-1,0,-1,0,1],12:[0,1,0,0,0,-1,0,-1,0,0,0,1]}

def mobius(n):
    p, value = 2, 1
    while p*p <= n:
        if n%p==0:
            n//=p
            value=-value
            if n%p==0:
                return 0
        p+=1
    return -value if n>1 else value

def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]

group_cases = abel_cases = rho_cases = 0
maximum_error = 0.
for D,ch in characters.items():
    chi=lambda n:ch[n%D]
    require(sum(ch)==0,'Nonprincipal full-period sum')
    nu=lambda n:sum(chi(d) for d in divisors(n))
    ups=lambda n:sum(mobius(d)*mobius(n//d)*chi(n//d) for d in divisors(n))
    for n in range(1,150):
        convolution=sum(ups(d)*nu(n//d) for d in divisors(n))
        require(convolution==(1 if n==1 else 0),'Literal inverse convolution')
        for X in (2,5,11):
            rho=sum(ups(n//e)*nu(e) for e in divisors(n) if e>X)
            require(abs(rho)<=nu(n)*len(divisors(n)), 'Rho absolute majorant')
            if n<=X:
                require(rho==0,'Rho support')
            rho_cases+=1
    for X in (7,16):
        for t in (0.,.3,7.):
            # Smooth real sample profile, used only to check exact grouping.
            h=lambda m:chi(m)*math.sin(math.pi*(m-17)/20)**2 if 17<m<37 else 0.
            phi=lambda x:max(0.,1-abs(math.log2(x))) if x>0 else 0.
            V=64.
            def w(u):
                return cmath.exp((-0.5-1j*t)*math.log(u))*phi(u/V)
            grouped=0j
            by_d=0j
            for u in range(1,37*X+1):
                A=sum(ups(d)*h(u//d) for d in divisors(u) if d<=X and d%D!=0)
                grouped+=A*w(u)
            for d in range(1,X+1):
                if d%D!=0:
                    by_d+=ups(d)*sum(h(m)*w(d*m) for m in range(18,37))
            err=abs(grouped-by_d)
            maximum_error=max(maximum_error,err)
            require(err<1e-11,'Exact Ahat finite-deletion grouping')
            group_cases+=1
    for start in (1,7,23):
        stop=start+71
        vals=[cmath.exp((-0.5+2.3j)*math.log(n)) for n in range(start,stop+1)]
        partial=0
        for n in range(start,stop+1):
            partial+=chi(n)
            require(abs(partial)<=D,'Incomplete periodic sum')
        left=abs(sum(chi(n)*vals[n-start] for n in range(start,stop+1)))
        right=D*(abs(vals[-1])+sum(abs(a-b) for a,b in zip(vals,vals[1:])))
        require(left<=right+1e-12,'Discrete Abel bound')
        abel_cases+=1
result['finite_principal_and_rho'] = {'conductors':list(characters),'grouping_cases':group_cases,
                                     'rho_cases':rho_cases,'Abel_cases':abel_cases,
                                     'maximum_grouping_error':maximum_error,
                                     'scope':'Algebraic regressions; sample profiles do not establish actual asymptotic cancellation.'}
result['status'] = 'PASS: exact rational budgets and finite regressions; read REVIEW.md for universal proofs and limits'
print(json.dumps(result,indent=2))
