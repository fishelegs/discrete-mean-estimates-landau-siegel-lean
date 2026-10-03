#!/usr/bin/env python3
"""Independent finite algebra and rational-budget regressions; no Lean invocation."""
from fractions import Fraction as F
from math import comb, pi, sqrt
import cmath, json

checks = {}

def save(name, value):
    checks[name] = value

def need(test, label):
    if not test:
        raise AssertionError(label)

def fstr(x):
    x = F(x)
    return f"{x.numerator}/{x.denominator}"

# Exact support and normalization exponents.
profile_lo, profile_hi = F(251,500), F(201,400)
need(profile_hi-profile_lo == F(1,2000), 'fixed profile width')
base_c = 1+profile_hi-profile_lo
base_y = 3+profile_hi-profile_lo
shell, height, conductor = F(1,8000), F(1,10000), F(1,1000)
c_paid = base_c+shell+height+conductor
y_paid = base_y+conductor
C, Y = F(501,500), F(1501,500)
need(c_paid<C<2, 'finite completed length')
need(y_paid<Y<4, 'whole uncompleted length')
principal_exponent = (C+Y)/2-2-profile_lo
need(principal_exponent == F(-1,2), 'principal row exponent')
need(F(1,2)-F(49,100)==F(1,100), 'principal D/log absorption')
save('profile_and_one_completion', {
    'profile_width':fstr(profile_hi-profile_lo),
    'C_paid_exponent':fstr(c_paid), 'C_envelope_exponent':fstr(C),
    'C_margin':fstr(C-c_paid),
    'Y_paid_exponent':fstr(y_paid), 'Y_envelope_exponent':fstr(Y),
    'Y_margin':fstr(Y-y_paid),
    'natural_sieve_loss':fstr((Y-2)/2),
    'principal_preabsorption_exponent':fstr(principal_exponent),
    'principal_claimed_exponent':fstr(F(-49,100)),
})

rows=[]
for completed in range(4):
    q=6-completed
    r=9*q*(q+1)//2
    low=F(-1997,2)+8*q*q
    high=2*r-2015
    need(high<low, f'high sparse exponent q={q}')
    ED=low+9*q*(q-1)
    EC=9*(completed+3)**2
    total=149+(EC+ED)/2
    want=[F(-123,4),F(-353,4),F(-479,4),F(-501,4)][completed]
    need(total==want, f'whole logarithmic budget r={completed}')
    rows.append({'completed':completed,'q':q,'nu_convolution_order':r,
                 'rho_low_exponent':fstr(low),'rho_high_exponent':str(high),
                 'D_energy_exponent':fstr(ED),'C_energy_exponent':str(EC),
                 'normalized_log_exponent':fstr(total)})
    # These regressions supplement the universal combinatorial proof.
    for j in range(501):
        tq=lambda e: comb(e+q-1,q-1)
        need((j+1)**4*tq(j)<=comb(j+2*r-1,2*r-1), f'split {q},{j}')
        need((j+1)**2*tq(j)<=comb(j+r-1,r-1), f'ramified {q},{j}')
        need((2*j+1)**2*tq(2*j)<=comb(j+r-1,r-1), f'inert {q},{j}')
        need(tq(2*j)<=comb(j+q*(q+1)//2-1,q*(q+1)//2-1), f'pairing {q},{j}')
save('energy_budgets',rows)
save('local_inequality_regressions',{'q_values':[3,4,5,6],'exponents_in_each_case':501,'passed':True})

zero=F(0)
def delta1(k): return F(501,1000)
def delta2(k): return max(zero,F(103,1000)+F(2,5)*k)/2+max(zero,F(-112,125)+F(2,5)*k)/2
def delta3(k): return max(zero,F(-663,1000)+F(2,3)*k)
bs=[F(99,100),F(1989,2000),F(4287,2800),F(56,25),F(359,160),F(301,100)]
need(delta3(bs[1])==0,'zero boundary')
need(delta2(bs[2])==delta3(bs[2]),'three/two crossing')
need(F(-112,125)+F(2,5)*bs[3]==0,'two-length crossing')
need(delta2(bs[4])==delta1(bs[4]),'two/one crossing')
forms=[lambda k:F(0), lambda k:F(-663,1000)+F(2,3)*k,
       lambda k:F(103,2000)+k/5,lambda k:F(-793,2000)+F(2,5)*k,lambda k:F(501,1000)]
for a,b,form in zip(bs,bs[1:],forms):
    for j in range(101):
        k=a+(b-a)*F(j,100)
        need(form(k)==min(delta1(k),delta2(k),delta3(k)),f'piecewise minimum {k}')
subrange = F(1337,1000)+F(2,3)*F(497,500)
need(subrange==F(5999,3000)<2,'paid high-label subrange')
save('piecewise_minimum',{'breakpoints':[fstr(x) for x in bs],
      'checked_rational_points':505,'worst_loss':fstr(F(501,1000)),
      'paid_subrange_K_exponent':fstr(F(497,500)),
      'paid_subrange_length_exponent':fstr(subrange)})

# Genuine characters for odd prime moduli.
def primitive_root(p):
    for g in range(2,p):
        if len({pow(g,k,p) for k in range(p-1)})==p-1:
            return g
    raise ValueError(p)

maxerr=0.0
kernel_cases=projection_cases=partition_cases=saturation_cases=0
prime_results=[]
for p in [5,7,11,13,17,19,23,29,31]:
    g=primitive_root(p)
    inds={pow(g,k,p):k for k in range(p-1)}
    chars={r:{x:cmath.exp(2j*pi*r*inds[x]/(p-1)) for x in range(1,p)} for r in range(p-1)}
    tau={r:sum(chars[r][x]*cmath.exp(2j*pi*x/p) for x in range(1,p)) for r in range(p-1)}
    need(abs(tau[0]+1)<1e-10,'principal tau=-1')
    for r in range(1,p-1):
        need(abs(abs(tau[r])-sqrt(p))<1e-10,'primitive Gauss magnitude')
    qr=(p-1)//2
    need(abs(tau[qr]**2/p-(-1)**qr)<1e-10,'quadratic retained')
    kl={z:sum(cmath.exp(2j*pi*(x+z*pow(x,-1,p))/p) for x in range(1,p)) for z in range(1,p)}
    for parity in [0,1]:
        family=[r for r in range(1,p-1) if r%2==parity]
        # A deliberately nontrivial finite mask; never asserted to be actual Psi1.
        good=[r for r in family if (r+p)%3!=0]
        bad=[r for r in family if r not in good]
        for c in range(1,p):
            for n in range(1,p):
                z=n*pow(c,-1,p)%p
                direct=sum(tau[r]**2/p*chars[r][c]*chars[r][n].conjugate() for r in family)
                formula=(p-1)/(2*p)*(kl[z]+(-1)**parity*kl[(-z)%p])-(1/p if parity==0 else 0)
                err=abs(direct-formula)
                maxerr=max(maxerr,err)
                need(err<1e-8,'squared Gauss kernel including negative principal correction')
                goodrow=sum(tau[r]**2/p*chars[r][c]*chars[r][n].conjugate() for r in good)
                badrow=sum(tau[r]**2/p*chars[r][c]*chars[r][n].conjugate() for r in bad)
                need(abs(goodrow-(formula-badrow))<1e-8,'exact good=full-bad')
                kernel_cases+=1
                partition_cases+=1
        # Matrix U(output y,input x), eigenbasis conjugate characters.
        residues=list(range(1,p))
        U=[[sum(tau[r]**2/p*chars[r][x]*chars[r][y].conjugate() for r in good)/(p-1)
            for x in residues] for y in residues]
        Q=[[sum(chars[r][x]*chars[r][y].conjugate() for r in good)/(p-1)
            for x in residues] for y in residues]
        for y in range(p-1):
            for x in range(p-1):
                err=abs(sum(U[y][z]*U[x][z].conjugate() for z in range(p-1))-Q[y][x])
                maxerr=max(maxerr,err)
                need(err<1e-8,'UU*=projection')
                projection_cases+=1
        if good:
            r=good[0]
            v=[chars[r][x].conjugate()/sqrt(p-1) for x in residues]
            omega=tau[r]**2/p
            uv=[sum(U[y][x]*v[x] for x in range(p-1)) for y in range(p-1)]
            need(max(abs(uv[i]-omega*v[i]) for i in range(p-1))<1e-8,'unit eigenvalue')
            pos=sum(uv[i]*(omega*v[i]).conjugate() for i in range(p-1))
            neg=sum(uv[i]*(-omega*v[i]).conjugate() for i in range(p-1))
            need(abs(pos-1)<1e-8 and abs(neg+1)<1e-8,'both real signs saturate')
            saturation_cases+=1
    prime_results.append({'p':p,'primitive_root':g,'quadratic_character_index':qr,'quadratic_parity':qr%2})
save('gauss_operator_regressions', {'primes':prime_results,'kernel_cases':kernel_cases,
    'good_bad_partition_cases':partition_cases,'projection_entries':projection_cases,
    'saturation_cases':saturation_cases,'max_floating_error':maxerr,
    'tolerance':1e-8,'principal_correction':'-1_even/p',
    'scope':'Finite character identities only; good masks are test masks, not exceptional families.'})

# Periodic primitive real characters and the exact discrete Abel inequality.
periodic={4:[0,1,0,-1],5:[0,1,-1,-1,1],8:[0,1,0,-1,0,-1,0,1],12:[0,1,0,0,0,-1,0,-1,0,0,0,1]}
abel_cases=0
for d,ch in periodic.items():
    need(sum(ch)==0, 'nonprincipal period sum')
    partial=0
    for n in range(1,8*d+1):
        partial+=ch[n%d]
        need(abs(partial)<=d,'periodic incomplete sum')
    for a in [1,7,13]:
        b=a+113
        weights=[cmath.exp(1j*(n**.5))/(n**.5)*(1+(n-a)*(b-n)/(b-a)**2) for n in range(a,b+1)]
        actual=sum(ch[n%d]*weights[n-a] for n in range(a,b+1))
        # Prefixes beginning at a have magnitude <=D by whole-period removal.
        budget=d*(abs(weights[-1])+sum(abs(weights[i]-weights[i+1]) for i in range(len(weights)-1)))
        need(abs(actual)<=budget+1e-10,'Abel variation bound')
        abel_cases+=1
save('periodic_principal_profile_regressions',{'conductors':list(periodic),'abel_cases':abel_cases,'passed':True})

save('status', 'PASS: finite/rational regressions only; source proof still requires independent review')
print(json.dumps(checks,indent=2))
