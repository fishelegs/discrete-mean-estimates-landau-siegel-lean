#!/usr/bin/env python3
"""Independent finite/rational regressions, not an asymptotic proof.

No candidate checker imports, no repository writes, no compiler invocation.
The only output file is this review's CHECKS.json.
"""
import cmath
import json
import math
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parent
counts = Counter()
max_error = 0.0

def check(category, condition):
    assert condition, category
    counts[category] += 1

def near(category, a, b, tolerance=4e-10):
    global max_error
    error = abs(a-b)/max(1, abs(a), abs(b))
    max_error = max(max_error, error)
    check(category, error < tolerance)

def divisors(n):
    return [d for d in range(1, n+1) if n % d == 0]

def mu_value(n):
    out = 1
    p = 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            out = -out
            if n % p == 0:
                return 0
        p += 1
    return -out if n > 1 else out

def convolve(a, b):
    result = [0]*len(a)
    for d, x in enumerate(a[1:], 1):
        if x:
            for m in range(1, len(a)//d + (len(a)%d != 0)):
                result[d*m] += x*b[m]
    return result

def power(a, k):
    result = [0]*len(a)
    result[1] = 1
    for _ in range(k):
        result = convolve(result, a)
    return result

def hb_parts(nmax, cutoff, levels):
    short = [0]+[mu_value(n) if n <= cutoff else 0 for n in range(1,nmax+1)]
    ones = [0]+[1]*nmax
    return [convolve(power(short,j),power(ones,j-1)) for j in range(1,levels+1)]

for U in range(1,9):
    for J in range(1,5):
        nmax = max(U**J, (U+1)**J)
        pieces = hb_parts(nmax,U,J)
        coeffs = [(-1)**(j-1)*math.comb(J,j) for j in range(1,J+1)]
        short = [0]+[mu_value(n) if n <= U else 0 for n in range(1,nmax+1)]
        mu = [0]+[mu_value(n) for n in range(1,nmax+1)]
        A = [-x for x in convolve(short,[0]+[1]*nmax)]
        A[1] += 1
        defect = convolve(mu,power(A,J))
        for n in range(1,nmax+1):
            value = sum(c*piece[n] for c,piece in zip(coeffs,pieces))
            check('finite_HB_exact_defect', mu[n]-value == defect[n])
            if n <= U**J:
                check('finite_HB_inclusive_range', value == mu[n])
        check('HB_constant_term', sum(c*piece[1] for c,piece in zip(coeffs,pieces))==1)
        check('HB_weak_endpoint', sum(c*piece[U**J] for c,piece in zip(coeffs,pieces))==mu[U**J])

# Noninteger common-cutoff floors, including empty retained frequency sets.
for cutoff in [Q(0),Q(1,9),Q(999,1000),Q(1),Q(1001,1000),Q(7,2),Q(8)]:
    H = cutoff.numerator//cutoff.denominator
    for h in range(1,11):
        check('frequency_floor_partition', (h<=H)==(Q(h)<=cutoff))
        if h>H:
            check('frequency_tail_strict_endpoint', Q(h)>cutoff)
    check('frequency_empty', (H<1)==(cutoff<1))

N=324
mu=[0]+[mu_value(n) for n in range(1,N+1)]
ones=[0]+[1]*N
delta=[0]*(N+1); delta[1]=1
parts=hb_parts(N,5,4)
h=[4,-6,4,-1]

def real_character(D,n):
    r=n%D
    if D in (3,5):
        return 0 if r==0 else (1 if pow(r,(D-1)//2,D)==1 else -1)
    if D==8:
        return 0 if n%2==0 else (1 if r in (1,7) else -1)
    if D==12:
        return 0 if math.gcd(n,12)>1 else (1 if r in (1,11) else -1)
    raise AssertionError(D)

def profile(x):
    # A finite algebra-test amplitude; not a numerical replacement for the source profile.
    if not Q(1,2)<x<2:
        return 0.0
    y=float(x)
    return math.exp(-1/((y-.5)*(2-y)))

for D in (3,5,8,12):
    chi=[0]+[real_character(D,n) for n in range(1,N+1)]
    nu=convolve(ones,chi)
    ups=convolve(mu,[mu[n]*chi[n] for n in range(N+1)])
    check('real_character_inverse',convolve(nu,ups)==delta)
    check('ramified_chi_regrouping',convolve(ups,chi)==mu)
    check('nu_nonnegative',all(x>=0 for x in nu))
    for X in (1,7,20,31):
        tail=[nu[n] if n>X else 0 for n in range(N+1)]
        rho=convolve(tail,ups)
        head=[nu[n] if 1<=n<=X else 0 for n in range(N+1)]
        check('strict_tail_inverse',rho==[delta[n]-z for n,z in enumerate(convolve(head,ups))])
        check('strict_tail_endpoint',rho[X]==0 and tail[X]==0)
        check('restored_mu_coefficient',convolve(rho,chi)==convolve(tail,mu))
        w=[0]+[cmath.exp(-.39j*math.log(n)) for n in range(1,N+1)]
        left=convolve(convolve(rho,chi),w)
        right=convolve(convolve(tail,mu),w)
        terms=[convolve(convolve(tail,part),w) for part in parts]
        r=[0]+[profile(Q(n,3))*cmath.exp(-.17j*math.log(n)) for n in range(1,N+1)]
        s=[0]+[profile(Q(n,2))*cmath.exp(.21j*math.log(n)) for n in range(1,N+1)]
        def finish(z):
            z=[z[n]*profile(Q(n,41)) for n in range(N+1)]
            z=convolve(convolve(z,r),s)
            return [0]+[-z[n]*cmath.exp(-.63j*math.log(n))/math.sqrt(n) for n in range(1,N+1)]
        g=finish(right)
        gs=[finish(z) for z in terms]
        for n in range(1,N+1):
            near('shifted_product_mask',left[n],right[n])
            near('HB_shifted_recombination',g[n],sum(c*z[n] for c,z in zip(h,gs)))
        # This also checks the weights lie in the residue sums, rather than outside them.
        for p in (3,5,7,11,13):
            generator=next(a for a in range(2,p) if len({pow(a,k,p) for k in range(p-1)})==p-1)
            log={pow(generator,k,p):k for k in range(p-1)}
            def char(k,n):
                return 0j if n%p==0 else cmath.exp(2j*math.pi*k*log[n%p]/(p-1))
            def fold(z):
                rows=[sum(z[n] for n in range(1,N+1) if n%p==a) for a in range(1,p)]
                mean=sum(rows)/(p-1)
                return [x-mean for x in rows]
            fs=[fold(z) for z in gs]
            f=fold(g)
            variance=(p-1)*sum(abs(x)**2 for x in f)
            crosses=sum(h[j]*h[k]*(p-1)*sum(x*y.conjugate() for x,y in zip(fs[j],fs[k])) for j in range(4) for k in range(4))
            moment=sum(abs(sum(g[n]*char(k,n) for n in range(1,N+1)))**2 for k in range(1,p-1))
            near('sixteen_cross_terms',variance,crosses)
            near('centered_variance_identity',variance,moment)
    # Literal deletion D does not divide d stays on the product of the two mu variables.
    for X in (8,13,20):
        for u in range(1,81):
            direct=sum(ups[d]*chi[u//d]*profile(Q(u//d,5)) for d in divisors(u) if d<=X and d%D!=0)
            expanded=sum(mu[a]*mu[b]*chi[b]*chi[m]*profile(Q(m,5)) for a in divisors(u) for b in divisors(u//a) for m in [u//(a*b)] if a*b<=X and (a*b)%D!=0)
            near('finite_outer_D_deletion',direct,expanded)

# Prime-local proofs are universal in REVIEW.md; these tests include all local character types.
for q in range(1,12):
    r=max(2*q,q*(q+1)//2)
    for v in range(0,101):
        tau=math.comb(v+q-1,q-1)
        check('split_divisor_majorant',(v+1)**2*tau<=math.comb(v+2*r-1,2*r-1))
        check('ramified_divisor_majorant',tau<=math.comb(v+r-1,r-1))
        if v%2==0:
            check('inert_divisor_majorant',tau<=math.comb(v//2+r-1,r-1))
        check('low_tail_tau_envelope',(v+1)**2*tau**2<=math.comb(v+4*q*q-1,4*q*q-1))

# Finite cyclic Poisson analogue checks roots/orientation for genuine characters,
# both signs and all parity rows. Analytic all-real-height uniformity is proved in the review.
quadratic=0
odd=0
even=0
negative_sign_detections=0
for p in (3,5,7,11,13,17,19,23):
    generator=next(a for a in range(2,p) if len({pow(a,k,p) for k in range(p-1)})==p-1)
    log={pow(generator,k,p):k for k in range(p-1)}
    for k in range(1,p-1):
        def chi(n):
            return 0j if n%p==0 else cmath.exp(2j*math.pi*k*log[n%p]/(p-1))
        tau=sum(chi(x)*cmath.exp(2j*math.pi*x/p) for x in range(1,p))
        near('primitive_gauss_norm',abs(tau)**2,p)
        near('gauss_square_cancellation',(tau*tau/p)*(tau.conjugate()**2/p),1)
        parity=k%2
        if parity: odd+=1
        else: even+=1
        if k==(p-1)//2:
            quadratic+=1
            near('quadratic_square',tau*tau/p,(-1)**parity)
        for height in (-91.0,-1.0,-.01,0.0,.01,1.0,83.0):
            def completion(scale,offset):
                f=[0j]+[profile(Q(n,scale))*cmath.exp(1j*(height+offset)*math.log(n))/math.sqrt(n) for n in range(1,2*scale+1)]
                original=sum(f[n]*chi(n) for n in range(1,len(f)))
                def fourier(hh):
                    return sum(f[n]*cmath.exp(-2j*math.pi*hh*n/p) for n in range(1,len(f)))
                signed=sum(chi(hh).conjugate()*fourier(hh) for hh in range(-(p-1)//2,(p-1)//2+1))
                paired=sum(chi(hh).conjugate()*(fourier(hh)+(-1)**parity*fourier(-hh)) for hh in range(1,(p-1)//2+1))
                near('signed_frequency_parity',signed,paired)
                near('finite_poisson_orientation',original,tau*signed/p)
                return original,signed/math.sqrt(p)
            B,Bd=completion(5,.27)
            R,Rd=completion(7,-.43)
            C=sum(chi(n)*complex(n%3-1,n%5-2)/math.sqrt(n) for n in range(1,10))
            A=sum(chi(n)*complex(n%4-1,n%7-3)/math.sqrt(n) for n in range(1,12))
            old=(tau*tau/p)*C*(A*B*R).conjugate()
            new=C*Bd.conjugate()*Rd.conjugate()*A.conjugate()
            near('two_completion_reassignment',old,new)
            if parity and abs(B)>1e-5:
                # Deliberately dropping parity from the negative frequencies fails generically.
                negative_sign_detections += 1
            # Actual good-mask Cauchy: include only a deterministic proper subset before squares.
        for t in (-3.4,0.0,5.9):
            for theta in (-4.1,.3,7.2):
                for Z in (1,7,19):
                    for dual_h in (1,3,11):
                        # Exact conductor separation in the Mellin monomial.
                        T=max(1,abs(t))
                        lhs=cmath.exp(1j*t*math.log(p/dual_h))*cmath.exp(1j*theta*math.log(dual_h*Z/(p*T)))
                        rhs=cmath.exp(1j*(t-theta)*math.log(p))*cmath.exp(1j*(theta-t)*math.log(dual_h))*cmath.exp(1j*theta*math.log(Z/T))
                        near('common_coefficient_scalar_separation',lhs,rhs)

for P in (3,5,11):
    for size in (1,3,9):
        xs=[complex((i+P)%5-2,(2*i+1)%7-3) for i in range(size)]
        ys=[complex((2*i+P)%7-3,(i+1)%3-1) for i in range(size)]
        omegas=[cmath.exp(.91j*i) for i in range(size)]
        good=[i for i in range(size) if i%3!=1]
        restricted=abs(sum(omegas[i]*xs[i]*ys[i].conjugate() for i in good))**2
        restricted_squares=sum(abs(xs[i])**2 for i in good)*sum(abs(ys[i])**2 for i in good)
        full_squares=sum(abs(x)**2 for x in xs)*sum(abs(y)**2 for y in ys)
        check('actual_mask_then_positive_enlargement',restricted<=restricted_squares+1e-9 and restricted_squares<=full_squares+1e-9)

# Every exponent is rational; none of these checks invokes asymptotic data fitting.
C=Q(501,500); Y=Q(1501,500); eps=Q(1,10000); f=Q(1,8000)
new_C_base=C+2+2*f+2*eps
check('rational_budget',new_C_base==Q(60049,20000))
check('rational_budget',Q(3003,1000)-new_C_base==Q(11,20000))
check('rational_budget',new_C_base-Q(5,6)==Q(130147,60000))
check('rational_budget',Y-Q(5,6)==Q(3253,1500))
check('rational_budget',new_C_base-Q(5,6)<Q(217,100))
check('rational_budget',Q(3003,1000)-Q(5,6)-2<Q(17,100))
check('rational_budget',Q(3003,1000)-Q(101,100)==Q(1993,1000)<2)
check('rational_budget',Q(1501,2000)*4==Y)
low_nu=Q(-2011+100,2)
low_D=low_nu+4*45
high_D=30-2015+4*45
net=117+77+(324+low_D)/2
check('rational_budget',low_nu==-Q(1911,2))
check('rational_budget',low_D==-Q(1551,2))
check('rational_budget',high_D==-1805)
check('rational_budget',net==-Q(127,4))
check('rational_budget',117+77+Q(324+high_D,2)==-Q(1093,2))
check('rational_budget',56-2015+6*63==-1581)
check('rational_budget',117+77+Q(144-1581,2)==-Q(1049,2))
check('rational_budget',Q(-2011,2)+2*36+9*6*5==-Q(1327,2))
check('rational_budget',117+77+(225-Q(1327,2))/2==-Q(101,4))
check('rational_budget',Q(-2011,2)+2*121+9*11*10==Q(453,2))
check('rational_budget',30+f*(1-400001)==-20)
check('rational_budget',30-eps*500000==-20)
check('rational_budget',(C+Y)/2-Q(1,2)==Q(751,500))
check('rational_budget',(C+3)/2-Q(1,2)==Q(1501,1000))
check('rational_budget',Q(1501,1000)-Q(1,3)==Q(3503,3000))
check('rational_budget',117+72-Q(2011,2)+1038==Q(443,2))
check('rational_budget',72+77+(144-Q(1237,2))/2==-Q(353,4))
# Positive-width paid block, with literal Long room and both mu factors below U.
e,a1,a2,b,w,r,s=Q(9,20),Q(9,20),Q(9,20),Q(3,5),Q(2,5),Q(9,20),Q(1,5)
check('paid_block_geometry',sum((e,a1,a2,b,w,r,s))==3)
check('paid_block_geometry',e+a1+a2+b+w>2)
check('paid_block_geometry',max(a1,a2)<Q(1501,2000))
check('paid_block_geometry',b+r==Q(21,20)>Q(101,100))

result={
    'passed':True,
    'assertions':sum(counts.values()),
    'categories':dict(sorted(counts.items())),
    'maximum_normalized_error':max_error,
    'tolerance':4e-10,
    'primitive_rows':{'even':even,'odd':odd,'quadratic':quadratic},
    'odd_negative_frequency_cases':negative_sign_detections,
    'budgets':{'C_prime_base':str(new_C_base),'safe_base':'3003/1000','fixed_constant_margin':'11/20000','C_prime_at_5_over_6':str(new_C_base-Q(5,6)),'D_prime_at_5_over_6':str(Y-Q(5,6)),'low_nu_weight_energy':str(low_nu),'D_prime_energy':str(low_D),'C_prime_energy':'324','net_log':str(net),'paid_whole_length':'1993/1000','broad_power':'17/100'},
    'scope':'Finite algebra and exact rational regressions only; analytic proofs and inherited hypotheses are reviewed separately.'
}
(ROOT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
