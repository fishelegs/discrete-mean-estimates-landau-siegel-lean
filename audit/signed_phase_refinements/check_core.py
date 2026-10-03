"""Independent exact algebra/provenance checks, not analytic or Lean certification."""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import subprocess

OUT = Path(__file__).resolve().parent
REPO = Path(__file__).resolve().parents[2]
checks = {}
details = {}

def check(name, condition):
    checks[name] = bool(condition)
    assert checks[name], name

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

# Coefficients of delta_j/alpha in the indeterminate u=c*alpha*L.
d1, d2, d3 = (F(1), F(-5)), (F(2), F(2)), (F(3), F(-3))
check('original_finite_D_shift_identity', tuple(a+b for a,b in zip(d1,d2)) == d3)
check('branch_shift_cancellation', all(a+b-(a+b+c)/2 == 0 for a,b,c in zip(d1,d2,d3)))
check('all_four_parities', all(F(3-4*a-2*b,4)+F(2*a+b,2)-F(3,4) == 0
                              for a in (0,1) for b in (0,1)))
check('gauss_phase_identity', all((2*j-j) % 4 == j for j in (0,1)))
def gadd(z,w):
    return (z[0]+w[0],z[1]+w[1])

def gmul(z,w):
    return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])

def gconj(z):
    return (z[0],-z[1])

# Re(-i(x+iy))=y in exact Gaussian-integer arithmetic.
check('real_part_sign', all(gmul((0,-1),(x,y))[0] == y
                            for x in range(-3,4) for y in range(-3,4)))
check('branch_global_sign_invariance', F((-1)**3,-1) == 1)

k = F(1,1000)
check('constant_length_margin', 64**3 <= 2**20)
check('dual_length_exponent', 2-2*k+3*k/8 == 2-F(13,8)*k < 2)
check('direct_length_exponent', 2-2*k < 2-F(13,8)*k)
check('profile_width', F(201,400)-F(251,500) == F(1,2000))
check('energy_exponents', (9*6**2,9*2**2,9*8**2) == (324,36,576))
check('absolute_core_budget', 77+F(324,2)+F(36,2)+36 == 293)
check('stationary_and_scalar_payment', 293-519 == -226)
check('upstream_sparse_payment', 77+F(324,2)-F(1723,4)+36 == -F(623,4))
check('mixed4_per_box', F(77+576-739,2) == -43)
check('mixed4_all_boxes', F(77+576-739,2)+36 == -7)
check('mixed_mass_threshold', 739-2*36 == 667)
# Formal normalization algebra with r representing sqrt(pi); the Gaussian
# integral itself is an analytic input, not certified by this check.
check('gaussian_mass_constant', all((r/w)*(2*w*r)/(2*r*r) == 1
    for r in (F(1,2),F(3,2),F(5,3)) for w in (F(1),F(7,3),F(9))))
principal_J = 100
principal_decay = F(251,500)*(principal_J-F(1,2))
check('principal_concrete_margin', principal_decay > 21)
check('principal_fixed_factor_budget', 5*2+1-21 == -10)
details['principal_J100_decay_before_P_o1_cost'] = str(principal_decay)
# The permitted geometry really need not make the product length <=P^2.
example_C = F(201,400)+3-F(2009,4000)-2*F(3,5)
example_D = F(9,5)
check('legal_leading_scale_example', example_C < 2-2*k and example_D < 2-2*k)
check('example_mixed_product_exceeds_sieve_length', example_C+example_D > 2)
details['example_product_leading_exponent'] = str(example_C+example_D)

# Integer cyclotomic arithmetic. Lists are coefficients in ascending degree.
def trim(p):
    p = list(p)
    while len(p)>1 and p[-1] == 0:
        p.pop()
    return p

def divmod_monic(a,b):
    a, b = trim(a), trim(b)
    assert b[-1] == 1
    q = [0]*max(1,len(a)-len(b)+1)
    while a != [0] and len(a)>=len(b):
        degree, coefficient = len(a)-len(b), a[-1]
        q[degree] += coefficient
        for i,v in enumerate(b):
            a[i+degree] -= coefficient*v
        a=trim(a)
    return trim(q),a

@lru_cache(None)
def cyclotomic(n):
    poly=[-1]+[0]*(n-1)+[1]
    for d in range(1,n):
        if n%d == 0:
            poly,rem=divmod_monic(poly,cyclotomic(d))
            assert rem == [0]
    return tuple(poly)

def primitive_root(p):
    for g in range(2,p):
        if len({pow(g,j,p) for j in range(p-1)}) == p-1:
            return g
    raise AssertionError(p)

def charsum_coeff(p,logs,l,n,indices):
    poly=[0]*(p-1)
    if l%p and n%p:
        delta=(logs[l%p]-logs[n%p])%(p-1)
        for m in indices:
            poly[(m*delta)%(p-1)] += 1
    return poly

def equals_integer(poly,p,value):
    poly=list(poly)
    poly[0]-=value
    return divmod_monic(poly,cyclotomic(p-1))[1] == [0]

pairs=0
for p in (3,5,7,11,13,17,19):
    g=primitive_root(p)
    logs={pow(g,j,p):j for j in range(p-1)}
    for l in range(1,2*p+2):
        for n in range(1,2*p+2):
            unit = int(l%p != 0 and n%p != 0)
            eq = int((l-n)%p == 0)
            neg = int((l+n)%p == 0)
            all_value = unit*((p-1)*eq-1)
            even_value = unit*((p-1)//2*(eq+neg)-1)
            odd_value = unit*((p-1)//2*(eq-neg))
            all_poly=charsum_coeff(p,logs,l,n,range(1,p-1))
            even_poly=charsum_coeff(p,logs,l,n,range(2,p-1,2))
            odd_poly=charsum_coeff(p,logs,l,n,range(1,p-1,2))
            assert equals_integer(all_poly,p,all_value)
            assert equals_integer(even_poly,p,even_value)
            assert equals_integer(odd_poly,p,odd_value)
            assert even_value+odd_value == all_value
            diagonal=unit*(p-1)*int(l==n)
            off=unit*(p-1)*int(l!=n and (l-n)%p==0)
            assert diagonal+off-unit == all_value
            pairs+=1
check('exact_primitive_orthogonality_and_two_parities', True)
check('exact_diagonal_off_principal_split', True)
details['cyclotomic_prime_list']=[3,5,7,11,13,17,19]
details['cyclotomic_pairs_checked']=pairs

# A symbolic p-unit identity relevant to the principal A=M H factorization.
check('principal_multiplicativity_above_p', all(
    int((d*m)%p != 0) == int(d%p != 0)*int(m%p != 0)
    for p in (3,5,7,11) for d in range(1,2*p+1) for m in range(1,2*p+1)))

# Exact finite conjugation check with a real character including ramification
# and a completely multiplicative unit phase. This is an algebra test only.
def omega(n):
    count,d=0,2
    while d*d<=n:
        while n%d == 0:
            count+=1
            n//=d
        d+=1
    return count+int(n>1)

def phase(n):
    return ((1,0),(0,1),(-1,0),(0,-1))[omega(n)%4]

def chi5(n):
    return {0:0,1:1,2:-1,3:-1,4:1}[n%5]

def finite_convolution(n,conjugate_phase=False):
    result=(0,0)
    for z in range(1,n+1):
        if n%z == 0:
            value=phase(n//z)
            if conjugate_phase:
                value=gconj(value)
            result=gadd(result,gmul((chi5(z),0),value))
    return result

check('opposite_shift_conjugation_with_ramification', all(
    finite_convolution(n,True) == gconj(finite_convolution(n,False))
    for n in range(1,301)))
check('ramified_local_collapse', all(
    finite_convolution(5**j,True) == gconj(phase(5**j)) for j in range(5)))


print(json.dumps({'all_passed':all(checks.values()),'check_groups':len(checks),'checks':checks,'details':details,'cyclotomic_pairs_checked':pairs,'scope':'Exact finite arithmetic only; not an analytic or Lean proof.'},indent=2))
