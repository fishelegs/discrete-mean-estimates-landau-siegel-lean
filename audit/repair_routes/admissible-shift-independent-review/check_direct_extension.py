"""Independent exact certificate: integrate the exponential energy directly.

No import from the proposed derivation and no use of its boundary-flux formula.
Run with Python 3 + SymPy; all equalities use rational function arithmetic.
"""
import json
from pathlib import Path
import sympy as s

a, b, u, v = s.symbols('a b u v', nonzero=True)
I = s.I
z = a+b
A, T, R = 2*z, a*b+a*z+b*z, a*b*z
lam = [s.S.Zero, a, b, z]
phase = [s.S.One, 1/u, 1/v, 1/(u*v)]

def bar(x):
    return s.cancel(s.conjugate(x).subs({s.conjugate(a):a,
        s.conjugate(b):b, s.conjugate(u):1/u, s.conjugate(v):1/v}))

def adj(m):
    return m.applyfunc(bar).T

def clean(m):
    return m.applyfunc(s.cancel)

w = [a*v/(b*(b-a)), -b*u/(a*(b-a)), z/(a*b)]
C = s.factor(sum(w)+sum(map(bar,w)))
X = -w[0]*b*z-w[1]*a*z-w[2]*a*b
V = ((w[0]-bar(w[0]))*b+(w[1]-bar(w[1]))*a)/(2*I)
imW = (sum(w)-sum(map(bar,w)))/(2*I)
D = I*(u*v-1-z*(v-u)/(b-a))

# Rows are conjugated coefficient indices, columns un-conjugated ones.
# Integrate exp(-i*(lambda_col-lambda_row)*s) on the added unit interval.
Gram = s.zeros(4)
for r, k in enumerate(lam):
    for c, j in enumerate(lam):
        integrand = j*j*k*k-A*j*k*(j+k)/2+T*j*k-R*(j+k)/2
        integral = 1 if r==c else (phase[c]/phase[r]-1)/(-I*(j-k))
        Gram[r,c] = s.factor(integrand*integral)
assert clean(Gram-adj(Gram)) == s.zeros(4)
assert all(Gram[j,j] == 0 for j in range(4))

# Endpoint conditions in order U(0), U'(0), U(1), U'(1),
# where this coordinate is the ADDED interval, and data are (h0,h1,M).
H = s.Matrix([[1]*4, [-I*j for j in lam], phase,
              [-I*j*q for j,q in zip(lam,phase)]])
rhs = s.Matrix([[0,0,0], [0,-1,0], [0,0,1], [-1,0,0]])
sol = clean(H.inv()*rhs)
assert clean(H*sol-rhs) == s.zeros(4,3)
det_check = s.cancel(H.det()-a*b*(a-b)*C/(u*v))
assert det_check == 0
extension = clean(adj(sol)*Gram*sol)

# Encode the reported boundary form directly as a quadratic matrix.
B = s.Matrix([[-2*V,bar(D),bar(X)],
              [D,-2*V,X],
              [X,bar(X),-R*imW]])
checks=[]
for r in range(3):
    for c in range(3):
        difference=s.cancel(C*extension[r,c]-B[r,c])
        assert difference==0,(r,c,difference)
        checks.append([r,c])
        print('direct exponential integration entry',r,c,'PASS',flush=True)

result={'identity':'C times direct added-interval energy equals B',
        'all_parameter_rational_identity':True,
        'matrix_entries_checked':checks,
        'determinant_checked':str(a*b*(a-b)*C/(u*v)),
        'assumptions':'a,b real; u,v unit phases; a*b*(b-a)*C nonzero',
        'proof_scope':'Algebraic extension identity, not actual arithmetic mean attachment'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: exact all-parameter extension by direct integration')
