"""Independent exact Green identity for the literal triangular profile.

The uniform analytic error bounds are a separate source proof.
"""
from pathlib import Path
import json
import sympy as s

v,t=s.symbols('v t',real=True)
ell=s.symbols('ell',nonzero=True)
a,m,b=s.Rational(1,2),s.Rational(251,500),s.Rational(63,125)
left=500*(v-a);right=500*(b-v)
K=(v-t)*s.exp(ell*(v-t))
densities=[2*ell*s.diff(f,v)+ell**2*f for f in [left,right]]
atoms=[(a,s.Integer(500)),(m,s.Integer(-1000)),(b,s.Integer(500))]

def piece(density,lo,hi):
    return s.integrate(s.expand(density*(v-t))*s.exp(ell*(v-t)),(v,lo,hi))
tests=[]
for region in range(4):
    if region==0:
        value=piece(densities[0],a,m)+piece(densities[1],m,b)
        chosen=atoms;expected=0
    elif region==1:
        value=piece(densities[0],t,m)+piece(densities[1],m,b)
        chosen=atoms[1:];expected=500*(t-a)
    elif region==2:
        value=piece(densities[1],t,b)
        chosen=atoms[2:];expected=500*(b-t)
    else:
        value=0;chosen=[];expected=0
    value+=sum(weight*K.subs(v,point) for point,weight in chosen)
    difference=s.simplify(s.expand(value-expected))
    assert difference==0,(region,difference)
    tests.append({'region':region,'status':'exact identity'})
assert s.simplify(K.subs(v,t))==0
checks={'status':'PASS','four_regions':tests,'endpoint_atom_kernel_is_zero':True,
        'ell':'arbitrary nonzero complex symbolic parameter','includes_three_literal_jump_atoms':True,
        'not_a_Lean_or_asymptotic_certificate':True}
Path(__file__).with_name('ATOMIC_RAMP_CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks,indent=2))
