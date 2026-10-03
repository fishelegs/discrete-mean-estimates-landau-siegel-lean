"""Exact symbolic checks of the claimed interior and boundary constants."""
import json
from pathlib import Path
import sympy as s

n,r,k=s.symbols('n r k',real=True)
pi=s.pi
P=n*(n-s.Rational(1,2))*(n-s.Rational(9,4))*(n-s.Rational(11,4))
out={}
for name,den,constant in [('L2',n**2,s.Rational(9,64)),
                           ('H1',n**4,s.Rational(5,288))]:
    diff=s.expand(P-constant*den)
    finite=[s.factor(diff.subs(n,j)) for j in [1,2,3]]
    assert all(x>=0 for x in finite)
    tails={}
    for name2,arg in [('positive_tail',r+4),('negative_tail',-r-1)]:
        polynomial=s.Poly(diff.subs(n,arg),r)
        assert all(x>0 for x in polynomial.all_coeffs())
        tails[name2]=str(polynomial.as_expr())
    out[name]={'finite_differences':list(map(str,finite)),**tails}

a,b=pi/2,9*pi/4
z=a+b
w=[a*s.exp(s.I*b)/(b*(b-a)),-b*s.exp(s.I*a)/(a*(b-a)),z/(a*b)]
C=s.simplify(s.expand_complex(sum(w)+s.conjugate(sum(w))))
K=s.simplify(C*9*pi*pi/64)
assert s.simplify(K-pi*(77+2*s.sqrt(2))/112)==0
out['interior_C']=str(C)
out['interior_L2_bound']=str(K)
T=a*b+a*z+b*z
R=a*b*z
imW=s.simplify(s.expand_complex(s.im(sum(w))))
assert T==139*pi*pi/16
assert s.simplify(R*imW-11*pi*pi*(2*s.sqrt(2)-81)/112)==0

# Differentiate the quartic on each fixed boundary null frequency.
v1,v2,ep,mu=s.symbols('v1 v2 ep mu',real=True)
quartic=mu*(mu-pi*(1+ep*v1))*(mu-pi*(k+ep*v2))*(mu-pi*(k+1+ep*(v1+v2)))
variation=[]
for m in [1,k,k+1]:
    variation.append(s.factor(2*s.diff(quartic,ep).subs({ep:0,mu:pi*m})/(pi*m)**2))
expected=[-2*pi*pi*v1*k*(k-1),2*pi*pi*v2*(k-1)/k,
          -2*pi*pi*(v1+v2)*k/(k+1)]
assert all(s.simplify(x-y)==0 for x,y in zip(variation,expected))
out['boundary_derivative_divided_by_C0']=list(map(str,variation))
d=s.Rational(1,250)
for kval,target in [(3,16000/(3*pi)+152*pi/1125),
                    (4,16000/(3*pi)+232*pi/1125)]:
    aa,bb=pi,kval*pi
    zz=aa+bb
    ww=[aa*s.exp(s.I*bb)/(bb*(bb-aa)),
        -bb*s.exp(s.I*aa)/(aa*(bb-aa)),zz/(aa*bb)]
    CC=s.simplify(2*s.re(sum(ww)))
    TT=aa*bb+aa*zz+bb*zz
    RR=aa*bb*zz
    norm=s.simplify(CC*(4/d+TT*d/3)-RR*s.im(sum(ww))*d*d/4)
    assert s.simplify(norm-target)==0
    beta=[s.simplify(x.subs({k:kval,v1:-(2*kval+1),v2:kval})*CC*pi/(pi*pi))
          for x in variation]
    expected_beta=[448,s.Rational(64,3),32] if kval==3 else [1152,32,s.Rational(128,3)]
    assert beta==expected_beta
    out['boundary_'+str(kval)]={'C0':str(CC),'target_norm':str(norm),
                               'beta_Lminus8_coefficients_divided_by_c_pi2':list(map(str,beta))}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: all-integer interior bounds, target constants, and general null-mode beta derivative')
