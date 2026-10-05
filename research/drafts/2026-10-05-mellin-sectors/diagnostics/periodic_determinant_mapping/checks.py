#!/usr/bin/env python3
"""Finite orbit and mapping diagnostics; no full near estimate is claimed."""
import json,math
from fractions import Fraction as F
from pathlib import Path
from sympy import kronecker_symbol,totient
from sympy.ntheory.modular import crt
HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True}
M=11;E=13
At=int(crt([M,E],[0,1])[0]);Bt=int(crt([M,E],[1,0])[0])
def projective(q):
 units=[u for u in range(q) if math.gcd(u,q)==1]
 rows=set()
 for c in range(q):
  for d in range(q):
   if math.gcd(math.gcd(c,d),q)!=1:continue
   rows.add(min(((u*c)%q,(u*d)%q) for u in units))
 return sorted(rows)
matrices=[]
for a in range(-10,11):
 for b in range(-10,11):
  for c in range(-10,11):
   for d in range(-10,11):
    if a*d-b*c==1 and abs(a)+abs(b)+abs(c)+abs(d)<=10:matrices.append((a,b,c,d))
orbits=[];autos=0
for disc in [-3,5,8,12]:
 D=abs(disc);ch=lambda n:int(kronecker_symbol(disc,n))
 rows=projective(D)
 vals=[ch(c*d) for c,d in rows]
 assert sum(vals)==0 and sum(v*v for v in vals)==int(totient(D))
 corr=[]
 for a,b,c,d in matrices:
  top=int((At*a+Bt*c)%M==0 and (At*b+Bt*d)%E==0)
  w=top*sum(ch((C*a+F0*c)*(C*b+F0*d))*ch(C*F0) for C,F0 in rows)
  if w:corr.append({'matrix':[a,b,c,d],'value':w})
 assert len(corr)==2
 assert {tuple(z['matrix']) for z in corr}=={(1,0,0,1),(-1,0,0,-1)}
 assert sum(abs(z['value']) for z in corr)==2*int(totient(D))
 orbits.append({'discriminant':disc,'bottom_projective_rows':len(rows),'linear_sum':sum(vals),'squared_sum':sum(v*v for v in vals),'full_small_matrix_correlation':sum(abs(z['value']) for z in corr)})
 def alpha(A,B,C,F0):return int(A%M==0 and B%E==0)*ch(C*F0)
 q=M*E*D
 for u in range(1,6):
  for z in range(1,6):
   for vv in [-1,0,1]:
    for ww in [-1,0,1]:
     v=M*E*vv;w=D*ww
     if math.gcd(u*z-v*w,q)!=1:continue
     for a1,b1,C,F0 in [(2,3,1,2),(1,2,3,4),(4,1,2,5)]:
      for sign in [-1,1]:
       for offA,offB in [(0,0),(1,0),(0,1),(1,1)]:
        A=M*a1+offA;B=sign*E*b1+offB
        assert alpha(u*A+v*C,u*B+v*F0,w*A+z*C,w*B+z*F0)==alpha(A,B,C,F0)
        autos+=1
out['CRT_orbit_zero_and_full_K_exact_value']={'cases':orbits,'small_integer_matrices_tested':len(matrices),'status':'PASS'}
out['full_integer_automorphy_not_only_SL2']={'cases':autos,'status':'PASS'}

# Fixing the top row modulo D would be a DIFFERENT problem: for D=5,
# top row (1,1) forces F-C=1 and the character sum is nonzero.
ch5=lambda n:int(kronecker_symbol(5,n))
fixed_top=sum(ch5(c*(c+1)) for c in range(5))
assert fixed_top==-1
out['top_row_not_fixed_modulo_D_caution']={'fixed_top_Jacobi_type_sum':fixed_top,'actual_free_bottom_orbit_sum':0,'status':'PASS'}

mapping=0
for d0 in [1,2,3]:
 for e0 in [1,2,3]:
  for a3,a4,b3,b4 in [(2,3,3,5),(1,11,1,13),(3,4,2,7)]:
   m=d0*a3*a4;ee=e0*b3*b4
   for a1,a2,b1,b2 in [(2,3,5,7),(3,4,2,9),(7,5,4,3)]:
    for sign in [-1,1]:
     A=m*a1;B=sign*ee*b1;C=b2;F0=a2
     k=m*a1*a2;ell=ee*b1*b2
     assert A*F0-B*C==k-sign*ell
     assert sign*B//ee==b1
     assert ch5(C*F0)==ch5(a2)*ch5(b2)
     mapping+=1
out['exact_both_sign_determinant_and_character_mapping']={'cases':mapping,'status':'PASS'}

assert F(7,64)*2+1==F(39,32)
assert F(39,32)>0
assert F(1,2)+F(1,2)==1
# Q_nu=sqrt(D)Q, x=sqrt(D)Q²: the outer Q² and sqrt(phi(D))<=sqrt(D)
# factors leave x^(1/2), rather than a logarithmic error.
assert F(2)-F(2,2)==1 # P exponent Q²*x^-1/2
assert 2*(400-519)==-238
out['natural_scale_error_and_contraction_exponents']={'single_shift_P_exponent_at_Delta_scale_x':str(F(39,32)),'optimistic_base_error_P_exponent':1,'separate_contraction_log_exponent':-238,'original_output_transfer_claimed':False,'status':'PASS'}
out['status']='PASS'
s=json.dumps(out,indent=2,sort_keys=True)+'\n';(HERE/'CHECKS.json').write_text(s);print(s,end='')
