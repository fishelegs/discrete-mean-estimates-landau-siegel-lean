"""Portable exact-rational conditional gate diagnostics; not an analytic certificate."""
from fractions import Fraction as F
import json
def gate(r,s,eA,eQ,gamma,kappa):
 return kappa*(1-F(1,r)-F(1,s))-F(eA,r)-F(eQ,s)-gamma*(1+F(1,r)+F(1,s))
J=gate(3,3,81,81,77,739);H=gate(3,4,81,144,77,739);R=2*F(1435,4)-F(81+81+5*77,3)
assert J==64 and H==123 and R==F(3211,6)
for beta,m in ((52,6),(40,12)):assert F(beta,2)-32==-m
kappa=min(740+2*F(87,4),746+2*F(75,4),739+2*F(89,4))
assert kappa==F(1567,2) and gate(3,3,81,81,77,kappa)==F(473,6)
assert 739-77==662
cases=0
for r in (2,3,4,5,6):
 for s in (2,3,4,5,6):
  theta=(1-F(1,r)-F(1,s))/2
  if theta<=0:continue
  assert F(1,2)+F(1,2*r)+F(1,2*s)+theta==1
  moment_mass=F(1,2)+F(1,2*r)+F(1,2*s)
  assert moment_mass==1-theta
  for gamma in (50,77,100):
   for k in (700,739,800):
    beta=F(61);eA=81;eQ=144
    exponent=beta/2+F(eA,2*r)+F(eQ,2*s)+gamma*moment_mass-k*theta
    assert exponent==(beta-gate(r,s,eA,eQ,gamma,k))/2;cases+=1
assert 3*F(63,125)<2 and 4*F(63,125)>2
print(json.dumps(dict(status='PASS',general_Holder_identity_cases=cases,original_gates={'J':str(J),'H':str(H),'R':str(R),'integrated_joint':'662'},new_mask_kappa=str(kappa),new_mask_J_gate='473/6',numerical_changed_time_kappa_proved=False,genuine_N_moment_proved=False),indent=2,sort_keys=True))
