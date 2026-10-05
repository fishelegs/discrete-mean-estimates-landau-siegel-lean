import json,math,itertools
from fractions import Fraction as F
from pathlib import Path
root=Path(__file__).resolve().parent
cases=0
for eta in [.1,.25,.5,.75]:
 c=min(.01,abs(math.log(1+eta))/8,abs(math.log(1-eta))/8,math.sqrt((math.sqrt(1+eta)-1)/(10*math.sqrt(1+eta))))
 for W in [2.,4.,8.]:
  T=W*W
  for r in [1+eta,2+eta,10.]:
   A=T*(math.sqrt(r)-1);u0=-.5*math.log(r);y=c*min(A/W**2,1)
   assert T*math.sqrt(r)*math.sin(y)/y-T>=A/2
   assert W*W*y*y-2*math.pi*y*(T*math.sqrt(r)*math.sin(y)/y-T)<=-A*y
   assert y*y<=u0*u0/4;cases+=1
  for r in [1-eta,(1-eta)/2]:
   A=T*(1-math.sqrt(r));u0=.5*math.log(1/r);y=c*A/W**2
   assert W*W*y*y+2*math.pi*y*(T*math.sqrt(r)*math.sin(y)/y-T)<=-A*y
   assert y*y<=u0*u0/4;cases+=1
for eps in [F(1,100),F(1,10),F(1,4)]:assert F(2)/(1+eps)>F(3,2)
out={'status':'PASS','finite_diagnostics_only':True,'fixed_gap_contour_cases':cases,'exact_primary_upper_edge':'2/(1+epsilon)>3/2 when epsilon<1/3'}
s=json.dumps(out,indent=2)+'\n';(root/'CHECKS.json').write_text(s);print(s,end='')
