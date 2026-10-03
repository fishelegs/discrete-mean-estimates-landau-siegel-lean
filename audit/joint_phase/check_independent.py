from fractions import Fraction as F
from pathlib import Path
import json

def add(z,w):return (z[0]+w[0],z[1]+w[1])
def neg(z):return(-z[0],-z[1])
def sub(z,w):return add(z,neg(w))
def mul(z,w):return(z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def conj(z):return(z[0],-z[1])
def norm2(z):return z[0]**2+z[1]**2
def div(z,w):
    n=norm2(w);assert n
    a=mul(z,conj(w));return(a[0]/n,a[1]/n)
def power(z,k):
    ans=(F(1),F(0))
    while k:
        if k%2:ans=mul(ans,z)
        z=mul(z,z);k//=2
    return ans
one=(F(1),F(0));zero=(F(0),F(0))
values=[zero,one,(F(0),F(1)),(F(2),F(1)),(F(-1),F(2)),(F(1,2),F(-2,3)),(F(3),F(-1))]
roots=[one,neg(one),(F(0),F(1)),(F(0),F(-1))]
count=0
for M in values:
 for S in values:
  for r in roots:
   U=mul(r,div(M,conj(M))) if M!=zero else one
   W=mul(M,S);Z=mul(r,mul(M,conj(S)))
   assert norm2(U)==1
   assert Z==mul(U,conj(W))
   for k in [1,2,8,21]:
    assert norm2(sub(power(U,k),power(Z,k)))==norm2(sub(one,power(W,k)))
    count+=1
j10=-F(2011,4)+4*10**2+4*10
j11=-F(2011,4)+4*11**2+4*11
theta=F(10,21)
assert theta/F(20)+(1-theta)/F(22)==F(1,21)
e21=theta*j10+(1-theta)*j11
assert j10==-F(251,4) and j11==F(101,4) and e21==-F(1399,84)
assert theta*440+(1-theta)*528==F(10208,21)
assert -F(2011,4)+8==-F(1979,4)
assert sum((1-F(k,22))*k*k for k in range(1,22))==F(1771,2)
assert 4*F(1771,2)==3542 and F(3542,22)==161
assert 2*sum(1-F(k,22) for k in range(1,22))==21
result={'status':'PASS','exact_complex_power_cases':count,'covers_M_zero':True,
 'L20_exponent':str(j10),'L22_exponent':str(j11),'L21_exponent':str(e21),
 'interpolation_weight':str(theta),'Fejer_peak':22,'Fejer_quadratic_loss':3542,
 'external_hyper_Kloosterman_bound_formalized_here':False,
 'scope':'Exact algebra and rational exponent checks; uniform character/arithmetic assertions are in the independently reviewed source proof, not numerically simulated.'}
Path(__file__).with_name('INDEPENDENT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
