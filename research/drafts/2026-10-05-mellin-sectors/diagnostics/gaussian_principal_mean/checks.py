#!/usr/bin/env python3
"""Finite diagnostics only; the all-height contour/norm proof is REPORT.md."""
import cmath
import json
import math
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
from sympy import primitive_root, factorint, divisors
HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True}
assert -8+F(1,2)+6==-F(3,2)
assert 13-14+F(1,2)==-F(1,2)
assert -8-14+1==-21
assert F(1,2)+F(1,99)-F(1,99)==F(1,2)
assert F(1,2)-F(1,4)==F(1,4)
assert 1+7*9+12*519==6292<6400
assert 12+24*9==228
assert F(959,15)<64
out['exact_exponents_critical_lines_and_gamma_pole_gap']='PASS'

cutoffs=0
for R,S in [(4,3),(4.2,3.7)]:
 for A in [.25,1,2,4,6,10]:
  for C in [.1,1,2.5,3,8]:
   for r in range(1,12):
    for n in range(1,10):
     hr=int(r>R);ha=int(r>A);hs=int(n>S);hc=int(n>C)
     assert hr*hs-ha*hc==(hr-ha)*hs+ha*(hs-hc)
     # Prefix windows and literal intersection decomposition.
     assert (hr-ha)*hs==((1-ha)-(1-hr))-((1-ha)-(1-hr))*(1-hs)
     assert ha*(hs-hc)==ha*(1-hc)-ha*(1-hs)
     cutoffs+=1
out['two_sided_cutoff_difference']={'cases':cutoffs,'status':'PASS'}

conv=0
for t in range(-7,8):
 for v in range(-5,6):
  for r in range(-4,5):
   for n in [-3,-1,0,2,5]:
    q=F(v*v+r*r+n*n)
    for y in [r,n]:
     assert q/2+F((t+v+y)**2,4)>=q/4+F(t*t,12)
     conv+=1
out['global_outer_gaussian_convolution']={'cases':conv,'status':'PASS'}

mp.mp.dps=32
mellin=[]
for alpha in [mp.mpf('.2'),mp.mpf('.05')]:
 for x in [mp.mpf('.1'),mp.mpf('1'),mp.mpf('3')]:
  def f(y):
   w=-alpha+1j*y
   return -mp.exp(w*w/2)/w*mp.exp(-w*mp.log(x))/(2*mp.pi)
  val=mp.quad(f,[-12,-6,-2,-.5,0,.5,2,6,12])
  exact=(1+mp.erf(mp.log(x)/mp.sqrt(2)))/2
  err=abs(val-exact)
  assert err<mp.mpf('1e-23'),(alpha,x,err)
  mellin.append(float(err))
out['gaussian_log_mellin_inversion']={'cases':len(mellin),'max_error':max(mellin),'status':'PASS'}

# Numerical checks of the exact artificial-weight contour identity. Each
# case keeps the p-Euler deletions, gamma ratios and combined zeta-pole circle.
contours=[]
for kind,T,bs in [('mixed',mp.mpf('0'),[mp.mpf('.013'),0]),('mixed',mp.mpf('2.1'),[mp.mpf('-.013'),0]),('plain',mp.mpf('.7'),[mp.mpf('.011'),mp.mpf('.023')]),('plain',mp.mpf('1.2'),[mp.mpf('.017'),mp.mpf('.017')])]:
 D=5;p=17;B=100;K=3;q=mp.mpf('.5')+1j*T
 gammas=[1j*b for b in bs];parities=[0,0]
 C=mp.mpf(p)*(mp.sqrt(D) if kind=='mixed' else 1)/mp.pi
 chi=[0,1,-1,-1,1];chip=chi[p%D]
 def E(s):
  if kind=='mixed':return (1-p**(-s-gammas[0]))*(1-chip*p**(-s))*mp.zeta(s+gammas[0])*mp.dirichlet(s,chi)
  return (1-p**(-s-gammas[0]))*(1-p**(-s-gammas[1]))*mp.zeta(s+gammas[0])*mp.zeta(s+gammas[1])
 def integrand(w):
  g=mp.mpc(1)
  for b,a in zip(gammas,parities):g*=mp.gamma((q+b+a+w)/2)/mp.gamma((q+b+a)/2)
  return mp.exp(w*w)/w*C**w*g*E(q+w)
 def vertical(c):return mp.quad(lambda y:integrand(c+1j*y)/(2*mp.pi),[-10,-6,-3,-1,0,1,3,6,10])
 left=vertical(mp.mpf('-.25'));right=vertical(mp.mpf('2'))
 rad=mp.mpf(2*K+1)/B;center=mp.mpf('.5')-1j*T
 circle=mp.quad(lambda theta:integrand(center+rad*mp.exp(1j*theta))*rad*mp.exp(1j*theta)/(2*mp.pi),[0,mp.pi/2,mp.pi,3*mp.pi/2,2*mp.pi])
 err=abs(right-(left+E(q)+circle))
 assert err<mp.mpf('1e-19'),(kind,T,err)
 contours.append({'kind':kind,'height':str(T),'repeated_pole':bs[0]==bs[1],'error':float(err)})
out['artificial_principal_inner_contour_identity']={'cases':contours,'status':'PASS'}

# Exact nonprincipal root reduction and the EVEN principal correction.
rootchecks=0
for p in [5,7,11,13]:
 g=int(primitive_root(p));log={pow(g,j,p):j for j in range(p-1)}
 def psi(j,n):return 0j if n%p==0 else cmath.exp(2j*math.pi*j*log[n%p]/(p-1))
 def eps(j):
  a=j%2
  return sum(psi(j,b)*cmath.exp(2j*math.pi*b/p) for b in range(1,p))/((1j)**a*math.sqrt(p))
 for a in [0,1]:
  js=[j for j in range(p-1) if j%2==a]
  for h in [0,1,2]:
   for x,y in [(1,1),(2,3),(p,1),(1,p)]:
    full=sum(eps(j)**(2*h)*psi(j,x)*psi(j,y).conjugate() for j in js)
    non=sum(eps(j)**(2*h)*psi(j,x)*psi(j,y).conjugate() for j in js if j!=0)
    correction=(p**(-h) if a==0 and x%p and y%p else 0)
    assert abs(full-non-correction)<1e-11
    # Negative powers are defined on nonprincipals and conjugated, never
    # by substituting the principal epsilon into a negative exponent.
    neg=sum(eps(j)**(-2*h)*psi(j,x)*psi(j,y).conjugate() for j in js if j!=0)
    swapped=sum(eps(j)**(2*h)*psi(j,y)*psi(j,x).conjugate() for j in js if j!=0).conjugate()
    assert abs(neg-swapped)<1e-10
    rootchecks+=1
out['reduced_root_kernel_principal_corrections']={'cases':rootchecks,'status':'PASS'}

# Principal mask factorization and total-minus-equality bookkeeping use
# arbitrary complex weights, not positivity or arithmetic cancellation.
factorchecks=0
for p in [5,7,11]:
 for D in [3,8]:
  if D%p==0:continue
  tuples=[(d,m,n) for d in range(1,4) for m in range(1,4) for n in range(1,4)]
  w1={x:complex((sum(x)%5)-2,(x[0]+2*x[1]-x[2])%4-1) for x in tuples}
  w2={x:complex((x[0]*x[1]+x[2])%7-3,(sum(x)%3)-1) for x in tuples}
  b1=sum(v for (d,m,n),v in w1.items() if d*m*n%p)
  b2=sum(v for (d,m,n),v in w2.items() if d*m*n%p)
  total=0j;eq=0j;off=0j
  for (d,m,n),v in w1.items():
   for (e,mm,nn),z in w2.items():
    x=D*d*n*nn;y=e*m*mm
    val=-v*z.conjugate() if x%p and y%p else 0j
    total+=val
    if x==y:eq+=val
    else:off+=val
    factorchecks+=1
  assert total==-b1*b2.conjugate()
  assert off==total-eq
out['principal_masks_and_complement_bookkeeping']={'tuple_pairs':factorchecks,'status':'PASS'}

def tau(k,n):
 ans=1
 for e in factorint(n).values():ans*=math.comb(e+k-1,k-1)
 return ans
rows=0
for D in [3,5,8]:
 for d in range(1,5):
  for n in range(1,5):
   for nn in range(1,4):
    T=D*d*n*nn
    assert sum(tau(2,e)*tau(4,T//e) for e in divisors(T))==tau(6,T)
    assert tau(6,T)<=tau(6,D)*tau(6,d)*tau(6,n)*tau(6,nn)
    for e in divisors(T):
     for m in divisors(T//e):
      mm=T//e//m
      assert d*e*m*mm*n*nn==D*d*d*n*n*nn*nn
    rows+=1
out['gaussian_equality_row_contraction']={'cases':rows,'status':'PASS'}

out['status']='PASS'
text=json.dumps(out,indent=2,sort_keys=True)+'\n'
(HERE/'CHECKS.json').write_text(text)
print(text,end='')
