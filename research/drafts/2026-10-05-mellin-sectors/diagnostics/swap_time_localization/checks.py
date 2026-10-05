#!/usr/bin/env python3
"""Finite diagnostics; REPORT.md contains the uniform analytic proof."""
import cmath,json,math
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True}
assert 405-395==10 and 2*405-2*400==10
assert 405+6-519==-108
assert F(1,8)-F(1,256)==F(31,256)>F(1,16)
assert F(1,4)-F(1,256)==F(63,256)>F(1,16)
assert 4-2*F(23,2)==-19
assert 6+F(1,2)*F(23,2)==F(47,4)<12
assert 1200+519*F(23,2)==F(14337,2)<7200
assert 38+4152+90+5==4285<5000
out['exact_tail_rectangle_and_logarithmic_exponents']='PASS'

mp.mp.dps=35
b=[mp.mpc(0,'.011'),mp.mpc(0,'.021'),mp.mpc(0,'.032')]
k1=mp.mpc(0,'.37');k2=mp.mpc(0,'-.28')
z=mp.mpc('.05','.43');om=mp.mpc('.05','-.21')
p=17

def Anu(t,D,a,c):
 q=mp.mpf('.5')+1j*t+k1;ac=(a+c)%2
 return (mp.mpf(p)/mp.pi)**(mp.mpf('.5')-q-b[0])*(mp.mpf(p*D)/mp.pi)**(mp.mpf('.5')-q)*mp.gamma((1-q-b[0]+a)/2)/mp.gamma((q+b[0]+a)/2)*mp.gamma((1-q+ac)/2)/mp.gamma((q+ac)/2)
def A23(t,a):
 q=mp.mpf('.5')+1j*t+k2
 val=(mp.mpf(p)/mp.pi)**(1-2*q-b[1]-b[2])
 for bj in b[1:]:val*=mp.gamma((1-q-bj+a)/2)/mp.gamma((q+bj+a)/2)
 return val

def gamma_pairs(t,a,c):
 s=mp.mpf('.5')+1j*t;ac=(a+c)%2
 return [((s+k2+b[1]+a)/2,(s+k1+b[0]+a)/2,1j/2),((s+k2+b[2]+a)/2,(s+k1+ac)/2,1j/2),((1-s-k1-b[0]+a)/2,(1-s-k2-b[1]+a)/2,-1j/2),((1-s-k1+ac)/2,(1-s-k2-b[2]+a)/2,-1j/2)]
def G(t,a,c):
 return mp.exp(sum(mp.loggamma(A)-mp.loggamma(B) for A,B,_ in gamma_pairs(t,a,c)))
fe=[];derivs=[]
for D,c in [(5,0),(3,1)]:
 for a in [0,1]:
  for tr,ti in [(50,0),(50,20),(200,-35),(500,100)]:
   t=mp.mpc(tr,ti)
   Omega=D**(-k1)*(mp.mpf(p)/mp.pi)**(2*(k2-k1)+b[1]+b[2]-b[0])
   exact=D**(-1j*t)*Omega*G(t,a,c)
   actual=Anu(t,D,a,c)/A23(t,a)
   err=abs(actual/exact-1)
   star=mp.conj(A23(mp.conj(t),a))
   assert abs(star*A23(t,a)-1)<mp.mpf('1e-28')
   assert err<mp.mpf('1e-27'),err
   fe.append(float(err))
   pairs=gamma_pairs(t,a,c)
   derivative=sum(rate*(mp.digamma(A)-mp.digamma(B)) for A,B,rate in pairs)
   bound=sum(abs(rate)*abs(A-B)*(2/min(abs(mp.im(A)),abs(mp.im(B)))**2+mp.pi/min(abs(mp.im(A)),abs(mp.im(B)))) for A,B,rate in pairs)
   assert abs(derivative)<=bound
   numerical=mp.diff(lambda x:mp.log(G(x,a,c)),t)
   assert abs(numerical-derivative)<mp.mpf('1e-27')
   derivs.append(float(abs(derivative)*tr))
out['exact_joint_FE_conductor_and_gamma_pairing']={'cases':len(fe),'max_relative_error':max(fe),'status':'PASS'}
out['joint_residual_log_derivative']={'cases':len(derivs),'max_height_scaled_derivative':max(derivs),'status':'PASS'}

trigamma=[]
for x in [-1000,-47.3,-2.1,0,2,100]:
 for y in [-100,-10,-1,1,10,100]:
  zz=mp.mpc(x,y)
  bound=2/mp.mpf(y)**2+mp.pi/abs(y)
  val=abs(mp.polygamma(1,zz))
  assert val<=bound
  trigamma.append(float(val/bound))
out['uniform_trigamma_off_real_axis']={'cases':len(trigamma),'largest_bound_ratio':max(trigamma),'status':'PASS'}

# The entire original Dirichlet monomial, at nonzero Mellin heights.
phase=[]
for d,e,m,n,mm,nn in [(2,3,7,5,11,13),(1,1,27,9,3,9),(4,5,6,7,8,9)]:
 D=3;t=mp.mpf('4.2');s=mp.mpf('.5')+1j*t
 z1=mp.mpc('.05','.17');wr1=mp.mpc('-.05','.20');wn1=mp.mpc('-.05','-.31')
 z2=mp.mpc('.05','-.13');wr2=mp.mpc('-.05','.23');wn2=mp.mpc('-.05','-.15')
 def direct(T):
  S=mp.mpf('.5')+1j*T;u11=S+z1+wr1;u12=S+z1+wn1;u21=S+z2+wr2;u22=S+z2+wn2
  return d**(z1-u11)*m**(u11-1)*n**(-u12)*mp.conj(e**(z2-u21)*mm**(-u21)*nn**(u22-1))
 ratio=direct(t)/direct(0)*D**(-1j*t)
 expected=mp.exp(1j*t*mp.log(mp.mpf(e*m*mm)/(D*d*n*nn)))
 err=abs(ratio-expected);assert err<mp.mpf('1e-29');phase.append(float(err))
out['all_coordinate_extracted_Dirichlet_phase']={'cases':len(phase),'max_error':max(phase),'status':'PASS'}

# Analytic finite-window contour identity, retaining both vertical edges.
contours=[]
for theta in [-3,3]:
 tc=mp.mpf('80');H=mp.mpf('6');W=mp.mpf('2');Delta=mp.sign(theta)*H/8
 def residual(t):
  s=mp.mpf('.5')+1j*t
  return G(t,0,1)*mp.gamma((s+z)/2)/mp.gamma(s/2)*mp.gamma((1-s+om)/2)/mp.gamma((1-s)/2)
 def f(t):return mp.exp(-(t-tc)**2/(4*W**2))*mp.exp(1j*t*theta)*residual(t)/(2*mp.sqrt(mp.pi)*W)
 lo=tc-H;hi=tc+H
 bottom=mp.quad(f,[lo,tc,hi])
 shifted=mp.quad(lambda x:f(x+1j*Delta),[lo,tc,hi])
 right=mp.quad(lambda y:1j*f(hi+1j*y),[0,Delta])
 left=mp.quad(lambda y:1j*f(lo+1j*y),[0,Delta])
 error=abs(bottom-(shifted-right+left))
 assert error<mp.mpf('1e-28'),error
 contours.append({'theta':theta,'rectangle_identity_error':float(error),'bottom_modulus':float(abs(bottom)),'shifted_modulus':float(abs(shifted)),'endpoint_modulus_sum':float(abs(left)+abs(right))})
out['finite_gaussian_rectangle_with_endpoints']={'cases':contours,'status':'PASS'}

# Exact partition of the actual parity covariance with arbitrary weights.
partitions=0
for p in [5,7,11]:
 D=3
 if p==D:continue
 for a in [0,1]:
  sums={k:0j for k in ['all','far','eq','near_off_geom','mean_all','mean_far','mean_eq']}
  for d in [1,2]:
   for e in [1,2]:
    for m in [1,2,3]:
     for n in [1,2,3]:
      for mm in [1,2,3]:
       for nn in [1,2,3]:
        x=D*d*n*nn;y=e*m*mm
        if x%p==0 or y%p==0:continue
        w=complex(d+m-2*n,e+mm-2*nn)
        geom=(p-1)/2*((x-y)%p==0)+(p-1)/2*(-1)**a*((x+y)%p==0)
        mean=-int(a==0);K=geom+mean
        far=abs(math.log(y/x))>.3;eq=x==y
        sums['all']+=w*K;sums['mean_all']+=w*mean
        if far:sums['far']+=w*K;sums['mean_far']+=w*mean
        if eq:sums['eq']+=w*K;sums['mean_eq']+=w*mean
        if not far and not eq:sums['near_off_geom']+=w*geom
        partitions+=1
  mean_near_off=sums['mean_all']-sums['mean_far']-sums['mean_eq']
  assert sums['all']==sums['near_off_geom']+sums['eq']+mean_near_off+sums['far']
out['near_far_full_kernel_principal_equality_partition']={'tuple_cases':partitions,'status':'PASS'}

out['status']='PASS'
text=json.dumps(out,indent=2,sort_keys=True)+'\n'
(HERE/'CHECKS.json').write_text(text)
print(text,end='')
