#!/usr/bin/env python3
"""Finite Fourier-grid/identity and exact arithmetic-ledger checks only."""
import json,math,itertools
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import numpy as np
ROOT=Path(__file__).resolve().parent
out={'finite_diagnostics_only':True,'FFT_values_are_not_rigorous_error_certificates':True}
N=16384;Y=64.;dy=2*Y/N;y=-Y+dy*np.arange(N);xi=np.fft.fftshift(np.fft.fftfreq(N,d=dy));dxi=1/(N*dy)
rows=[]
for W,tau in itertools.product([2.,4.,8.,16.],[0.,.1,.5,1.]):
 T=tau*W*W;valid=y>-W
 U=np.zeros(N,dtype=complex);Up=np.zeros(N,dtype=complex)
 u=np.log1p(y[valid]/W)
 U[valid]=np.exp(-u/2-W*W*u*u+2j*np.pi*T*(u-y[valid]/W))
 lp=-(.5+2*W*W*u)/(W+y[valid])+2j*np.pi*T/W*(np.exp(-u)-1)
 Up[valid]=U[valid]*lp
 G0=np.exp(-y*y);R=U-G0;Rp=Up+2*y*G0
 rh=dy*np.fft.fftshift(np.fft.fft(np.fft.ifftshift(R)))
 norm=np.sum(np.abs(rh))*dxi
 l2=np.sum(np.abs(R)**2)*dy
 fourierl2=np.sum(np.abs(rh)**2)*dxi
 assert abs(l2-fourierl2)<1e-11
 Hspec=(np.sum((1+(2*np.pi*xi)**2)*np.abs(rh)**2)*dxi)**.5
 cgrid=(np.sum(1/(1+(2*np.pi*xi)**2))*dxi)**.5
 assert norm<=cgrid*Hspec+1e-12
 Hreal=(np.sum(np.abs(R)**2+np.abs(Rp)**2)*dy)**.5
 eps=tau+1/W
 assert norm/eps<100 and Hreal/eps<100
 rows.append({'W':W,'T':T,'tau':tau,'Fourier_L1_over_epsilon':float(norm/eps),'H1_over_epsilon':float(Hreal/eps),'spectral_real_H1_difference':float(abs(Hspec-Hreal))})
out['rescaled_Fourier_and_H1_samples']={'cases':len(rows),'rows':rows,'status':'PASS'}
# Exact variable-change normalization and derivative symbol.
ident=0
for W,T,u in itertools.product([2.,5.,12.],[0.,3.,10.],[-3.,-.5,0.,.3,2.]):
 v=math.expm1(u);yy=W*v
 Fv=(1+v)**(-.5)*np.exp(2j*np.pi*T*math.log1p(v)-W*W*math.log1p(v)**2)
 original=np.exp((.5+2j*np.pi*T)*u-W*W*u*u)
 assert abs(Fv*math.exp(u)-original)<1e-10*(1+abs(original));ident+=1
out['Jacobian_and_carrier_normalization']={'cases':ident,'status':'PASS'}
# Endpoint flatness: u-polynomial and fixed exp multiples are overwhelmed.
end=0
for W,j,m in itertools.product([2,4,8],[0,1,2,4],[0,1,3]):
 logs=[]
 for v in [4,8,16,32]:
  # A deliberately coarse fixed-order derivative/weight tail envelope.
  logs.append(-W*W*v*v+(j+m+2)*v+(j+m+2)*math.log(W*(1+v)))
 assert logs[-1]<logs[-2]<logs[-3] and logs[-1]<-100;end+=1
out['v_minus_one_derivative_tail_envelopes']={'cases':end,'status':'PASS'}
# Complex contour real parts in the off-comparable exponential proof.
cont=0
for W in [2.,4.,8.,16.]:
 for T in [2*W,W*W]:
  for r in [2.,3.,10.,100.]:
   A=T*(math.sqrt(r)-1);h=.01*min(A/W**2,1)
   phase=W*W*h*h-2*np.pi*h*(T*math.sqrt(r)*math.sin(h)/h-T)
   assert phase<=-A*h
   u0=-.5*math.log(r);assert h*h<=u0*u0/4;cont+=1
  for r in [.5,.1,.001]:
   A=T*(1-math.sqrt(r));h=.01*A/W**2
   phase=W*W*h*h+2*np.pi*h*(T*math.sqrt(r)*math.sin(h)/h-T)
   assert phase<=-A*h
   u0=.5*math.log(1/r);assert h*h<=u0*u0/4;cont+=1
out['one_sided_exponential_contour_signs']={'cases':cont,'status':'PASS'}
@lru_cache(None)
def factors(n):
 ans=[];p=2
 while p*p<=n:
  if n%p==0:
   e=0
   while n%p==0:n//=p;e+=1
   ans.append(e)
  p+=1
 if n>1:ans.append(1)
 return ans
def tau(n,r):return math.prod(math.comb(e+r-1,r-1) for e in factors(n))
hyp=0
for r,x,h in itertools.product([2,3,5],[10,31,100],[1,3,7]):
 U=0
 while (U+1)**r<=(2*x)**(r-1):U+=1
 lhs=sum(tau(n,r) for n in range(x,x+h+1))
 rhs=r*sum(tau(q,r-1)*(F(h,q)+1) for q in range(1,U+1))
 assert lhs<=rhs;hyp+=1
out['divisor_sampling_hyperbola_input']={'cases':hyp,'status':'PASS'}
for g,want in [(118,(247,128)),(113,(237,123))]:
 got=next((a,b) for a in range(1,600) for b in range(9,600) if a-b>g and 2*b-a>=9)
 assert got==want
out['local_interface_integer_pairs']={'unchanged_phase_gap':[247,128],'conditional_refined_phase_gap':[237,123],'not_global_parameter_theorems':True,'status':'PASS'}
assert 2+9*11==101
out['principal_scalar_log_budget']='p L^2 B^11 = p L^101'
out['status']='PASS'
s=json.dumps(out,sort_keys=True,indent=2)+'\n';(ROOT/'CHECKS.json').write_text(s);print(s,end='')
