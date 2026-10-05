"""Finite independent Fourier/contour diagnostics; not a rigorous certificate."""
import json,math
import numpy as np
# Separate frequency-grid checks with different grid and parameter choices.
N=32768;Y=96.;dy=2*Y/N;y=np.arange(N)*dy-Y;freq=np.fft.fftshift(np.fft.fftfreq(N,d=dy));df=1/(N*dy)
rows=[]
for W in (2.5,6.,12.,24.):
 for tau in (0.,.03,.3,.9):
  T=tau*W*W;valid=y>-W;u=np.log1p(y[valid]/W)
  A=np.zeros(N,dtype=complex)
  A[valid]=np.exp(-u/2-W*W*u*u+2j*np.pi*T*(u-y[valid]/W))
  R=A-np.exp(-y*y);ft=dy*np.fft.fftshift(np.fft.fft(np.fft.ifftshift(R)))
  assert abs(np.sum(abs(R)**2)*dy-np.sum(abs(ft)**2)*df)<1e-10
  l1=np.sum(abs(ft))*df;weighted=np.sum((1+abs(freq))*abs(ft))*df
  assert l1/(tau+1/W)<100 and weighted/(tau+1/W)<100
  rows.append(dict(W=W,tau=tau,l1_over_epsilon=float(l1/(tau+1/W)),weighted_l1_over_epsilon=float(weighted/(tau+1/W))))
# Fixed-gap contour signs, including the source-consumer edge below 2T.
contours=0
for W in (2.,5.,20.):
 for T in (2*W,W*W):
  if T<2*W:continue
  for r in (1.5,1.9,1.999,2.,4.,25.):
   a=T*(math.sqrt(r)-1);h=.001*min(a/(W*W),1.)
   exponent=W*W*h*h+2*math.pi*(T*h-T*math.sqrt(r)*math.sin(h))
   assert exponent<-a*h;contours+=1
  for r in (.75,.5,.1,.001):
   a=T*(1-math.sqrt(r));h=.001*a/(W*W)
   exponent=W*W*h*h+2*math.pi*(-T*h+T*math.sqrt(r)*math.sin(h))
   assert exponent<-a*h;contours+=1
for gap,want in ((118,(247,128)),(113,(237,123))):
 got=next((a,b) for a in range(1,500) for b in range(9,a) if a-b>gap and 2*b-a>=9)
 assert got==want
print(json.dumps(dict(status='PASS',frequency_grid_cases=rows,fixed_gap_contour_cases=contours,FFT_is_not_a_rigorous_certificate=True,altered_global_theorem=False,tilted_kernel_proved=False),indent=2,sort_keys=True))
