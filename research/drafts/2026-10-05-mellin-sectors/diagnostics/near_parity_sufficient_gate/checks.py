#!/usr/bin/env python3
"""Finite tests only; the uniform same-branch proof is REPORT.md."""
import cmath,json,math
from pathlib import Path
from fractions import Fraction as F
import mpmath as mp
HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True}
assert 4-2*F(23,2)==-19
assert 6+F(23,4)<12 and 1200+519*F(23,2)<7200
assert F(1,8)-F(1,256)==F(31,256)>F(1,16)
assert F(1,4)-F(1,256)==F(63,256)>F(1,16)
assert 405+6-519==-108
assert 38+4152+90+5<5000
out['all_four_branch_tail_and_rectangle_exponents']='PASS'
mp.mp.dps=32
b=[mp.mpc(0,'.011'),mp.mpc(0,'.021'),mp.mpc(0,'.032')]
kn=mp.mpc(0,'.27');knp=mp.mpc(0,'-.31');kp=mp.mpc(0,'-.13');kpp=mp.mpc(0,'.42')
p=17

def A(t,k,kind,D,a,c):
 q=mp.mpf('.5')+1j*t+k
 if kind=='nu':
  pairs=[(b[0],a),(0,(a+c)%2)]
  f=(mp.mpf(p)/mp.pi)**(mp.mpf('.5')-q-b[0])*(mp.mpf(p*D)/mp.pi)**(mp.mpf('.5')-q)
 else:
  pairs=[(b[1],a),(b[2],a)]
  f=(mp.mpf(p)/mp.pi)**(1-2*q-b[1]-b[2])
 for shift,parity in pairs:f*=mp.gamma((1-q-shift+parity)/2)/mp.gamma((q+shift+parity)/2)
 return f

def pairs(t,k,kprime,kind,a,c):
 s=mp.mpf('.5')+1j*t
 shifts=[(b[0],a),(0,(a+c)%2)] if kind=='nu' else [(b[1],a),(b[2],a)]
 ans=[]
 for shift,parity in shifts:
  ans.extend([((1-s-k-shift+parity)/2,(1-s-kprime-shift+parity)/2,-1j/2),((s+kprime+shift+parity)/2,(s+k+shift+parity)/2,1j/2)])
 return ans

def G(t,i,j,a,c):
 ps=(pairs(t,kn,knp,'nu',a,c) if i else [])+(pairs(t,kp,kpp,'plain',a,c) if j else [])
 return mp.exp(sum(mp.loggamma(x)-mp.loggamma(y) for x,y,_ in ps))

fe=[];deriv=[];unit=[]
for D,c in [(5,0),(3,1)]:
 for a in [0,1]:
  for i in [0,1]:
   for j in [0,1]:
    for tr,ti in [(60,0),(100,25),(250,-70)]:
     t=mp.mpc(tr,ti)
     actual=(A(t,kn,'nu',D,a,c)/A(t,knp,'nu',D,a,c))**i*(A(t,kp,'plain',D,a,c)/A(t,kpp,'plain',D,a,c))**j
     cn=(mp.mpf(p)*mp.sqrt(D)/mp.pi)**(2*(knp-kn))
     cp=(mp.mpf(p)/mp.pi)**(2*(kpp-kp))
     expected=cn**i*cp**j*G(t,i,j,a,c)
     err=abs(actual/expected-1);assert err<mp.mpf('1e-26');fe.append(float(err))
     ps=(pairs(t,kn,knp,'nu',a,c) if i else [])+(pairs(t,kp,kpp,'plain',a,c) if j else [])
     dg=sum(rate*(mp.digamma(x)-mp.digamma(y)) for x,y,rate in ps)
     bound=sum(abs(rate)*abs(x-y)*(2/min(abs(mp.im(x)),abs(mp.im(y)))**2+mp.pi/min(abs(mp.im(x)),abs(mp.im(y)))) for x,y,rate in ps)
     assert abs(dg)<=bound+mp.mpf('1e-30')
     assert abs(mp.diff(lambda z:mp.log(G(z,i,j,a,c)),t)-dg)<mp.mpf('1e-25')
     deriv.append(float(abs(dg)*tr))
    for t in [mp.mpf('0'),mp.mpf('100')]:
     val=A(t,kn,'nu',D,a,c)**i*A(t,kp,'plain',D,a,c)**j
     er=abs(abs(val)-1);assert er<mp.mpf('1e-28');unit.append(float(er))
out['same_pair_conductor_and_gamma_cancellation']={'cases':len(fe),'max_relative_error':max(fe),'status':'PASS'}
out['joint_complex_height_log_derivatives']={'cases':len(deriv),'max_height_scaled_derivative':max(deriv),'status':'PASS'}
out['all_four_real_axis_FE_moduli']={'cases':len(unit),'max_error':max(unit),'status':'PASS'}

phase=[]
for i in [0,1]:
 for j in [0,1]:
  for d,e,m,n,mm,nn in [(2,3,7,5,11,13),(1,2,3,9,7,5)]:
   z1=mp.mpc('.05','.17');wr1=mp.mpc('-.05','.10');wn1=mp.mpc('-.05','-.30')
   z2=mp.mpc('.05','-.13');wr2=mp.mpc('-.05','-.18');wn2=mp.mpc('-.05','.55')
   def q(u,dual):return 1-u if dual else u
   def raw(t):
    s=mp.mpf('.5')+1j*t;u1=s+z1+wr1;u2=s+z1+wn1;v1=s+z2+wr2;v2=s+z2+wn2
    return d**(z1-u1)*m**(-q(u1,i))*n**(-q(u2,j))*mp.conj(e**(z2-v1)*mm**(-q(v1,i))*nn**(-q(v2,j)))
   x=d*m**(1-i)*n**(1-j)*mm**i*nn**j;y=e*m**i*n**j*mm**(1-i)*nn**(1-j)
   t=mp.mpf('3.7');err=abs(raw(t)/raw(0)-mp.exp(1j*t*mp.log(mp.mpf(y)/x)))
   assert err<mp.mpf('1e-27');phase.append(float(err))
out['all_coordinate_same_branch_ratio_phase']={'cases':len(phase),'max_error':max(phase),'status':'PASS'}

rect=[]
for i,j in [(0,0),(0,1),(1,0),(1,1)]:
 for theta in [-3,3]:
  tc=mp.mpf('70');H=mp.mpf('6');W=mp.mpf('2');Delta=mp.sign(theta)*H/8
  def residual(t):
   s=mp.mpf('.5')+1j*t;z=mp.mpc('.05','.21');w=mp.mpc('.05','-.17')
   return G(t,i,j,1,1)*mp.gamma((s+z)/2)/mp.gamma(s/2)*mp.gamma((1-s+w)/2)/mp.gamma((1-s)/2)
  def f(t):return mp.exp(-(t-tc)**2/(4*W**2)+1j*t*theta)*residual(t)/(2*mp.sqrt(mp.pi)*W)
  lo=tc-H;hi=tc+H
  bottom=mp.quad(f,[lo,tc,hi]);top=mp.quad(lambda x:f(x+1j*Delta),[lo,tc,hi])
  right=mp.quad(lambda y:1j*f(hi+1j*y),[0,Delta]);left=mp.quad(lambda y:1j*f(lo+1j*y),[0,Delta])
  error=abs(bottom-(top-right+left));assert error<mp.mpf('1e-25')
  rect.append(float(error))
out['all_four_finite_rectangles_and_vertical_endpoints']={'cases':len(rect),'max_error':max(rect),'status':'PASS'}

# Exact finite character covariance and full-K partition for every branch.
partitions=0;rootineq=0;character_errors=[]
for p,g in [(5,2),(7,3)]:
 logs={pow(g,r,p):r for r in range(p-1)}
 def char(k,n):return 0j if n%p==0 else cmath.exp(2j*math.pi*k*logs[n%p]/(p-1))
 tuples=[(d,m,n) for d in range(1,4) for m in range(1,4) for n in range(1,4)]
 for a in [0,1]:
  coeff={}
  for i in [0,1]:
   for j in [0,1]:
    ww={(d,m,n):complex(d+(i+1)*m-(j+1)*n, (d*m+n+i+j)%5-2) for d,m,n in tuples};coeff[i,j]=ww
    sums={k:0j for k in ['all','far','eq','near','mean_all','mean_far','mean_eq']}
    for d,m,n in tuples:
     for e,mm,nn in tuples:
      x=d*m**(1-i)*n**(1-j)*mm**i*nn**j;y=e*m**i*n**j*mm**(1-i)*nn**(1-j)
      if x%p==0 or y%p==0:continue
      value=ww[d,m,n]*ww[e,mm,nn].conjugate()
      geom=(p-1)/2*(int((x-y)%p==0)+(-1)**a*int((x+y)%p==0));mean=-int(a==0);K=geom+mean
      far=abs(math.log(y/x))>.3;eq=x==y
      sums['all']+=value*K;sums['mean_all']+=value*mean
      if far:sums['far']+=value*K;sums['mean_far']+=value*mean
      if eq:sums['eq']+=value*K;sums['mean_eq']+=value*mean
      if not far and not eq:sums['near']+=value*geom
      partitions+=1
    meanoff=sums['mean_all']-sums['mean_far']-sums['mean_eq']
    assert abs(sums['all']-sums['near']-sums['eq']-meanoff-sums['far'])<1e-7
    assert abs(sums['near'].imag)<1e-8
    direct=0.0
    for k in range(1,p-1):
     if k%2!=a:continue
     val=sum(ww[d,m,n]*char(k,d)*(char(k,m).conjugate() if i else char(k,m))*(char(k,n).conjugate() if j else char(k,n)) for d,m,n in tuples)
     direct+=abs(val)**2
    err=abs(direct-sums['all']);assert err<1e-7;character_errors.append(err)
  for k in range(1,p-1):
   if k%2!=a:continue
   bs={}
   for i in [0,1]:
    for j in [0,1]:bs[i,j]=sum(coeff[i,j][d,m,n]*char(k,d)*(char(k,m).conjugate() if i else char(k,m))*(char(k,n).conjugate() if j else char(k,n)) for d,m,n in tuples)
   eps=sum(char(k,r)*cmath.exp(2j*math.pi*r/p) for r in range(1,p))/((1j)**a*math.sqrt(p));omega=eps**2
   chip=1 if p%3==1 else -1;kappa=chip*char(k,3)*(-1)**a
   total=bs[0,0]+omega*bs[0,1]+kappa*omega*bs[1,0]+kappa*omega**2*bs[1,1]
   assert abs(total)**2<=4*sum(abs(v)**2 for v in bs.values())+1e-7
   rootineq+=1
out['exact_character_full_kernel_near_partition']={'tuple_cases':partitions,'max_character_covariance_error':max(character_errors),'near_rows_real':True,'status':'PASS'}
out['uniform_label_dependent_unit_root_inequality']={'actual_labels':rootineq,'status':'PASS'}
out['status']='PASS'
s=json.dumps(out,indent=2,sort_keys=True)+'\n';(HERE/'CHECKS.json').write_text(s);print(s,end='')
