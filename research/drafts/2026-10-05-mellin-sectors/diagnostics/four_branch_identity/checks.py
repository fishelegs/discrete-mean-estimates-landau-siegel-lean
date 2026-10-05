#!/usr/bin/env python3
"""Finite algebra/analytic diagnostics; no energy estimate is certified."""
import cmath
import json
import math
from pathlib import Path
import mpmath as mp
from sympy import divisors, factorint, kronecker_symbol, mobius, primitive_root

HERE=Path(__file__).resolve().parent
out={'diagnostic_only':True,'actual_energy_lower_bound_claimed':False}
mp.mp.dps=50

def chi_table(disc):
 D=abs(disc)
 return D,[int(kronecker_symbol(disc,n)) for n in range(D)]

def prime_chars(p):
 g=int(primitive_root(p));logs={pow(g,e,p):e for e in range(p-1)}
 result=[]
 for j in range(1,p-1):
  a=j%2
  vals=[0j]+[cmath.exp(2j*math.pi*j*logs[n]/(p-1)) for n in range(1,p)]
  tau=sum(vals[n]*cmath.exp(2j*math.pi*n/p) for n in range(p))
  eps=tau/(1j**a*math.sqrt(p))
  assert abs(abs(eps)-1)<2e-13
  result.append((j,a,vals,eps))
 return result

root_cases=0;max_root_error=0.0;inert_phases=[]
for disc in [-3,5,-7,8,12]:
 D,ch=chi_table(disc);c=0 if ch[-1]==1 else 1
 tch=sum(mp.mpf(ch[n])*mp.exp(2j*mp.pi*n/D) for n in range(D))
 ech=tch/(1j**c*mp.sqrt(D))
 for p in [7,11,13,17]:
  if p<=D:continue
  g=int(primitive_root(p));logs={pow(g,e,p):e for e in range(p-1)}
  for j in range(1,p-1):
   a=j%2
   def psi(n):return mp.mpc(0) if n%p==0 else mp.exp(2j*mp.pi*j*logs[n%p]/(p-1))
   ep=sum(psi(n)*mp.exp(2j*mp.pi*n/p) for n in range(p))/(1j**a*mp.sqrt(p))
   q=D*p;ac=(a+c)%2
   eprod=sum(ch[n%D]*psi(n)*mp.exp(2j*mp.pi*n/q) for n in range(q))/(1j**ac*mp.sqrt(q))
   predicted=ch[p%D]*psi(D)*(-1)**(a*c)*ech*ep
   err=abs(eprod-predicted)
   assert err<mp.mpf('1e-43'),(disc,p,j,err)
   max_root_error=max(max_root_error,float(err));root_cases+=1
   if ch[p%D]==-1 and len(inert_phases)<10:
    kappa=ch[p%D]*psi(D)*(-1)**(a*c)*ech
    inert_phases.append({'disc':disc,'p':p,'character_index':j,'kappa_real':float(mp.re(kappa)),'kappa_imag':float(mp.im(kappa))})
out['exact_CRT_root_identity']={'cases':root_cases,'max_error':max_root_error,'inert_prime_examples':inert_phases,'status':'PASS'}

kernel_checks=0;max_kernel_error=0.0
kernel_cache={}
for p in [3,5,7,11,13,17]:
 chars=prime_chars(p)
 E={x:cmath.exp(2j*math.pi*x/p) for x in range(1,p)}
 kl=dict(E);kls={}
 for depth in range(2,5):
  nxt={x:0j for x in range(1,p)}
  for x,v in kl.items():
   for y,e in E.items():nxt[x*y%p]+=v*e
  kl=nxt
  if depth in [2,4]:kls[depth]=dict(kl)
 for a in [0,1]:
  for h in [0,1,2]:
   for x in range(p):
    for y in range(p):
     direct=sum(eps**(2*h)*vals[x]*vals[y].conjugate() for j,aa,vals,eps in chars if aa==a)
     if not x or not y: formula=0j
     elif h==0: formula=(p-1)/2*((x-y)%p==0)+(-1)**a*(p-1)/2*((x+y)%p==0)-(a==0)
     else:
      ratio=y*pow(x,-1,p)%p
      formula=(-1)**(a*h)*(p-1)/(2*p**h)*(kls[2*h][ratio]+(-1)**a*kls[2*h][-ratio%p])-(p**(-h) if a==0 else 0)
     err=abs(direct-formula);assert err<2e-10,(p,a,h,x,y,err)
     max_kernel_error=max(max_kernel_error,err);kernel_checks+=1
     kernel_cache[p,a,h,x,y]=direct
out['ordinary_and_Gauss_weighted_kernels']={'checks':kernel_checks,'max_error':max_kernel_error,'even_principal_correction':'Included as -p^(-h) for h>0','status':'PASS'}

cross_checks=0;max_cross_error=0.0
branches=[(0,0),(0,1),(1,0),(1,1)]
crosses=[((0,1),(0,0)),((1,0),(0,0)),((1,1),(0,0)),((1,0),(0,1)),((1,1),(0,1)),((1,1),(1,0))]
for disc in [-3,5,8]:
 D,ch=chi_table(disc);c=0 if ch[-1]==1 else 1
 tau=sum(ch[n]*cmath.exp(2j*math.pi*n/D) for n in range(D));ech=tau/(1j**c*math.sqrt(D))
 beta=[.017j,-.023j,.031j]
 def nu(n,sgn):return sum(cmath.exp(-sgn*beta[0]*math.log(d))*ch[(n//d)%D] for d in divisors(n))
 def d23(n,sgn):return sum(cmath.exp(-sgn*beta[1]*math.log(d)-sgn*beta[2]*math.log(n//d)) for d in divisors(n))
 def ups(n):return sum(int(mobius(d))*int(mobius(n//d))*ch[(n//d)%D] for d in divisors(n))
 weights={}
 for i,j in branches:
  weights[i,j]=[(d,m,n,ups(d)*nu(m,1 if i==0 else -1)*d23(n,1 if j==0 else -1)*cmath.exp(-.2*(d+m+n)+1j*(.31*d+.2*m-.17*n+.23*i+.11*j))) for d in range(1,5) for m in range(1,4) for n in range(1,4)]
 for p in [11,13]:
  if p<=D:continue
  chars=prime_chars(p)
  for a in [0,1]:
   eta=(-1)**(a*c)*ech
   B={}
   for idx,aa,vals,eps in chars:
    if aa!=a:continue
    for i,j in branches:
     B[idx,i,j]=sum(w*vals[d%p]*(vals[m%p] if i==0 else vals[m%p].conjugate())*(vals[n%p] if j==0 else vals[n%p].conjugate()) for d,m,n,w in weights[i,j])
    om=eps**2;kap=ch[p%D]*vals[D%p]*eta
    values=[B[idx,0,0],om*B[idx,0,1],kap*om*B[idx,1,0],kap*om**2*B[idx,1,1]]
    expanded=sum(abs(v)**2 for v in values)+2*sum((values[ii]*values[jj].conjugate()).real for ii in range(4) for jj in range(ii))
    assert abs(abs(sum(values))**2-expanded)<1e-9
   for (i,j),(ip,jp) in crosses:
    delta=i-ip;h=i+j-ip-jp
    lhs=sum((ch[p%D]*vals[D%p]*eta)**delta*eps**(2*h)*B[idx,i,j]*B[idx,ip,jp].conjugate() for idx,aa,vals,eps in chars if aa==a)
    rhs=0j
    for d,m,n,w in weights[i,j]:
     for e,mm,nn,ww in weights[ip,jp]:
      x=d*m**(1-i)*n**(1-j)*mm**ip*nn**jp
      y=e*m**i*n**j*mm**(1-ip)*nn**(1-jp)
      kval=kernel_cache[p,a,h,(D**delta*x)%p,y%p]
      rhs+=(ch[p%D]*eta)**delta*w*ww.conjugate()*kval
    err=abs(lhs-rhs);assert err<2e-9,(disc,p,a,i,j,ip,jp,err)
    max_cross_error=max(max_cross_error,err);cross_checks+=1
out['all_six_signed_cross_orientations']={'cases':cross_checks,'max_error':max_cross_error,'individual_duals_conjugated':False,'weights':'Common finite complex weights including actual nu/d23 orientations; algebra diagnostic only','status':'PASS'}

def bump(x):return math.exp(1-1/(1-16*x*x)) if abs(x)<.25 else 0.0
M=17.4;R=3.1;S=2.5;X=4
Jr=list(range(math.floor(R)+1,math.floor(M)+1));Js=list(range(math.floor(S)+1,math.floor(M)+1));Jm=list(range(1,math.floor(M)+1))
phi=lambda js,x:sum(bump(x-j) for j in js)
mask_checks=0;power_checks=0
for d in range(1,8):
 for m in range(1,19):
  for n in range(1,19):
   value=(d<=X)*phi(Jr,d*m)*phi(Js,n)*phi(Jm,d*m*n)
   desired=int(d<=X and d*m>R and n>S and d*m*n<=M)
   assert value==desired
   mask_checks+=1
   if d<=4 and m<=4 and n<=4:
    z=.03+.2j;s=.5+4.7j;w1=.1+.13j;w2=.3-.27j;w0=.2+.07j
    u1=s+z+w1+w0;u2=s+z+w2+w0
    lhs=cmath.exp(z*math.log(d)-(s+z)*math.log(d*m*n)-w1*math.log(d*m)-w2*math.log(n)-w0*math.log(d*m*n))
    rhs=cmath.exp((z-u1)*math.log(d)-u1*math.log(m)-u2*math.log(n))
    assert abs(lhs-rhs)<1e-12
    power_checks+=1
out['literal_integer_cell_masks']={'checks':mask_checks,'Mellin_power_checks':power_checks,'status':'PASS'}

adjacent_checks=0
for q1 in range(2,31):
 for q2 in range(2,31):
  for J in range(4,400):
   available=[j for j in range(J-3,J+1) if (j+1)%q1 and (j+1)%q2]
   assert available
   adjacent_checks+=1
tiny=mp.mpf('1e-35');near_ratio=-mp.exp(1j*tiny)
near_value=1+near_ratio
assert 0<abs(near_value)<2*tiny
out['four_adjacent_geometric_exponents']={'exact_divisibility_cases':adjacent_checks,'near_root_value_magnitude':float(abs(near_value)),'uniform_positive_lower_bound_claimed':False,'status':'PASS'}

arith_witness=[]
phase_identity_checks=0
for disc in [5,8,12,13]:
 D,ch=chi_table(disc);L=mp.log(D);B=L**9;ell=min(factorint(D+1));J=int(mp.floor(B/mp.log(ell)))
 alpha=mp.pi/B;c0=mp.mpf('.1')
 beta1=1j*alpha*(1-5*c0*alpha*L)
 beta2=2j*alpha*(1+c0*alpha*L)
 beta3=3j*alpha*(1-c0*alpha*L)
 def geom(a,b,j):return (a**(j+1)-b**(j+1))/(a-b) if abs(a-b)>mp.mpf('1e-45') else (j+1)*a**j
 candidates=[]
 for j in range(J-3,J+1):
  nuv=geom(mp.exp(beta1*mp.log(ell)),mp.mpf(ch[ell%D]),j)
  dv=geom(mp.exp(-beta2*mp.log(ell)),mp.exp(-beta3*mp.log(ell)),j)
  candidates.append((abs(nuv*dv),j,nuv,dv))
 mag,j,nuv,dv=max(candidates,key=lambda t:t[0]);assert mag>0
 logn=j*mp.log(ell)
 assert logn>B-8*L and logn>B-14*L
 assert logn<=B
 assert L+2*logn<=2*B+5*L
 factor=mp.exp(beta1*L)*(nuv*dv)**2
 assert abs(factor)>0
 V=nuv*dv;chin=ch[ell%D]**j
 assert abs(mp.conj(V)-chin*mp.exp(2*beta2*logn)*V)<mp.mpf('1e-35')*max(1,abs(V))
 assert abs(V**2-chin*mp.exp(-2*beta2*logn)*abs(V)**2)<mp.mpf('1e-35')*max(1,abs(V)**2)
 phase_identity_checks+=2
 arith_witness.append({'D':D,'ell':int(ell),'j':j,'log_n_over_log_P':float(logn/B),'arithmetic_factor_nonzero':True})
out['actual_shift_arithmetic_row_witness']=arith_witness
out['literal_shift_relation_arithmetic_phase']={'checks':phase_identity_checks,'beta3_equals_beta1_plus_beta2':True,'status':'PASS'}

stationary_checks=0
for D in [3,5,8,12]:
 for d,e,m,n,mm,nn in [(1,1,D*7,7,7,7),(2,3,5,7,11,13),(3,2,17,5,7,11)]:
  alpha=mp.mpf('.01');T=mp.mpf('17.3');u=mp.mpf('.5')+alpha+1j*T
  powers=mp.power(d,alpha-u)*mp.power(e,alpha-mp.conj(u))*mp.power(m,-(1-u))*mp.power(n,-u)*mp.power(mm,-mp.conj(u))*mp.power(nn,-(1-mp.conj(u)))*mp.power(D,mp.mpf('.5')-u)
  phase=mp.exp(1j*T*mp.log(mp.mpf(e)*m*mm/(mp.mpf(D)*d*n*nn)))
  assert abs(powers/abs(powers)-phase)<mp.mpf('1e-45')
  if e*m*mm==D*d*n*nn:assert abs(phase-1)<mp.mpf('1e-45')
  stationary_checks+=1
out['exact_extracted_conductor_Dirichlet_phase']={'checks':stationary_checks,'remaining_gamma_weight_oscillation_not_estimated':True,'status':'PASS'}

derivative=[]
for D,c in [(3,1),(5,0)]:
 for a in [0,1]:
  for T in [100,1000]:
   alpha=mp.mpf('.01');u=mp.mpf('.5')+alpha+1j*T
   bs=[.013j,.021j,.031j]
   def gamma_der(pairs):return -1j/2*sum(mp.digamma((1-u-b+aa)/2)+mp.digamma((u+b+aa)/2) for b,aa in pairs)
   err=gamma_der([(bs[0],a),(0,(a+c)%2)])-gamma_der([(bs[1],a),(bs[2],a)])
   assert abs(err)*T<10
   derivative.append({'D':D,'a':a,'T':T,'T_times_gamma_derivative_difference':float(abs(err)*T)})
out['nonconstant_scalar_ratio']=derivative

out['status']='PASS'
(HERE/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
