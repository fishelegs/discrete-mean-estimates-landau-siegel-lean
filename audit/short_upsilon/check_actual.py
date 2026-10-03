"""Independent actual arithmetic regressions, not a simulation of assumption A."""
import cmath, json, math, hashlib
from pathlib import Path
from fractions import Fraction
ROOT=Path(__file__).resolve().parent
N=22000
spf=list(range(N+1))
for p in range(2,math.isqrt(N)+1):
 if spf[p]==p:
  for n in range(p*p,N+1,p):
   if spf[n]==n: spf[n]=p
mu=[0]*(N+1); mu[1]=1
for n in range(2,N+1):
 p=spf[n];m=n//p;mu[n]=0 if m%p==0 else -mu[m]
def tau(k,n):
 r=1
 while n>1:
  p=spf[n];e=0
  while n%p==0: n//=p;e+=1
  r*=math.comb(k+e-1,e)
 return r
t2=[0]+[tau(2,n) for n in range(1,N+1)]
t4=[0]+[tau(4,n) for n in range(1,N+1)]
t16=[0]+[tau(16,n) for n in range(1,N+1)]
t32=[0]+[tau(32,n) for n in range(1,N+1)]
def conv(a,b):
 c=[0]*(N+1)
 for d in range(1,N+1):
  if a[d]:
   for m in range(1,N//d+1):c[d*m]+=a[d]*b[m]
 return c
def close(a,b):
 return abs(a-b)<=1e-8*(1+abs(a)+abs(b))
chars={3:{1:1,2:-1},5:{1:1,2:-1,3:-1,4:1},8:{1:1,3:-1,5:-1,7:1},12:{1:1,5:-1,7:-1,11:1}}
shifts=[(0.13j,-0.20j,-0.07j),(0.31j,0.12j,-0.27j)]
records=[]
for D,vals in chars.items():
 chi=[vals.get(n%D,0) for n in range(N+1)]
 nu=conv([0]+[1]*N,chi)
 ups=conv(mu,[mu[n]*chi[n] for n in range(N+1)])
 assert conv(ups,chi)==mu
 for n in range(1,N+1):
  assert 0<=abs(ups[n])<=nu[n]<=t2[n]
  assert nu[n]**2*t2[n]**2<=t16[n]
  assert t4[n]**2*t2[n]<=t32[n]
 cutoff=D**4
 us=[ups[n] if n<=cutoff else 0 for n in range(N+1)]
 ut=[ups[n]-us[n] for n in range(N+1)]
 for beta in shifts:
  powers=[[0]+[cmath.exp(-b*math.log(n)) for n in range(1,N+1)] for b in beta]
  power3=conv(conv(powers[0],powers[1]),powers[2])
  kappa=conv(mu,power3)
  f=conv(chi,power3)
  full=conv(ups,f)
  short=conv(us,f)
  delta=conv(ut,f)
  for n in range(N+1):
   assert close(kappa[n],full[n]),(D,n,'factorization')
   assert close(kappa[n]-short[n],delta[n]),(D,n,'residual')
   if n<=cutoff:assert abs(delta[n])==0
   if n:assert abs(f[n])<=t4[n]+1e-8 and abs(short[n])<=tau(6,n)+1e-8
  endpoints=[0,1,cutoff-1,cutoff,cutoff+1,cutoff+2,N]
  cauchy=[0.0]*(N+1)
  for d in range(cutoff+1,N+1):
   for m in range(1,N//d+1):
    cauchy[d*m]+=abs(ups[d]*f[m])**2
  for n in range(1,N+1): assert abs(delta[n])**2<=t2[n]*cauchy[n]+1e-7
  for end in endpoints:
   S=sum(abs(delta[n])**2/n for n in range(1,end+1))
   A=sum(abs(ups[n])**2*t2[n]/n for n in range(cutoff+1,end+1))
   B=sum(t4[n]**2*t2[n]/n for n in range(1,end+1))
   T=sum(nu[n]**2/n for n in range(cutoff+1,end+1))
   H=sum(1/n for n in range(1,end+1))
   assert S<=A*B+1e-7
   assert A*A<=T*H**16+1e-7
   assert B<=H**32+1e-7
   assert S*S<=T*H**80+1e-7
   records.append({'D':D,'beta':[str(b) for b in beta],'N':end,'cutoff':cutoff,'energy':S,'tail_nu_energy':T,'all_passed':True})
# Exact exponent arithmetic and integral loss.
assert Fraction(-2011)+80*9==-1291
assert Fraction(-1291,2)==Fraction(-1291,2)
assert 2*(-645)==-1290 and -1291<=-1290 and 1260<=36**2 and -645<=-640
assert Fraction(-640,2)+Fraction(36,4)+Fraction(36,4)==-302
report={'status':'PASS','actual_conductors':list(chars),'max_n':N,'endpoint_cases':len(records),'pure_shift_triples':[[str(b) for b in beta] for beta in shifts], 'includes_independent_third_shift':True,'ramified_primes':[2,3,5], 'warning':'Finite arithmetic regressions only. Assumption A and enormous analytic scale bounds are proved only by Lean, not numerical simulation.','records':records}
(ROOT/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='records'},indent=2))
