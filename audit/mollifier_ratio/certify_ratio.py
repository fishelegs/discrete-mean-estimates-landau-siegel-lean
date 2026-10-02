"""Bound the full homogeneous ratio in all twelve frozen finite models by 1/2.
Stdlib rational intervals only. No parameter or coefficient search.
This does not prove the arithmetic character-sum-to-model bridges.
"""
from interval_engine import R,C,P,t,pi,explin,Z,ONE,ii,S
from fractions import Fraction as F
from pathlib import Path
import json, hashlib
ROOT=Path(__file__).with_name('inputs')
source=ROOT/'section18-certified.json';data=json.loads(source.read_text())
def loadR(d):
 assert d['scale']=='1e55'
 return R.raw(int(d['lo']),int(d['hi']))
def loadC(d):return C(loadR(d['real']),loadR(d['imag']))
def ramp(r,tau):return ('ramp',F(r),F(tau))
def tent(lo,h):return ('tent',F(lo),F(h))
def breaks(p):return [F(0),p[1]] if p[0]=='ramp' else [F(0),p[1],p[1]+p[2]/2,p[1]+p[2]]
def conjugate(p):return ramp(p[1],-p[2])if p[0]=='ramp'else p
def values(p,mid,end):
 if p[0]=='ramp':
  r,tau=p[1:]
  if mid>=r:return P([0]),P([0]),P([0])
  x=r-t;k=C(0,pi*tau);ex=explin(-tau,-r,end=end);v=x*ex/r
  return v,-ex/r-v*k,(ex*(x/k-ONE/(k*k))+ONE/(k*k))/r
 lo,h=p[1:];hi=lo+h
 if mid<=lo:return P([0]),P([0]),P([h/2])
 if mid>=hi:return P([0]),P([0]),P([0])
 if mid<lo+h/2:
  x=t-lo;return x*(2/h),P([2/h]),P([h/2])-x*x/h
 x=hi-t;return x*(2/h),P([-2/h]),x*x/h
q=[F(1,2),F(2),F(3,2)]
def one(p,s):
 bs=sorted(set(breaks(p)+breaks(s)));ans=Z
 for lo,hi in zip(bs,bs[1:]):
  mid=(lo+hi)/2;v,d,w=values(p,mid,hi);u,e,x=values(s,mid,hi)
  poly=P([0])
  for j in range(1,4):
   a=-d-v*C(0,pi*j)
   b=-e+u*C(0,pi*(6-j))-x*C(pi*pi*[6,3,2][j-1])
   poly=poly+a*b*q[j-1]
  ans=ans+poly.integral(hi)-poly.integral(lo)
 return ans/C(pi)
def mean(p,s):return one(p,conjugate(s))+one(s,conjugate(p)).conj()
phis=[ramp('.504','1.5'),ramp('.5','2.5'),ramp('.498','1.5')]
w=tent('.5','.004');wr=tent('.496','.004')
ell=[mean(phis[0],w),mean(phis[1],w),mean(wr,phis[2]),mean(wr,phis[1])]
Rmodel=mean(w,w)
Rclosed=32/(pi*R('.004'))+88*pi*R('.004')/3
assert Rmodel.r.lo<=Rclosed.hi and Rclosed.lo<=Rmodel.r.hi
assert Rmodel.i.lo<=0<=Rmodel.i.hi
# Use the exact closed form and its directed interval in the block certificate.
Rj=Rclosed
checks={'c11':mean(phis[0],phis[0]),'c22':mean(phis[1],phis[1]),'c12':mean(phis[0],phis[1]),'c33':mean(phis[2],phis[2])}
for k,v in checks.items():
 old=loadC(data[k]) if k=='c12' else C(loadR(data[k]))
 assert v.r.lo<=old.r.hi and old.r.lo<=v.r.hi
 assert v.i.lo<=old.i.hi and old.i.lo<=v.i.hi
# True LDL Hermitian decomposition with interval arithmetic. Positive pivots
# certify every exact matrix contained in these entry enclosures, subject to
# the mathematically established Hermitian equalities.
def ldl(A):
 n=len(A);L=[[Z for _ in range(n)]for _ in range(n)];D=[]
 for j in range(n):
  dj=A[j][j]-sum((L[j][k]*L[j][k].conj()*C(D[k])for k in range(j)),Z)
  assert dj.i.lo<=0<=dj.i.hi
  assert dj.r.lo>0
  D.append(dj.r);L[j][j]=ONE
  for i in range(j+1,n):
   L[i][j]=(A[i][j]-sum((L[i][k]*L[j][k].conj()*C(D[k])for k in range(j)),Z))/C(D[j])
 return D
out={'method':'rational directed intervals; scale1e55; degree80 exponential Taylor bounds; positive augmented Hermitian LDL',
 'scope':'finite models only; no new character-mean asymptotic or main theorem',
 'matrix_input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'ell':[v.dump()for v in ell],'J_norm_exact_expression':'32/(pi*h)+88*pi*h/3, h=1/250','J_norm':Rj.dump(),
 'J_norm_from_residue_integral':Rmodel.dump(),'branches':{}}
for name,d in data.items():
 if not isinstance(d,dict) or 'matrix'not in d:continue
 M=[[loadC(v)for v in row]for row in d['matrix']]
 # Block A=[ M,conj(ell); ell^T,Rj/2 ]. Positive definiteness means
 # Rj/2-ell^T M^-1 conj(ell)>0, so max |ell^T z|²/(Rj z*M z)<1/2.
 A=[M[j]+[ell[j].conj()]for j in range(4)]+[ell+[C(Rj/2)]]
 D=ldl(A)
 ratio=R('.5')-D[-1]/Rj
 out['branches'][name]={'augmented_LDL_pivots':[v.dump()for v in D],
   'maximum_ratio':ratio.dump(),'claim':'maximum_ratio < 1/2'}
 assert ratio.hi<R('.5').lo
 print(name,'max ratio',ratio.show(20),'last pivot',D[-1].show(10),flush=True)
# Containment of independently derived quadrature at 70 and100 digits.
for fname in ['ratio-70.json','ratio-100.json']:
 diag=json.loads(Path(__file__).with_name(fname).read_text())
 def contains(iv,num):
  num=F(num);assert F(iv.lo,S)<=num<=F(iv.hi,S)
 for v,wit in zip(ell,diag['mixed_linear_functional']):
  contains(v.r,wit['real']);contains(v.i,wit['imag'])
 contains(Rj,diag['J_norm']['real'])
 for name,d in out['branches'].items():
  den,hi,tail=name.split(':');dkey=':'.join([den,'exact_model'if hi=='exact'else hi,{'printed':'full','upstream':'upstream_tail','collapsed':'collapsed'}[tail]])
  contains(loadR(d['maximum_ratio']),diag['branches'][dkey]['maximum_homogeneous_ratio'])
Path(__file__).with_name('ratio-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: all12 finite-model homogeneous maxima are below1/2; both independent quadrature runs contained')
