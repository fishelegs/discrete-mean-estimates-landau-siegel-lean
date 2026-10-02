"""Fixed source profiles only. Diagnostic mpmath evaluation, not an interval certificate.
No candidate coefficient, cutoff, or frequency search is performed.
Bilinear model is rederived from Sections 8 and 10 contour residues;
Section 18 matrices are read-only frozen audit inputs, not arithmetic theorems.
"""
from pathlib import Path
import json
import mpmath as m
import sys
m.mp.dps=int(sys.argv[1]) if len(sys.argv)>1 else 70
R=m.mpf; I=m.j; pi=m.pi
DATA=Path(__file__).with_name('inputs')/'section18-quadrature.json'
frozen=json.loads(DATA.read_text())
class Ramp:
 def __init__(self,r,tau): self.r=R(r);self.tau=R(tau);self.breaks=[R(0),self.r]
 def conj(self): return Ramp(self.r,-self.tau)
 def vals(self,t):
  x=self.r-t
  if x<=0: return R(0),R(0),R(0)
  k=I*pi*self.tau; ex=m.exp(k*x)
  return x/self.r*ex,-ex/self.r-k*x/self.r*ex,(ex*(x/k-1/k**2)+1/k**2)/self.r
class Tent:
 def __init__(self,lo,h): self.lo=R(lo);self.h=R(h);self.hi=self.lo+self.h;self.mid=self.lo+self.h/2;self.breaks=[R(0),self.lo,self.mid,self.hi]
 def conj(self): return self
 def vals(self,t):
  if t<=self.lo: return R(0),R(0),self.h/2
  if t>=self.hi:return R(0),R(0),R(0)
  if t<self.mid:
   x=t-self.lo;return 2*x/self.h,2/self.h,self.h/2-x*x/self.h
  x=self.hi-t;return 2*x/self.h,-2/self.h,x*x/self.h
q=[R('.5'),R(2),R('1.5')]
def one(phi,psi):
 breaks=sorted(set(phi.breaks+psi.breaks))
 def integrand(t):
  v,d,w=phi.vals(t); u,e,x=psi.vals(t)
  return sum(q[j-1]*(-d-I*pi*j*v)*(-e+I*pi*(6-j)*u-pi*pi*[6,3,2][j-1]*x) for j in range(1,4))
 return m.quad(integrand,breaks)/pi
def mean(phi,psi):return one(phi,psi.conj())+m.conj(one(psi,phi.conj()))
def dec(x):return m.mpc(x['real'],x['imag'])
def enc(x):return {'real':m.nstr(m.re(x),55),'imag':m.nstr(m.im(x),55)}
phi=[Ramp('.504','1.5'),Ramp('.5','2.5'),Ramp('.498','1.5')]
w=Tent('.5','.004');wr=Tent('.496','.004')
checks={
 'c11':mean(phi[0],phi[0]),'c22':mean(phi[1],phi[1]),
 'c12':mean(phi[0],phi[1]),'c33':mean(phi[2],phi[2]),
 'c34_corrected':mean(phi[1],phi[2])}
errors={k:m.fabs(v-dec(frozen[k])) for k,v in checks.items() if k in frozen}
# c34 in the paper follows the H2 conjugate-coefficient convention.
errors['c34_corrected']=m.fabs(checks['c34_corrected']-dec(frozen['.5:exact_model:upstream_tail']['c34']))
L=m.matrix([mean(phi[0],w),mean(phi[1],w),mean(wr,phi[2]),mean(wr,phi[1])])
Rj=mean(w,w).real
Rformula=32/(pi*R('.004'))+88*pi*R('.004')/3
z=m.matrix([1,m.mpc('.94977','-1.38995'),m.mpc('-1.00635','-.22789'),m.mpc('-.68738','1.60688')])
ell=(L.T*z)[0]
out={'precision':m.mp.dps,'provenance':str(DATA),'note':'diagnostic only; no new arithmetic asymptotic claimed',
 'matching_diagonal_block_errors':{k:m.nstr(v,8)for k,v in errors.items()},'mixed_linear_functional':[enc(v)for v in L],
 'J_norm':enc(Rj),'J_norm_formula_error':m.nstr(abs(Rj-Rformula),8),'paper_mixed':enc(ell),'branches':{}}
for key,d in frozen.items():
 if not isinstance(d,dict) or 'matrix' not in d:continue
 M=m.matrix([[dec(v)for v in row]for row in d['matrix']])
 b=L.conjugate();y=m.lu_solve(M,b)
 maxratio=(L.T*y)[0].real/Rj
 paperQ=(z.transpose_conj()*M*z)[0].real
 out['branches'][key]={'paper_ratio':m.nstr(abs(ell)**2/(paperQ*Rj),55),'maximum_homogeneous_ratio':m.nstr(maxratio,55),
 'paper_Q':m.nstr(paperQ,55)}
print(json.dumps(out,indent=2))
assert max(errors.values())<m.mpf('1e-55')
assert abs(Rj-Rformula)<m.mpf('1e-55')
