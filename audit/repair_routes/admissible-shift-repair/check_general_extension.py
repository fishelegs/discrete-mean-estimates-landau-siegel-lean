import sympy as s
from pathlib import Path
I=s.I
x,y,u,v=s.symbols('x y u v');z=x+y;A=2*z;T=x*y+x*z+y*z;R=x*y*z
conj=lambda f:s.cancel(s.conjugate(f).subs({s.conjugate(x):x,s.conjugate(y):y,s.conjugate(u):1/u,s.conjugate(v):1/v}))
w=[x*v/(y*(y-x)),-y*u/(x*(y-x)),z/(x*y)]
C=s.factor(sum(w)+sum(map(conj,w)));X=s.factor(-w[0]*y*z-w[1]*x*z-w[2]*x*y)
V=s.factor(((w[0]-conj(w[0]))*y+(w[1]-conj(w[1]))*x)/(2*I))
D=I*(u*v-1-z*(v-u)/(y-x));imW=s.factor((sum(w)-sum(map(conj,w)))/(2*I))
e0=s.Matrix([[1,0,0]]);e1=s.Matrix([[0,1,0]]);em=s.Matrix([[0,0,1]])
cm=lambda m:m.applyfunc(conj)
out=lambda a,b:cm(a).T*b
bd=-2*V*(out(e0,e0)+out(e1,e1))-R*imW*out(em,em)
bd+=X*out(em,e0)+conj(X)*out(e0,em)+X*out(e1,em)+conj(X)*out(em,e1)+D*out(e1,e0)+conj(D)*out(e0,e1)
lam=[0,x,y,z];ph=[1,1/u,1/v,1/(u*v)]
j0=lambda k:s.Matrix([[(-I*l)**k for l in lam]]) if k else s.ones(1,4)
j1=lambda k:s.Matrix([[(-I*l)**k*ph[j] for j,l in enumerate(lam)]]) if k else s.Matrix([ph])
mat=s.Matrix.vstack(j0(0),j0(1),j1(0),j1(1))
det=s.factor(mat.det()); print('det=',det,flush=True); print('det/C=',s.factor(det/C),flush=True)
sol=mat.inv()*s.Matrix.vstack(s.zeros(1,3),-e1,em,-e0);sol=sol.applyfunc(s.factor)
U0=[(j0(k)*sol).applyfunc(s.factor) for k in range(4)];U1=[(j1(k)*sol).applyfunc(s.factor) for k in range(4)]
def boundary(U):
 q,qp,qpp,qppp=U
 return out(qp,qpp+I*A/2*qp)+out(q,-qppp-I*A*qpp+T*qp+I*R/2*q)
ext=boundary(U1)-boundary(U0); ext=(ext+cm(ext).T)/2
checks=[]
for r in range(3):
 for c in range(3):
  d=s.simplify(s.factor(bd[r,c]-C*ext[r,c]));print(r,c,d,flush=True);assert d==0;checks.append((r,c))
Path(__file__).with_name('general-extension-checks.json').write_text(__import__('json').dumps({'exact_rational_phase_identity':'PASS','entries_checked':checks,'determinant_over_C':str(s.factor(det/C)),'scope':'Algebraic extension identity only; periodic PSD is proved in DERIVATION.md, actual mean attachments are not established'},indent=2)+'\n')
