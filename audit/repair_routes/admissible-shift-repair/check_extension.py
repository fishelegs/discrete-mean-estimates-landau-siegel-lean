import sympy as s
I=s.I; pi=s.pi
for theta in [(s.Rational(1,2),s.Rational(9,4),s.Rational(11,4)),(1,3,4),(1,4,5),(1,2,3)]:
 a=[pi*s.Rational(t) for t in theta]; x,y,z=a;A=sum(a);T=x*y+x*z+y*z;R=x*y*z
 w=[s.simplify(a[j]*s.expand_complex(s.exp(I*(z-a[j])))/s.prod(a[k]-a[j] for k in range(3) if k!=j)) for j in range(3)]
 C=s.simplify(2*s.re(sum(w))); X=s.simplify(sum(-w[j]*s.prod(a[k] for k in range(3) if k!=j) for j in range(3))); V=s.simplify(sum(s.im(w[j])*(A/2-a[j]) for j in range(3)))
 D=s.simplify(I*s.expand_complex(s.exp(I*z))-sum(I*w[j]*s.prod(a[k] for k in range(3) if k!=j)/a[j] for j in range(3)))
 e0=s.Matrix([[1,0,0]]);e1=s.Matrix([[0,1,0]]);em=s.Matrix([[0,0,1]])
 out=lambda u,v:s.conjugate(u).T*v
 # z^* matrix z convention: z=(h0,h1,M), 2Re X h0barM
 bd=-2*V*(out(e0,e0)+out(e1,e1))-R*s.im(sum(w))*out(em,em)
 bd+=X*out(em,e0)+s.conjugate(X)*out(e0,em)+X*out(e1,em)+s.conjugate(X)*out(em,e1)+D*out(e1,e0)+s.conjugate(D)*out(e0,e1)
 lam=[s.Integer(0),x,y,z]; phase=[s.expand_complex(s.exp(-I*l)) for l in lam]
 jet0=lambda k:s.Matrix([[(-I*l)**k for l in lam]]) if k else s.ones(1,4)
 jet1=lambda k:s.Matrix([[(-I*l)**k*phase[j] for j,l in enumerate(lam)]]) if k else s.Matrix([phase])
 mat=s.Matrix.vstack(jet0(0),jet0(1),jet1(0),jet1(1))
 rhs=s.Matrix.vstack(s.zeros(1,3),-e1,em,-e0)
 sol=s.simplify(mat.inv()*rhs)
 ub0=[s.simplify(jet0(k)*sol) for k in range(4)];ub1=[s.simplify(jet1(k)*sol) for k in range(4)]
 def boundary(U):
  u,up,upp,uppp=U
  return out(up,upp+I*A/2*up)+out(u,-uppp-I*A*upp+T*up+I*R/2*u)
 ext=boundary(ub1)-boundary(ub0);ext=s.simplify((ext+s.conjugate(ext).T)/2)
 diff=s.simplify(s.expand_complex(bd-C*ext))
 print('theta',theta,'C',C,'diff',diff,flush=True)
 assert diff==s.zeros(3),diff
