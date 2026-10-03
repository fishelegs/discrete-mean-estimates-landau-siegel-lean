import sympy as s,json
from pathlib import Path
n,m=s.symbols('n m',real=True)
P=n*(n-s.Rational(1,2))*(n-s.Rational(9,4))*(n-s.Rational(11,4))
claims=[('L2',P-s.Rational(9,64)*n*n),('H1',P-s.Rational(5,288)*n**4)]
result={}
for name,F in claims:
 vals=[s.factor(F.subs(n,k)) for k in (1,2,3)]
 assert all(v>=0 for v in vals)
 tail={}
 for label,sub in [('n>=4',m+4),('n<=-1',-m-1)]:
  pol=s.Poly(s.expand(F.subs(n,sub)),m)
  assert all(c>0 for c in pol.all_coeffs())
  tail[label]=str(pol.as_expr())
 result[name]={'n_1_2_3':list(map(str,vals)),'positive_coefficient_tails':tail}
pi=s.pi
for k,expected in [(2,[160,16,32]),(3,[448,s.Rational(64,3),32]),(4,[1152,32,s.Rational(128,3)])]:
 C0=4*(k+1)/(k*pi) if k%2 else 4*k/((k-1)*pi)
 beta=s.simplify(2*C0*pi*s.diag((2*k+1)*k*(k-1),k-1,k))
 assert beta==s.diag(*expected)
 result['beta_k'+str(k)]=str(beta)
Path(__file__).with_name('spectral-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: both all-integer coercivity bounds, and exact beta matrices k=2,3,4')
