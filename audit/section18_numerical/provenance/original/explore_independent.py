import mpmath as m
import json
m.mp.dps=70
R=m.mpf; I=m.j; pi=m.pi
r1=R('.504');r2=R('.5');r3=R('.498');h=R('.004')
q=[R('.5'),R(2),R('1.5')]
i2=R('.94977')-I*R('1.38995');i3=-R('1.00635')-I*R('.22789');i4=-R('.68738')+I*R('1.60688')
a=[0,R('1.5'),R('2.5')]
def f(j,k,z):
 return (1+I*pi*(a[k]-j)*z)*m.exp(I*pi*a[k]*z)
def g(j,k,z):
 # Literal source tables
 A=([R(8)/3,R(4)/3,R(8)/9] if k==1 else [R(24)/25,R(12)/25,R(8)/25])[j-1]
 B=([-R(5)/3,-R(1)/3,R(1)/9] if k==1 else [R(1)/25,R(13)/25,R(17)/25])[j-1]
 C=([-R(1)/2,R(1)/2,R(1)/6] if k==1 else [R(1)/10,R(3)/10,-R(3)/10])[j-1]
 return A+(B+I*pi*C*z)*m.exp(-I*pi*a[k]*z)
def b(k,l,shiftk,shiftl,end,den):
 return sum(q[j-1]*m.quad(lambda z:f(j,k,z+shiftk)*g(j,l,z+shiftl),[0,end]) for j in range(1,4))/(pi*den)
b11=b(1,1,0,0,r1,r1*r1); b22=b(2,2,0,0,r2,r2*r2)
b12=b(1,2,h,0,r2,r1*r2); b21=b(2,1,0,h,r2,r1*r2)
b33=b(1,1,0,0,r3,r3*r3)
c11=2*b11.real;c22=2*b22.real;c12=b12+m.conj(b21);c33=2*b33.real

def e(j,k):
 r=[0,r1,r2,r3][k];alpha=[0,R('1.5'),R('2.5'),R('1.5')][k]
 return (1-R(j)/alpha+R(j)/(alpha**2*r*pi*I))*m.exp(alpha*r*pi*I)-R(j)/(alpha**2*r*pi*I)

def ee(j):
 return R(j)/R('.756')*m.quad(lambda z:m.exp(R('1.5')*(r1-z)*pi*I)-m.exp(R('.75')*pi*I),[0,h])
bstar=m.quad(lambda z:z*m.exp(R('1.5')*pi*I*z),[0,h])/r1
E1=[-pi*bstar*sum([3,6,3][j-1]*m.quad(lambda z:f(j,k,r-z),[0,R('.496')])/r for j in range(1,4)) for k,r in [(1,r3),(2,r2)]]
E2=[4/(r1*pi)*(-R('.002')/r3),4/(r1*pi)*(-R('.008')-2*pi*I/R(250)**2)]
# High exact-phase model from differentiating source residue expression.
def W1(j,t):
 return m.exp(-R('1.5')*pi*I*t)*(-1+(R('1.5')-j)*pi*I*t)
def W2(j,t):
 u=R('1.5')*pi*I; p=-pi*pi*[6,3,2][j-1]; s=(6-j)*pi*I
 F=lambda z:m.exp(u*z)*(z/u-1/u**2)
 return m.exp(u*t)*(-1+(s-u)*t)+p*(F(h)-F(t))
EX=[]
for k,r,d in [(1,r3,R('.002')),(2,r2,h)]:
 aa=sum(q[j-1]*m.quad(lambda t:f(j,k,d-t)*W2(j,t),[0,d]) for j in range(1,4))/(r1*r*pi)
 bb=sum(q[j-1]*m.quad(lambda t:g(j,k,d-t)*W1(j,t),[0,d]) for j in range(1,4))/(r1*r*pi)
 EX.append(aa+m.conj(bb))

def matrix(denom,high='printed',cancel='full'):
 b34=b(2,1,R('.002'),0,r3,R(denom)*r3)
 b43=b(1,2,0,R('.002'),r3,R(denom)*r3)
 c34=b34+m.conj(b43)
 M=m.matrix(4);M[0,0]=c11;M[1,1]=c22;M[0,1]=m.conj(c12);M[1,0]=c12
 M[2,2]=c33;M[3,3]=c22;M[2,3]=m.conj(c34);M[3,2]=c34
 K=m.matrix(2)
 for u,ku in enumerate([1,2]):
  for v,kv in enumerate([3,2]):
   K[u,v]=-I*(sum(w*(e(j,ku)-((ee(j) if cancel=='full' else -I*pi*j*bstar) if u==0 and cancel!='collapsed' else 0))*e(j,kv) for j,w in [(1,3),(2,3),(3,1)])+m.exp(pi*I*[R('.756'),R('1.25')][u])*m.exp(pi*I*[R('.747'),R('1.25')][v]))
   if u==0: K[u,v]+=(E1[v] if cancel!='collapsed' else 0)+(2*E2[v] if high=='printed' else EX[v])
   M[v+2,u]=K[u,v];M[u,v+2]=m.conj(K[u,v])
 return M,K,c34

def enc(x):
 return {'real':m.nstr(m.re(x),60),'imag':m.nstr(m.im(x),60)}
res={'c11':enc(c11),'c22':enc(c22),'c12':enc(c12),'c33':enc(c33),'e1star_coeff':[enc(x) for x in E1],'e2star_coeff':[enc(x) for x in E2],'exact_high_coeff':[enc(x) for x in EX]}
z=m.matrix([1,i2,i3,i4])
for den in ['.504','.5']:
 for high in ['printed','exact_model']:
  for cancel in ['full','collapsed','upstream_tail']:
   M,K,c34=matrix(den,high,cancel)
   c1=(m.conj(z[0])*M[0,0]*z[0]+m.conj(z[0])*M[0,1]*z[1]+m.conj(z[1])*M[1,0]*z[0]+m.conj(z[1])*M[1,1]*z[1]).real
   c2=sum(m.conj(z[u])*M[u,v]*z[v] for u in [2,3] for v in [2,3]).real
   c3=sum(z[u]*m.conj(z[v+2])*K[u,v] for u in [0,1] for v in [0,1])
   vals,U=m.eighe(M)
   N=M[1:4,1:4];d=M[1:4,0:1];opt=-m.lu_solve(N,d);optz=m.matrix([1,*list(opt)]);Qopt=(optz.transpose_conj()*M*optz)[0].real
   key=f'{den}:{high}:{cancel}';res[key]={'c1':enc(c1),'c2':enc(c2),'c3':enc(c3),'total':enc(c1+c2+2*c3.real),'c34':enc(c34),'matrix':[[enc(M[u,v]) for v in range(4)]for u in range(4)],'eigenvalues':[enc(x) for x in vals],'free_submatrix_eigenvalues':[enc(x)for x in m.eighe(N)[0]],'formal_stationary_coefficients':[enc(x)for x in opt],'stationary_total':enc(Qopt)}
   print(key,'c2=',m.nstr(c2,20),'c3=',m.nstr(c3,20),'TOTAL=',m.nstr(c1+c2+2*c3.real,20),'eig=',[m.nstr(x,8)for x in vals],'stationary=',m.nstr(Qopt,15))
json.dump(res,open('/tmp/section18-quadratic-audit/exploratory.json','w'),indent=2)
