"""Exact algebraic checks. No Lean, source imports, external numeric data, or arithmetic-mean claim."""
from pathlib import Path
import json
import sympy as S
x,t,s,r = S.symbols('x t s r', real=True)
I,pi=S.I,S.pi
rat=S.Rational
checks={}
def record(name, expr):
    z=S.simplify(S.expand(expr))
    assert z==0,(name,z)
    checks[name]='exact zero'
    print(name, flush=True)
def integral_poly(expr,var,lo=None,hi=None):
    prim=S.Poly(S.expand(expr),var).integrate().as_expr()
    return prim if lo is None else S.expand(prim.subs(var,hi)-prim.subs(var,lo))
def real(z):return S.expand_complex(S.expand(z)).as_real_imag()[0].expand()
def norm2(z):return S.expand(z*S.conjugate(z))
class Profile:
    def __init__(self, pieces):
        self.pieces=[(rat(a),rat(b),S.expand(p)) for a,b,p in pieces]
        self.breaks=sorted({S.Integer(0),S.Integer(1)}|{u for a,b,p in self.pieces for u in (a,b)})
    def val(self,z):
        for a,b,p in self.pieces:
            if a<=z<=b:return p.subs(x,z)
        return S.Integer(0)
    def poly(self,z):
        return next((p for a,b,p in self.pieces if a<z<b),S.Integer(0))
    def Wpoly(self,z):
        out=S.Integer(0)
        for a,b,p in self.pieces:
            if b<=z:continue
            primitive=integral_poly(p,x)
            out+=primitive.subs(x,b)-primitive.subs(x,a if z<a else x)
        return S.expand(out)
    def Wval(self,z):
        out=S.Integer(0)
        for a,b,p in self.pieces:
            if b<=z:continue
            out+=integral_poly(p,x,max(a,z),b)
        return out
    def reflconj(self):
        return Profile([(1-b,1-a,S.conjugate(p.subs(x,1-x))) for a,b,p in self.pieces])
    def scale(self,c):return Profile([(a,b,c*p) for a,b,p in self.pieces])
    def add(self,other):
        cuts=sorted(set(self.breaks+other.breaks))
        return Profile([(a,b,self.poly((a+b)/2)+other.poly((a+b)/2)) for a,b in zip(cuts,cuts[1:])])
def integ(f, profiles, cuts=None):
    cuts=sorted(set(sum([p.breaks for p in profiles],[])+(cuts or [])))
    ans=0
    for a,b in zip(cuts,cuts[1:]):
        mid=(a+b)/2
        ans+=integral_poly(f(mid),x,a,b)
    return S.expand(ans)
weights=[rat(1,2),2,rat(3,2)];ps=[6,3,2]
def Qsource(a):
    def density(mid):
        v,d,w=a.poly(mid),S.diff(a.poly(mid),x),a.Wpoly(mid)
        return sum(q*(-d-I*pi*j*v)*S.conjugate(-d-I*pi*(6-j)*v-pi**2*p*w) for j,q,p in zip((1,2,3),weights,ps))/pi
    return 2*real(integ(density,[a]))
def B(a,b):
    def density(mid):
        av,bv=a.poly(mid),b.poly(mid);ad,bd=S.diff(av,x),S.diff(bv,x)
        aw,bw=a.Wpoly(mid),b.Wpoly(mid)
        return 8/pi*ad*S.conjugate(bd)+24*I*(av*S.conjugate(bd)-ad*S.conjugate(bv))+88*pi*av*S.conjugate(bv)+24*I*pi**2*(av*S.conjugate(bw)-aw*S.conjugate(bv))
    return integ(density,[a,b])-12*pi*(a.val(0)*S.conjugate(b.Wval(0))+a.Wval(0)*S.conjugate(b.val(0)))
def Csource(a,b):
    lo=a.Wval(0)-a.Wval(rat(1,2)); mass=a.Wval(rat(1,2))
    base=-I*(sum(c*(a.val(0)-I*pi*j*lo)*(b.val(0)-I*pi*j*b.Wval(0)) for j,c in ((1,3),(2,3),(3,1)))+a.val(0)*b.val(0))
    cuts=sorted({rat(1,2),S.Integer(1)}|{c for c in a.breaks if c>rat(1,2)}|{1-c for c in b.breaks if c<rat(1,2)})
    out=base
    for l,u in zip(cuts,cuts[1:]):
        mid=(l+u)/2
        av=a.poly(mid);ad=S.diff(av,x);aw=a.Wpoly(mid)
        bp=b.poly(1-mid);bv=bp.subs(x,1-x);bd=S.diff(bp,x).subs(x,1-x);bw=b.Wpoly(1-mid).subs(x,1-x)
        den=sum(q*((-bd-I*pi*j*bv)*(ad+I*pi*(6-j)*av-pi**2*p*(mass-aw))+(-bd-I*pi*(6-j)*bv-pi**2*p*bw)*(ad+I*pi*j*av)) for j,q,p in zip((1,2,3),weights,ps))
        out+=integral_poly(den,x,l,u)/pi
    return S.expand(out)
def E(h):
    k=3*pi/2
    def density(mid):
        v=h.poly(mid);d=S.diff(v,x);w=h.Wpoly(mid)
        return 8/pi*(norm2(-d-2*I*k*v-k*k*w)-5*pi*pi/2*norm2(-v+I*k*w)+9*pi**4/16*norm2(w))
    f0=h.Wval(0);d0=-h.val(0)+I*k*f0;d1=I*h.val(1)
    return S.expand(integ(density,[h])-12*pi*real(d0*S.conjugate(f0))-16*real(d0*S.conjugate(d1)))

a=Profile([(0,rat(503,1000),(1+I*x)*(rat(503,1000)-x)**2)])
b=Profile([(0,rat(499,1000),(2-I+3*I*x)*(rat(499,1000)-x)**2)])
J=Profile([(rat(1,2),rat(251,500),500*(x-rat(1,2))),(rat(251,500),rat(63,125),500*(rat(63,125)-x))])
J2=J.reflconj();q=b.reflconj();h=a.add(q)
record('same_side_source_Q',Qsource(a)-B(a,a))
record('cross_gluing_with_tail',Csource(a,b)-(B(a,q)-8*I*a.val(0)*b.val(0)-12*pi*b.val(0)*a.Wval(0)))
record('reflected_Q',Qsource(q)-Qsource(b)-24*pi*real(b.val(0)*S.conjugate(b.Wval(0))))
record('joined_gauge',Qsource(a)+Qsource(b)+2*real(Csource(a,b))-E(h))
polar=(E(h.add(J))-E(h.add(J.scale(-1))))/4+I*(E(h.add(J.scale(I)))-E(h.add(J.scale(-I))))/4
record('mixed_orientation',polar-B(a,J)-B(J2,b))
record('target_R',Qsource(J)-(32/(pi*rat(1,250))+88*pi*rat(1,250)/3))
# Overlap cancellation is a separate, infinite-dimensional pair-space kernel.
bump=Profile([(rat(1,2),rat(63,125),(x-rat(1,2))**2*(rat(63,125)-x)**2*(1+I*x))])
cancel=bump.reflconj().scale(-1)
record('overlap_kernel',Qsource(bump)+Qsource(cancel)+2*real(Csource(bump,cancel)))
record('overlap_mixed',B(bump,J)+B(J2,cancel))
# Natural boundary conditions and differential equation for all three modes.
ks=[S.cos(pi*t/2),S.cos(3*pi*t/2),S.sin(pi*t/2)+S.sin(3*pi*t/2)]
for n,k in enumerate(ks,1):
    record(f'k{n}_ode',S.diff(k,t,4)+5*pi*pi/2*S.diff(k,t,2)+9*pi**4/16*k)
    record(f'k{n}_endpoint',k.subs(t,1))
    record(f'k{n}_right_natural',S.diff(k,t,2).subs(t,1)-pi*S.diff(k,t).subs(t,0))
    record(f'k{n}_left_natural_1',S.diff(k,t,2).subs(t,0)+3*pi*pi/4*k.subs(t,0)+pi*S.diff(k,t).subs(t,1))
    record(f'k{n}_left_natural_2',S.diff(k,t,3).subs(t,0)+7*pi*pi/4*S.diff(k,t).subs(t,0))
# The optional Hilbert-Schmidt proof needs only polynomial integration.
K0=lambda z:z-t-rat(1,2)
K1=lambda z:z-t+rat(1,2)
H=S.integrate(K0(s)*K0(r),(t,0,s))+S.integrate(K1(s)*K0(r),(t,s,r))+S.integrate(K1(s)*K1(r),(t,r,1))
record('periodic_covariance',H-((r-s)**2-(r-s)+rat(1,6))/2)
record('kernel_square_integral',2*S.integrate(S.integrate(S.expand(H**2),(s,0,r)),(r,0,1))-rat(1,720))
margin=S.factor(720-rat(25,4)*rat(22,7)**4)
assert margin>0
checks['sqrt720_gt_5pi2_over2_via_pi_lt_22_over7']=str(margin)
Path(__file__).with_name('exact-checks.json').write_text(json.dumps({'scope':'Exact symbolic algebra; not Lean or actual arithmetic means','checks':checks},indent=2)+'\n')
print(json.dumps({'passed':len(checks),'rational_square_margin':str(margin)},indent=2))
