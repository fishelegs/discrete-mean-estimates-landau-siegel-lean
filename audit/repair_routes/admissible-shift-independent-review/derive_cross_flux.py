"""Formal pointwise gluing check using independent complex jet variables."""
import sympy as s

f,fb,q,qb,fp,fbp,qp,qbp,F,Fb,Q,Qb,m,mb,n,nb,c,cb=s.symbols(
    'f fb q qb fp fbp qp qbp F Fb Q Qb m mb n nb c cb')
b,S,P=s.symbols('b S P')
# b and S are imaginary; P is real. f=phi, q=conjugate-reflection psi.
# m=integral phi, n=integral q, c=integral_0^.5 phi.
high=(qbp-b*qb)*(fp+(S-b)*f+P*(m-c-F))+(fbp-b*fb)*(qp+(S-b)*q+P*(n-Q))
same=(-fp-b*f)*(-qbp+(S-b)*qb+P*Qb)+(-qp-b*q)*(-fbp+(S-b)*fb+P*Fb)
delta=s.expand(high-same)
flux=(S-2*b)*(f*qb+fb*q)+P*(-F*qb+Fb*q-Q*fb+Qb*f
    -b*(F*Qb+Fb*Q)+(m-c)*qb+n*fb+b*((m-c)*Qb+n*Fb))
deriv={f:fp,fb:fbp,q:qp,qb:qbp,F:-f,Fb:-fb,Q:-q,Qb:-qb}
dflux=sum(s.diff(flux,k)*v for k,v in deriv.items())
assert s.expand(delta-dflux)==0
f0,qb1,fmid,fbmid=s.symbols('f0 qb1 fmid fbmid')
k1=flux.subs({f:0,fb:0,F:0,Fb:0,Q:0,Qb:0,qb:qb1})
kmid=flux.subs({q:0,qb:0,Q:n,Qb:nb,f:fmid,fb:fbmid,F:m-c,Fb:mb-cb})
# The same-side cross term on the lower interval is P*nb*(-f'-b*f).
lower=P*nb*(-fmid+f0-b*c)
integrated_difference=s.factor(k1-kmid-lower)
expected=P*((m-c)*qb1-f0*nb+b*c*nb)
assert s.expand(integrated_difference-expected)==0

# Add low coupling -w*P/b*(f0-b*c)*(qb1-b*nb).
# Its discrepancy from the desired boundary is cancellation of the c term.
low_without_weight=-P/b*(f0-b*c)*(qb1-b*nb)
assert s.expand(integrated_difference+low_without_weight
                -(P*m*qb1-P/b*f0*qb1))==0
print('PASS: pointwise arbitrary-jet cross flux identity')
print('PASS: integrated high-minus-same plus low equals P*m*qb1-P/b*f0*qb1')
print('No profile samples, phase samples, or numerical approximations were used.')
