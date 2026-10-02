# Independent exact interval certificate

## Arithmetic and π

The certifier uses only Python integers, fractions.Fraction for conversion, and
math.factorial. Every real interval has endpoints A/10^55,B/10^55 with integer
A,B. Addition and negation are exact; multiplication and division take extrema
of endpoint products/quotients, then round outward to the fixed lattice. Division
checks that its denominator interval excludes zero. Complex intervals are
rectangles made from two real intervals. Nothing numerical is rounded inward.

π is enclosed with Machin's exact identity
π=16 atan(1/5)−4 atan(1/239).
The alternating series use 50 and 15 terms respectively; the interval between
the partial sum and the partial sum plus its next signed term encloses each
arctangent. This is a mathematical identity/alternating-series reliance, not a
Lean proof. The output contains the exact π endpoints.

## Exponentials and integration

Every exponential is e^{iθ} or e^{iπa(t+s)}. Use the degree-80 Taylor polynomial.
For |θ|≤M<40, the exponential tail satisfies

Σ_{k=81}^∞ M^k/k! ≤ 2 M^81/81!,

because the ratio of successive terms is ≤M/82<1/2. The certifier asserts the
bound M<40. Each real and imaginary remainder is enclosed by the symmetric
interval with this rational bound. Linear exponentials are factored into a
constant phase and e^{iπat}; the latter's pointwise remainder on 0≤t≤end is
added as an interval in the constant coefficient. All original and reflected
arguments use explicit frequency/sign and phase, never a sampled quadrature.

The f,g,W1,W2 functions become polynomials with complex interval coefficients.
Their products are formed by exact interval convolution. The integrals are
coefficientwise antiderivatives evaluated at nonnegative rational endpoints.
The constant-coefficient remainder is a pointwise interval bound; the actual
error need not be constant. Since all monomials t^k are nonnegative on the
integration ranges, integrating the interval polynomial still bounds every
possible pointwise remainder. Products preserve pointwise inclusion.

The certificate includes full interval matrices for all twelve branches, along
with c1,c2,c3,Q. It verifies at the original coefficient vector that Q>.05 in
every branch. It also checks the printed-model cancellation defect and the Appendix B terminal-expression
model local cancellation norm<10^-5.

## Global minimum, without a floating-point optimization premise

For the Hermitian 4×4 model matrix M, reorder coordinates to
(iota2,iota3,iota4,first coefficient), i.e. original indices (1,2,3,0).
Perform the exact Hermitian LDL recurrence through interval arithmetic:

D_j=A_jj−Σ_{k<j} L_jk conj(L_jk) D_k,
L_ij=(A_ij−Σ_{k<j}L_ik conj(L_jk)D_k)/D_j.

Each computed diagonal's imaginary enclosure contains zero; the true diagonal
is real by Hermitian algebra. The code then uses its real enclosure. All four
pivot lower endpoints are checked positive. The first three pivots therefore
certify positive definiteness of the free 3×3 block N. Writing
M=[[m00,d*],[d,N]] in the original order gives exactly

z*Mz = (u+N^-1d)*N(u+N^-1d) + (m00−d*N^-1d),  z=(1,u).

The fourth reordered LDL pivot is the Schur complement m00−d*N^-1d. Its
computed interval bounds the **global** minimum over every u∈C³, not just a
stationary point or sampled search. Each branch's lower endpoint is >.024.
Thus Q<.001 is impossible in the specifically defined model with first
coefficient fixed to 1, regardless of the three other complex coefficients.
This is an elementary linear-algebra conclusion from the certified matrices.

For the `.5:exact:upstream` branch the first three pivots are approximately
1.32214926395, 3.52441721591, .0128935516269; the final pivot is
.02492942443909531277… . All exact outward bounds are in certified.json.

## What is and is not checked

This is a reproducible rational computer-assisted certificate, not a Lean kernel
certificate of the integrals or the mean-value formulas. Its trusted computation
base is Python integer arithmetic and the provided interval implementation; its
mathematical reductions are laid out above and in DERIVATION.md. The independent
mpmath quadrature code agrees but is not needed by the certificate.

No source epsilon is silently enlarged or set to an arbitrary value. The twelve
matrices are leading finite models. The source's fixed small epsilons and unknown
analytic bridges are not free optimization variables. The results neither prove
nor refute the Landau–Siegel theorem, and they make no infeasibility claim outside
this specified fixed-H11 family of models.
