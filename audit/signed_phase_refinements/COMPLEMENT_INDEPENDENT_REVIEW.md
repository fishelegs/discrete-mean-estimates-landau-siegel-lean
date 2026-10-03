# Independent review of the actual long-complement extension

2026-10-03. **ACCEPT at source level, with the precise scope below.** The fixed-power extension of the actual sparse square tail, arbitrary-length source sieve, actual-u refinement, all-frequency boundary comparison, and completed-right contour identity are valid deductions from the stated source inputs. The new aggregate comparison error is

    O(a^-1 L^(-187/4)) + O(a^-1 P^-10) + O(exp(-c L^10)).

This is not a strict signed gain, an evaluation of either surviving main, a proof of Z2-min, or a Lean acceptance claim. The independent open target is still

    Re(J_right^infinity + Delta_long) <= (1-epsilon)m_H + o(1)

for a fixed epsilon>0. The new completed right integral is essential. It cannot be replaced by the old power-small right integral.

Candidate: `COMPLEMENT_PROOF.md`, SHA256 `da3091adfc403c1f5951a41d4334e8e6205c4416b2bf7c292fe8abf8c7894b02`. I independently checked the candidate manifest against the actual input bytes, reopened the source statements used for the two new arithmetic deductions, and reconstructed the candidate's twelve exact checks. The frozen interface has its unchanged SHA256 `3cba7904b89c904326406849fefb6f102a6f96625a7d7230b7dba9ccf8e4a530`. Repository HEAD is `ae8003c332174819f097e728ea1532b7340c758f`.

The acceptance is relative to the already independently accepted finite T3 bridge and source contour attachments, at their stated source-level scope.

## 1. Unchanged objects and exact signs

Keep `(A): L(1,chi)<L^-2022`, the separate final exponent 2024, the actual primitive real chi of either parity, the original prime window, actual good family Psi1, actual branch, actual compatible shifts, first R5 bump, and actual normalization. In particular,

    L=log D, B=log P=L^9, X=D^20,
    a>1/2, Mcal>=P^2/(4 L^77).

All contours use the inherited actual finite height cuts and their already paid endpoint treatment. The exact original core remains the two simultaneous frozen inequalities. Only its exact complement is refined and repartitioned.

With the source convention `power_gamma(n)=n^(-gamma)`, write

    eta^vee = mu*power_(-beta3),
    nu = 1*chi,
    c_X = eta^vee*nu_[1,X],
    c_inf = chi*power_(-beta3),
    E_X = c_X-c_inf = -eta^vee*(nu 1_(e>X)).

The last minus sign is correct. Ramified coefficients remain in this identity. In an ordinary C_psi conjugate(D_psi) pairing the D coefficient is conjugate(c), so the main D coefficient is `chi*power_(+beta3)`. It is not copied with the reflected shift.

The actual outer coefficient is

    Ahat(u)=sum_(dm=u,d<=X,D not dividing d) upsilon(d)h(m).

Its deletion stays on d. The mask phi(u/V) is a common bounded coefficient mask. Neither a full upsilon inverse identity nor the refinement permits deleting the d cutoff, ramified deletion, or either profile mask.

## 2. Actual square tail through every fixed P power

I reopened `Lemma31LinearTail.lean`, `Lemma31TotalWeight.lean`, and `Lemma31WeightedTail.lean`. Their relevant statements genuinely have arbitrary integer endpoint Y. The tail theorem is not confined to floor(P^2) before normalization.

For Y>=D^2 they give

    T(Y):=sum_(D^2<e<=Y)nu(e)/e
         <= L(1,chi)(1+log Y)+18 D^-1/2,

    sum_(e<=D^2)nu(e)/e <=9 L^2,

    sum_(D^4<e<=Y)nu(e)^2/e <=2 T(Y) U(Y),
    U(Y):=sum_(e<=Y)nu(e)/e.

Fix a real c>=2 before taking D sufficiently large. For Y<=P^c, L>=1 and the already available eventual absorption D^-1/2<=L^-2013 give

    1+log Y <=1+c L^9 <=(c+1)L^9,
    T(Y)<=(c+19)L^-2013,
    U(Y)<=9L^2+(c+19)L^-2013 <=(c+28)L^2.

Thus the candidate's bound is valid:

    sum_(D^4<e<=floor(P^c))nu(e)^2/e
          <=2(c+19)(c+28)L^-2011.

The constants are 1260 for c=2 and 1472 for c=4. If an endpoint is below D^2 or D^4, the relevant nonnegative tail is empty; the same eventual statement follows directly. Nothing here strengthens (A) or inserts a D power into the final constant.

Every retained original finite n support lies below P^4 eventually. For example, the original common label condition gives NRS<=8P^3.0008 and hence n<=2N<=16P^3.0008, since R,S>=1. This is <=P^4 eventually. Consequently all e indices occurring in the finite E_X coefficient have e<=P^4, even when e>P^2.

Coefficient Cauchy and tau2(qe)<=tau2(q)tau2(e) yield

    E(E_X phi_N)
      <= [sum_(q<=P^4)|eta(q)|^2 tau2(q)/q]
         [sum_(X<e<=P^4)nu(e)^2 tau2(e)/e].

The first bracket is O(L^72), since |eta|<=tau2 and tau2^3<=tau8. Cauchy bounds the second bracket by

    (sum_(X<e<=P^4)nu(e)^2/e)^(1/2)
    (sum_(e<=P^4)nu(e)^2 tau2(e)^2/e)^(1/2)
       << L^(-2011/2) L^72 = L^(-1867/2).

Here X>D^4 and nu^2 tau2^2<=tau16 include ramification. Therefore the extended error energy is exactly

    E(E_X phi_N) << L^(-1723/2).

The fixed exponent 4 affects only the constant. This deduction gives coefficient energy; it does not itself remove a long-polynomial sieve cost.

## 3. The arbitrary-length sieve preserves the actual family

I reopened `Lemma33.lean`, `Lemma33AdditiveLargeSieve.lean`, and `Lemma33ActualSamples.lean`. The first reduction from the actual primitive family to additive samples permits every integer polynomial length Y. The additive theorem has a free positive real parameter, with conditions

    Y<=P_eff^2,
    sample separation >=(8P_eff^2)^-1.

The actual samples are in [0,1] and are separated by (8P^2)^-1 once L>=3. Put P_eff^2=max(P^2,Y). Then P_eff>=1, the length condition holds, and the original spacing is stronger than the requested spacing. The additive index set is unchanged. This proves

    sum_(actual primitive family)|sum_(n<=Y)b(n)psi(n)|^2
      <=(32+pi^2)max(P^2,Y) sum_(n<=Y)|b(n)|^2.

This is not an assertion about primes near P_eff. It uses the actual original samples with a weaker spacing parameter. Shared coefficients can depend on the fixed D, fixed chi, t, and Mellin parameters, but not on the varying p or psi.

Cauchy on the actual good subset, followed by extension only of nonnegative square sums, now gives

    |sum_(Psi1)lambda C_psi conjugate(D_psi)|
      <<P^2 G(Y_C,Y_D) sqrt(E(C)E(D)),

    G(Y_C,Y_D)=sqrt(max(1,Y_C/P^2)max(1,Y_D/P^2)),
    |lambda|<=1.

No signed bad-family subtraction or conjugation closure enters this step. The factor G is necessary and is retained throughout the candidate.

## 4. Common actual-u refinement and constant-ratio localization

Insert sum_V phi(u/V)=1 only in the exact original complement. Ahat_V has the same support restrictions and envelope tau3. The additional dyadic label count is O(log P)=O(L^9).

For z=N R S M/V, the support has

    z/32 <= n r v m/u <=32z.

The factor 32 is exact for four dyadic numerator variables and one denominator variable. A refined support retained by intersection with [Qstar/4,4Qstar], where Qstar=D P^3(T0/(2pi))^3, has

    Qstar/128 <=z<=128Qstar.

Since Q_p(t)/Qstar lies between 1/2 and 2 eventually, a discarded support has x/Q_p(t)<=1/2 throughout or x/Q_p(t)>=2 throughout. This remains uniform at the inherited finite horizontal cuts. The selection depends on common labels only, not p, psi, or individual summands.

The scalar localization is valid. All these discarded refined pieces are already finite. Their kernel is analytic on the high rectangle extending to sigma=1/2 +/- A log P for any fixed A. The inherited gamma/branch estimate there is, up to a bounded factor,

    sqrt(x)(x/Q_p(t))^(sigma-1/2)|omega(s)|.

For the low-ratio side shift to the right; for the high-ratio side shift to the left. The vertical gain is at least P^(-A log 2). The number of terms, divisor envelopes, actual finite lengths, and label count have a fixed P-power bound. Choose A after that bound and the required K=10. This pays O(a^-1 P^-10).

There is no unaccounted horizontal exp(C(log P)^2) loss: along each outward horizontal path the ratio factor is at most its central value. Uniform Stirling remains valid because (A log P)^2/T0=o(1). The Gaussian real-part correction is exp(O((A log P)^2/L^800))=O(1), while the actual endpoint decay is exp(-cL^10). All finite polynomial costs are absorbed into that endpoint decay. The same argument applies to c_X, c_inf, and their difference, each with a fixed divisor envelope.

This argument must not be applied to the original infinite high tail from the central line. That tail was already summed starting on sigma=-1/2 against a summable divisor-weighted n^-3/2 majorant. The candidate preserves that order.

The natural real dual scales satisfy

    H_R=64 P Tstar/R,
    H_S=64 P Tstar/S,
    H_M=64 D P Tstar/M,
    Y_C^0=2 V H_R H_S H_M,
    Y_D=2N.

Consequently

    Y_C^0/N =2*64^3 D P^3 Tstar^3/z
      <=256*64^3(2pi Tstar/T0)^3.

Since Tstar/T0<=5 eventually, the right side is an absolute fixed constant C0. This is the required whole-polynomial cancellation. It retains and then cancels D, the actual profile-scale ratio, and the outer U slack. It does not call D^20 or P^.0005 an absolute constant. Shell enlargements are accounted for separately next.

## 5. Every dual frequency shell, including subunit natural lengths

Use the exact Fourier identity and bounded Mellin total-variation result from the accepted finite T3 review. These retain both frequency signs and the entire symbol; no stationary-phase remainder is removed. For either sign and each fixed logarithmic derivative order,

    |(y d/dy)^j V_t^sigma(y)|
       <<_(j,A) t^(1/2-A)y^(1/2-A)

in the large-y region. The H-profile amplitudes have uniformly bounded fixed-order derivatives; the fixed bump width gives fixed constants, not a growing D or P factor. For pure factors t is replaced by t+Im beta_j, which is uniformly comparable and positive.

For H>=1 take the first finite range h<=H, then shells 2^j H<h<=2^(j+1)H. Floors are implicit when restricting positive integers. The first range uses the full symbol and its O(1) Mellin total variation. On a later shell the chosen constant 64 ensures y>=c 2^j in the large-y region uniformly across p and t. Insert a smooth cutoff equal to one above the common lower bound and zero below half it. Its definition is independent of p and psi, so its Mellin measure is common across the family.

For completeness, put v(x)=Theta(e^x/Y)V_t^sigma(e^x), where the represented frequencies have y>=Y and Theta is zero at y<=Y/2. The large-y bounds, including two logarithmic derivatives, give

    ||v||_1+||v''||_1 <<_A t^(1/2-A)Y^(1/2-A).

Fourier inversion in x and the estimates on |xi|<=1 and |xi|>1 imply the same bound for Mellin total variation. The cutoff derivative terms satisfy the same estimate. Thus the shell measure has norm

    <<_A t^(1/2-A)2^(j(1/2-A)).

For H<1 take h<=1 first and shells 2^j<h<=2^(j+1) afterwards. Already h=1 has y>=c/H, so the first measure has norm

    <<_A t^(1/2-A) H^(A-1/2),

and subsequent shell norms acquire the same 2^(j(1/2-A)) factor. This case is not dropped or treated as having a zero-length polynomial.

Each triple of finite frequency ranges, signs, and Mellin parameters gives genuine finite polynomials with common coefficients. C has envelope tau6: the original tau3 coefficient and three unit-modulus dual factors. The actual finite lengths before arbitrary shell indices are in a fixed P-power range, including when H<1. Therefore

    E(C) << L^324(1+j_R+j_S+j_M)^36.

This follows from tau6^2<=tau36 and the harmonic divisor bound at the actual shell endpoint. It is a logarithmic energy bound at that endpoint, not an application of a P^2-only sieve to an infinite series.

If Y_C is enlarged by theta>=1, then

    G(theta Y_C,Y_D)<=theta^(1/2)G(Y_C,Y_D).

Consequently a dyadic shell contributes at most a fixed multiple of 2^(j(1-A)) after combining its Mellin norm with the sieve length cost. For H<1, replacing H by 1 costs at most H^-1/2 in G, leaving the compensating factor H^(A-1)<=1. The product of the three geometric shell weights sums against every fixed polynomial in j_R+j_S+j_M. A fixed A=21 is more than sufficient.

The sequence of limiting operations is sound: exact per-character Poisson; finite shell restrictions; Mellin inversion on each finite restriction; the finite arbitrary-length sieve; absolutely summable integrated shell-pairing bounds; then passage to the complete series. For each fixed D the original smooth Poisson series also converges absolutely and uniformly on the finite t interval. Thus the sum being estimated is the original full transformed expression. No infinite critical-line polynomial is fed to a finite sieve.

The zero frequency vanishes for each primitive nonprincipal completion. Negative frequencies contribute their exact parity factors and are retained. For parity a of psi and b of chi psi,

    epsilon_theta tau(conjugate theta)/sqrt(q)=i^parity,

so the exact three-root product is i^(2a+b), with further signs

    (-1)^(a 1_(sigma_R=-)+a 1_(sigma_S=-)+b 1_(sigma_M=-)).

The inherited gamma/branch scalar is still present with modulus one on the central line. These facts license the absolute comparison but supply no signed evaluation.

## 6. Normalized per-box and boundary budgets

The complete shell sum has the same base energy and sieve-length budget as the natural lengths. Combining Sections 2, 3, and 5, and then the actual Gaussian mass and prime-mass lower bound, gives

    |J_box(E_X)|
      <<(a Mcal)^-1 P^2 G(Y_C^0,2N) L^162 L^(-1723/4)
      <<a^-1 L^(-767/4) max(1,N/P^2).

The exponent identity is 77+162-1723/4=-767/4. The fixed C0 is absorbed only after the explicit cancellation in Section 4. No remaining factor Tstar, D, F, or profile width grows with D.

There are O(L^45) quintuples: the original four dyadic labels and the common u label. The label boundary 2N<=P^2 L^100 therefore gives total error

    O(a^-1 L^(-767/4+45+100))=O(a^-1 L^(-187/4)).

This uses L=log D. Replacing L^100 by (log P)^100 would add 900 rather than 100 and would destroy this saving. Every smooth box intersecting a pointwise threshold is retained whole according to its label; no sharp mask inside a Poisson factor is introduced.

The scalar discarded pieces retain their separate power and exponential payments. The accepted original core comparison is unchanged; its L^-623/4 error is smaller. Thus

    I_left^X = J_core^div + J_boundary^inf + J_long^X
         +O(a^-1 L^(-187/4))+O(a^-1 P^-10)+O(exp(-cL^10)).

This is an expansion of the region where the sparse replacement is valid. It is not a bound on the replaced main. With c_inf itself, this same absolute argument gives only O(a^-1 L^402) across the boundary. For N=P^(2+delta), the comparison cost after all quintuples is P^delta L^-587/4. No fixed logarithmic saving pays a fixed positive delta.

## 7. Completed-series holomorphy, orientation, and the new right term

On sigma=-1/2 define S_inf^dagger by its absolutely convergent product

    L(1-s,conjugate psi)L(1-s,chi conjugate psi).

Safe regrouping produces c_inf exactly. The same safe-line localization applies, now with the smaller tau2 envelope. Comparing the original X and infinity expressions uses the same frozen core and the same retained refined complement labels. The core and boundary comparisons are paid, so

    I_left^X-I_left^inf = Delta_long
       +O(a^-1 L^(-187/4))+O(a^-1 P^-10)+O(exp(-cL^10)),

    Delta_long=J_long^X-J_long^inf=sum_Long J_box(E_X).

The plus sign in I_left^X=I_left^inf+Delta_long+error follows from E_X=c_X-c_inf, despite E_X's negative convolution-tail representation.

The exact functional equations give Phi S_inf^dagger=L(s,psi)L(s,chi psi). Multiplying the original Ctilde cancels its L(s,psi) denominator, leaving precisely

    F_inf(s,psi)=-i B_beta(s)Z_psi(s)^-1
       M_psi(s)H_psi(s)H_psi^dagger(s)
       product_(j=1,2,3)L(s+beta_j,psi) L(s,chi psi) omega(s).

All four L functions are entire for these primitive nonprincipal characters. The original finite M and the two H polynomials are entire. The inherited branch and Z_psi^-1 are holomorphic and nonzero on this high rectangle; their possible gamma singularities lie outside it. The apparent quotient singularities at sampled L(s,psi) zeros are removable exactly. There is no remaining sampled residue, irrespective of the AFE.

The vertical edges are both oriented upward. Cauchy's theorem and the paid finite horizontal edges therefore give

    I_left^inf=J_right^inf+O(exp(-cL^10)),

not the negative of J_right^inf and not a vanishing individual left integral. Combining with the previous difference proves the candidate's AFE-free identity

    I_left^X=J_right^inf+Delta_long
       +O(a^-1 L^(-187/4))+O(a^-1 P^-10)+O(exp(-cL^10)).

The coefficient formula is also correct. With d_beta=chi*power_(beta1)*power_(beta2)*power_(beta3), on the safe right line

    J_right^inf=(a Mcal)^-1 sum_(Psi1) sum_(u,m,ell)
      Ahat(u)h(m)d_beta(ell)psi(ell u)conjugate(psi(m))/m
      (2pi i)^-1 integral_(sigma=3/2)
         [-i B_beta Z_psi^-1](m/(ell u))^s omega(s) ds.

The u,m sums are the actual finite ones; the ell series is absolutely convergent only on its safe line here. The signs of all three beta shifts are the forward-series signs. The scalar phase gives the degree-one resonance ell u/m approximately p t/(2pi), which is not excluded by support.

The old right estimate cannot be reused: its decaying Z_(chi psi) factor has been replaced by the growing Z_psi^-1. An independent absolute bound gives

    |Z_psi^-1|<<pT0,
    |M|<<1, |H|<<P^-0.251, |H^dagger|<<P^0.75375,
    |J_right^inf|<<a^-1 T0 P^(6011/4000).

This coarse bound is correct and is not evidence that the true right term is large. It only demonstrates that the old P^-0.49 bound is unavailable for this new object.

## 8. Global compensation and the remaining theorem

The original observable satisfies

    W_H=I_right^X-I_left^X+paid endpoints.

The accepted actual-zero AFE diagnoses Re W_H=-m_H+E_AFE, while the original I_right^X is O(a^-1 P^-0.49). It therefore diagnoses Re I_left^X=m_H+o(1). Substitution into the new, independently established contour identity yields

    Re(J_right^inf+Delta_long)=m_H
      +O(a^-1 L^-203)
      +O(sqrt(m_H/a)L^(-1077/4))
      +O(a^-1 P^-0.49)
      +O(a^-1 L^(-187/4))
      +O(a^-1 P^-10)+O(exp(-cL^10)).

The source a>1/2 and fixed positive m_H=lambda+o(1) make all these errors o(1). The AFE is used only for this diagnostic, never to prove the opposite strict bound.

Zero completed residue alone gives no independent value of either J_right^inf or Delta_long. In particular it does not force Re Delta_long=m_H+o(1), nor force the original left complement alone to supply the constant. Even before the new boundary bridge, the accepted finite core supports only the joint statement

    I_left^X=J_right^inf+(J_rest^X-J_rest^inf)
       +O(a^-1 L^(-623/4))+O(a^-1 P^-10)+O(exp(-cL^10)).

Any earlier wording that locates all compensation in the left complement must be read subject to this correction; it is not an accepted independent evaluation of that complement. The new report explicitly corrects this point without changing the accepted finite T3 theorem.

The remaining minimum proposition is a fixed strict gap for the joint signed expression, or its equivalent original/expanded split. Separate bounds with constants b,c and b+c<1 would suffice, but none has been proved. Arbitrary-length congruences, both parities, phases, and actual Psi1 remain substantive data. An eventual full-family argument would also need its actual Psi2 correction. Sparsity and nonnegative energy alone do not supply any of those signed conclusions.

## 9. Independent checks and trust boundary

The original `check_independent.py` reconstructs all twelve candidate arithmetic checks without importing a candidate checker. It also checks 420 exact rational inequalities governing shell length inflation and H<1 compensation, 1,203 prime-power divisor-envelope inequalities, 1,800 finite truncated-convolution sign identities, and all 32 parity/frequency-sign cases. It verifies all fourteen candidate-manifest input/output hashes, the specifically requested report hash, the frozen interface hash, and repository HEAD. All 27 check groups passed.

These exact finite checks corroborate algebra and bookkeeping only. They do not prove uniform analytic estimates, (A), an actual exceptional-character configuration, a transitive Lean axiom closure, or the missing signed gain. The analytic justification is in Sections 2–7 above and the previously accepted source inputs. The new source-level acceptance stops exactly at the displayed boundary comparison and AFE-free signed identity.


## Public evidence edition

The historical proof/review SHA256 identifiers are recorded in PROVENANCE.json. This copy removes local process descriptions and replaces workspace paths with public evidence references; the mathematical assertions and scope are retained. The portable checks separate exact arithmetic from historical provenance checks. See STATUS.md for the combined result and remaining signed gap. No Lean verification is claimed.

The portable arithmetic extraction `check_complement.py` prints 24 arithmetic groups. Historical source/HEAD checks account for the other three groups; their provenance is retained separately.
