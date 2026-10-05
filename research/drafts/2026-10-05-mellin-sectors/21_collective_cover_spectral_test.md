# Collective outer levels: exact cover representation and the remaining spectral-sum bill

Draft research note dated 2026-10-05. Status: SOURCE_REVIEWED_BOUNDED_COLLECTIVE_COVER_AND_PROFILE_FLOOR_TEST_ONLY_NOT_LEAN. This proves an exact induced common-base representation and sharp bookkeeping for specified norm-bound methods. The spectral floor is for a defined nonnegative error-control quantity, with the H-scale conclusion conditional on the stated l1 profile norms. It is not a lower bound for the true spectral error or actual energy, and it supplies no new middle estimate or universal collective-method impossibility.

## Result

Two specified collective attempts can now be priced precisely.

1. The changing groups can be represented exactly on a common base group by induced finite-dimensional permutation representations. This avoids the enormous intersection group, but it does not turn the problem into the scalar common-group hypothesis of GM7.1. Orthogonally summing those representations duplicates the spectral/test vector. Optimizing every positive Cauchy weight returns exactly the old outer L1 sum of fixed-level error bounds; there is no automatic outer L2 gain.
2. GM Corollary8.3's THIRD, level-averaged clause does not repair that particular direct-sum/Cauchy argument at the actual favorable-cell scales. Its modulus-scale term is D times the plain-factor level count, and its explicit ||β||₁²Q_level/N remainder persists. More decisively, GM7.1 defines each Rβ with the nonnegative summand ||β||₁²/N. On changing levels N≈P t_c, this prevents a single-level-sized sum only under the stated lower bounds on the individual profile l1 norms. Those lower bounds are not asserted for the actual level-dependent masked family.

These are obstructions to the stated norm-bound routes, not lower bounds for the actual covariance or for the true error. A signed cross-level spectral identity, a new weighted Bessel estimate using the real outer coefficients, or a different representation could still improve the original arithmetic sum. No such estimate is proved here. The full-K near unequal middle and the original restricted principal subtraction remain OPEN.

## 1. Current source scope and actual target

The mathematical inputs are the source-reviewed actual averaged attachment in [note 18](18_averaged_determinant_attachment.md), the scoped common-level variance result in [note 19](19_common_level_outer_variance.md), the finite prime-Hecke interface in [note 17](17_prime_hecke_correlation.md), and the original [GM primary](https://arxiv.org/pdf/2404.08502v2). All are used only at their stated scopes.

The unchanged sufficient target concerns the collective full-K near unequal transformed square

    P²L^402<X_ij,Y_ij≤P²D^5,  |log(X_ij/Y_ij)|≤L^-395,

with original shifts, finite d,e≤D⁴, prime window, both parities, p-unit masks, full original weight, Gaussian and restricted even-principal subtraction. This note tests a genuine smooth generic cell of that target, using exactly the accepted current interface. No transformed-output condition is reinterpreted as an original-output cutoff.

Write t_c=2πL^519 and W=L^400. In this note only, put t₀=t_c for the scale notation (the time-parameter note instead uses t₀=L^519). Set

    U=P t₀, V=sqrt(D)U, x=UV=sqrt(D)U²,
    H=x/(PW).                                             (1)

Here U is the plain pair scale, V the mixed pair scale, and H the positive-difference determinant h-block in the effective Gaussian core. This is a favorable test with d=e=1; the other finite-inverse terms remain in the exact complement and are not assumed small. The actual reviewed attachment covers both determinant signs, but this favorable positive block already identifies the cost of the proposed collective shortcut.

For an outer tuple i=(a₃,a₄,b₃,b₄), set

    M_i=a₃a₄≈U, E_i=b₃b₄≈U, q₁,i=M_iE_i, q₂=D.

The four variables individually have scale sqrt(U). Keep the genuine generic conditions gcd(M_i,E_i)=gcd(M_iE_i,D)=1 and every remaining accepted determinant/primitive-column restriction. The periodic weight is

    α_i((A,B;C,F))=1_(M_i|A)1_(E_i|B)χ(CF),
    g=(M_i a₁, σE_i b₁; b₂,a₂), det g=ph.                 (2)

Its complex outer coefficients are the actual Mellin/beta monomials. Nothing below replaces them by independent or random coefficients.

The reviewed fixed-outer result has the error certificate

    E_i ≤ C_ε L^C x^ε x^-1/2 P sqrt(φ(D)N_p)
                                  [H U^-1/2+sqrt(H)],     (3)

after the exact common normalized carrier and cutoff separation. N_p is the actual original-window prime count in this generic sector. Its bound N_p≪P L^-68 enters only the accepted explicit finite-Hecke correlation. It is not substituted for a generic prime-sampled operator norm.

The common-level variance review's scope is respected: its lower bound concerns the explicit GM10.2 expression, not the kernel-weighted Kα of general GM7.1. This note does not promote that lower bound to a statement about general GM spectral compensation.

Every common-product-level determinant specialization must retain gcd(h,p q₁D)=1. This is stronger than the coprimality for each individual cell; the extra excluded h sectors remain a separate UNPAID contribution. Neither the induced-cover representation nor a change of scalar level silently removes them. Individual level-dependent restrictions remain in the actual operator throughout.

## 2. The actual normalized GM scales

Use the raw matrix scales

    A_raw≈U sqrt(V), C_raw≈F_raw≈sqrt(V),
    A_raw F_raw≈x, C_raw F_raw≈V.

Normalize by sqrt(HP)=sqrt(x/W). Denote the resulting GM7.1 coordinate scales by A,C,F, avoiding confusion with conductor D. Then

    A≈sqrt(UW), C≈F≈sqrt(W/U),
    AF≈W, CF≈W/U,
    q₁≈U², q=q₁D≈D U²,
    N=q₁ CF/(AF+1)≈U.                                   (4)

For the exact M_i,E_i rather than their comparable scales, N≈E_i, so replacing N by one common dyadic-comparable U requires only constant-factor comparisons in the positive decay weights. No factor equal to the number of levels is gained in that comparison.

The pointwise R2 arguments used by the accepted attachment are

    H CF/D≈t₀/sqrt(D),
    HN/q≈t₀/(W sqrt(D)).                                 (5)

Both tend to zero. After the determinant proof's h/Hecke decomposition, its pointwise nonnegative spectral bill is therefore of the form

    R_i≲Z^ε [||β||₂²+||β||₁²/U]
       ≲Z^ε [H+H²/U]                                    (6)

for the bounded determinant sequence of the actual smooth block. The coupling gcd(h,pq)=1 stays in the original operator, as in the accepted attachment; it is not absorbed into a fictitious common unrestricted sum.

The two terms of (6) produce respectively sqrt(H) and H/sqrt(U) in (3). In fact H/U≈sqrt(D)t₀/W eventually grows. The second term, corresponding to R0, is a genuine part of the available bound and cannot be ignored when looking for a collective gain.

## 3. A common-base representation that preserves all levels

Let

    Γ_D=Γ₂(1,D), Γ_i=Γ₂(q₁,i,D)⊂Γ_D.

In the generic sector (q₁,i,D)=1, CRT reduction gives

    I_i=[Γ_D:Γ_i]=q₁,i ∏_(ℓ|q₁,i)(1+1/ℓ).               (7)

Choose representatives ρ for the left cosets Γ_i\Γ_D. For a function f on Γ_i\G define the vector-valued function

    (U_i f)(g)_ρ=f(ρg).                                  (8)

Right multiplication of the coset labels by γ∈Γ_D is a permutation: if ργ=γ_iρ′, then f(ργg)=f(ρ′g). Thus (8) is equivariant for the finite-dimensional induced permutation representation of Γ_D on C[Γ_i\Γ_D]. It is NOT generally a scalar automorphic function for Γ_D with the original principal group character.

With counting measure in the fibre, the identity

    ∫_(Γ_D\G) Σ_ρ |f(ρg)|² dg
                    =∫_(Γ_i\G)|f(g)|² dg               (9)

is an exact isometry, obtained by partitioning a fundamental domain of the cover into those cosets. Poincare sums, original evaluations and the group-compatible Hecke operations can be transported by this isometry. For clarity, one may define the transported operator as U_i T_h^(i) U_i^-1 on its image; no equality with one common SCALAR Hecke operator is assumed.

This construction is a concrete alternative to the intersection cover. It preserves α_i, all actual test functions, determinant restrictions and outer phases. It does not erase the varying divisibility levels. It also shows where their information now lives: the representation and its fibre depend on i.

A normalized fibre average would divide the left side of (9) by I_i. To remain an isometry one must then multiply U_i by sqrt(I_i). Hence changing counting measure to probability measure is not a free level saving.

GM7.1 as printed concerns one scalar group character and one fixed group; it is not already a vector-valued cross-representation theorem for the direct sum of all (8). Applying it separately to the components and then summing is legitimate but returns to the existing method. A true vector-valued estimate would require its own kernel and spectral norm proof.

## 4. Exact obstruction to a direct-sum cheap-L2 argument

The issue can be stated independently of automorphic normalization. Suppose the component method supplies scalar errors E_i with bounds

    |E_i|≤C sqrt(K_i R_i),

where physical normalization and the common derivative envelope have been extracted. Keep the actual outer coefficients c_i. Orthogonal direct-sum Cauchy, with arbitrary positive balancing weights w_i, gives the certificate

    |Σ_i c_i E_i|
       ≤C [Σ_i w_i|c_i|²K_i]^(1/2)
             [Σ_i R_i/w_i]^(1/2).                       (10)

The optimal value over all positive w_i is EXACTLY

    inf_w [Σ_i w_i|c_i|²K_i]^(1/2)[Σ_i R_i/w_i]^(1/2)
                       =Σ_i |c_i|sqrt(K_i R_i).           (11)

Cauchy proves the lower inequality; equality follows by taking w_i proportional to sqrt(R_i)/(|c_i|sqrt(K_i)) on nonzero components, with limits for zero components. Thus no choice of direct-sum normalization or weights alone upgrades the existing outer L1 error summation to a cheap L2 sum.

Equation (11) is sharp for information consisting only of those component norm bounds: one-dimensional component vectors can have phases chosen to align all c_iE_i. This does NOT claim the actual errors align or that the actual coefficients are arbitrary. It proves that their real cross-level structure must enter a new estimate before those norm bounds can certify cancellation.

A proposed gain using one common test vector must prove that it really is common after the induced representations, level-dependent h-coprimality, actual test functions and evaluations are transported. Merely giving every component the same coefficient sequence β does not identify their automorphic spectra or Fourier vectors.

## 5. Testing the third clause of GM Corollary8.3

The primary PDF's printed page 43 was inspected directly, as well as its text. Let

    Q_lev≈D U², Q₁≈U², N≈U, CF≈W/U,

and use the principal automorphic character, whose conductor in this theorem is 1. The exceptional-spectrum term in its level average has size

    (CF Q₁)^(2θ) Q_lev^(1−4θ)
       ≈(WU)^(2θ)(D U²)^(1−4θ)
       ≤C D U²,                                         (12)

for every stated θ≥0 and all sufficiently large original parameters. Indeed its ratio to D U² is (W²/(D⁴U⁶))^θ≤1. Also N≪Q_lev.

A valid homogeneous estimate follows by applying the level-average clause only to a singleton sequence and first proving a homogeneous comparison. Let δ₁ denote the single coefficient at h=1. The defining Hecke sums and the uniform pointwise Hecke bound give, for every spectral representation,

    |Σ_h β_h λ_V(h)|≤C_ε H^(ϑ+ε)||β||₁.

The analogous continuous-spectrum bound also holds, by its explicit divisor formula. Applying this BEFORE the positive spectral sum and its maximum gives

    Rβ(q₁,q₂,N)≤C_ε H^(2ϑ+ε)||β||₁² Rδ₁(q₁,q₂,N).       (13a)

This includes the added norm term because H≥1. Apply the third clause only to δ₁, where every coefficient norm equals 1 and its support parameter can be taken to be 1. At (4),(12), including its Q_lev/N term, this yields the valid collective certificate

    Σ_(levels) Rβ≲x^ε D U² H^(2ϑ)||β||₁²
                       ≲x^ε D U² H^(2+2ϑ).              (13b)

This is worse than the pointwise R2 comparison below. For an even more favorable applicability test, GRANT a hypothetical level-average certificate with only one factor ||β||₁ in the first term and the explicit quadratic remainder retained. Its ledger would be

    ≲Z^ε [||β||₁ H^(2ϑ)D U²+||β||₁²D U]
       ≲Z^ε D[H^(1+2ϑ)U²+H²U].                         (13c)

The subsequent no-gain comparison already holds for that more favorable ledger; it does not require (13c) to be a valid theorem for arbitrary β. The unambiguous definition, the reviewed R2 application, and the singleton level-average clause suffice for all proved claims here.

By contrast, summing the already applicable pointwise R2 bound over a full dyadic collection of about U² levels yields

    ≲Z^ε[U²H+UH²].                                     (14)

Even with ϑ=0, the favorable level-average ledger (13c) is not smaller than (14). The scale in the printed formula is Q_lev=D U², not the number of selected levels in our q₂=D slice. Restricting its nonnegative left side to that slice does not license division of the right side by D. Such a sparse-level refinement would be a new theorem. Even hypothetically granting that division, the resulting bound at ϑ=0 merely has the same U²H+UH² scale as (14), rather than saving a power of P.

Repeated levels require additional care. Different outer tuples can have the same product q₁. Their exact multiplicity is a restricted four-divisor coefficient, and their phases and actual weights remain. The unweighted third clause is not a theorem for this weighted multiplicity. Ignoring repetitions is a favorable comparison, not a valid payment for them. A max-divisor bound would introduce another cost; a weighted cross-level estimate would require proof.

All Z^ε or x^ε losses remain power losses with fixed ε; they are not silently relabeled as fixed powers of L.

## 6. An unavoidable term in this particular spectral certificate

There is a sharper reason that this route cannot manufacture a single-level-sized spectral sum. GM7.1 defines its spectral quantity as two nonnegative spectral pieces PLUS

    ||β||₁²/N.

Thus, independently of any spectral large sieve or Ramanujan estimate,

    Rβ(q₁,i,D,N_i)≥||β||₁²/N_i.                          (15)

Suppose the selected normalized profiles on an interval of size H satisfy uniform lower bounds ||β_i||₁≥cH, and N_i≈U. This is a profile hypothesis, not an established fact about the actual level-dependent masked family. The original coprimality restriction remains in the operator; if extra masks are absorbed into β_i, their l1 norms must be checked afresh. Under exactly these lower-bound hypotheses one obtains

    Σ_(i∈I) Rβ(q₁,i,D,N_i)≥c |I| H²/U.                  (16)

With level-dependent profiles β_i, the exact statement is Σ_i R_(β_i)(q₁,i,D,N_i)≥Σ_i||β_i||₁²/N_i. The |I|H²/U conclusion requires uniform lower bounds ||β_i||₁≥cH and N_i≈U. It is not universal under an altered mask or reparameterization; absorbing extra coprimality into β_i requires rechecking these norms and the common representation. This is a lower bound for the defined NONNEGATIVE CERTIFICATE, not for a spectral error or the arithmetic target. It remains true with exact tuple repetitions. In the determinant proof the auxiliary m-sum contains the m=1 term, so passing to that decomposition does not remove this particular obligation.

Under those profile hypotheses, retaining these Rβ definitions and taking componentwise/direct-sum Cauchy cannot obtain the desired common-vector compensation by showing Σ_iRβ has only single-level size. A different representation, an estimate before this nonnegative majorization, a signed cross-level identity, or a revised proof that removes or reorganizes the added norm term is needed.

With the actual accepted correlation bound, ordinary Cauchy over J components gives a certificate proportional to

    x^-1/2 P sqrt(φ(D)N_p) sqrt(J)
                         [Σ_i R_i]^(1/2).

Substituting (6) gives J times the fixed-outer certificate (3). Substituting either (13b) or the more favorable (13c) supplies no improvement. Therefore the actual reviewed outer-count ledger remains

    x^ε L^C [P³D^(1/2)L^804+P³D^(3/4)L^(1727/2)].        (17)

This is an upper-bound ledger of the specified method, never an actual-energy lower bound. Optimistically granting an outer square-root-count gain would still leave positive D powers from the fixed-outer normalization; such a hypothetical gain alone would not complete the full logarithmic target either.

## 7. Concrete missing collective input and stopping point

The cover construction (8) is an exact way to keep the changing levels without the intersection-group product. What is absent is a weighted cross-representation estimate for the actual sum, prior to replacing it by (10). Such an estimate must preserve the actual outer Mellin/beta coefficients, the joint carrier/cutoff weights, finite d,e, level-dependent gcd restrictions, original p-unit masks, both determinant signs and the restricted original principal subtraction.

The primary level-average clause controls a sum of separate nonnegative spectral quantities. It does not give the needed signed cross-level covariance or identify the induced fibres. Its printed range, modulus scale, repeated-level multiplicities, and explicit floor term have all been kept visible here.

This bounded attempt stops at that precise gate. It neither claims a new collective energy estimate nor rules out other collective GM7.1 uses or a compensating spectral construction. All complements of the favorable generic cell remain part of the original target. No new Lean certificate or final-gap conclusion is made.

## 8. Primary references and verification scope

- [Grimmelt–Merikoski, arXiv:2404.08502v2](https://arxiv.org/pdf/2404.08502v2): Theorem 7.1's defined nonnegative R_beta, Corollary 8.3 at the singleton sequence, and the determinant proof's normalized coefficients
- [Actual averaged attachment](18_averaged_determinant_attachment.md) and [scoped common-level variance](19_common_level_outer_variance.md)
- [Selected source identities](SOURCE_PINS.json), [finite diagnostics](diagnostics/README.md) and [read-only verifier](verify_checkpoint.py)

Only the exact induced cover/isometry, optimized Cauchy identity, singleton-derived homogeneous comparison, actual scale ledger and conditional profile floor are accepted here. Equation (13c) is an explicitly favorable hypothetical ledger, not a general-beta theorem. The floor bounds the defined R_beta certificate only. Any common-product-level specialization retains gcd(h,p q₁D)=1, with additional excluded h sectors separately UNPAID. No conditional profile lower bound is promoted to a fact about the actual masked family. No actual error or energy lower bound, complete collective application, new middle bound or impossibility theorem follows. Primary papers and raw review text are not redistributed.
