# Independent review of the square-factor positive tail

2026-10-04. **SOURCE ONLY.** Independent mathematical verdict: **ACCEPT**, for the strict tail and the resulting two-smooth-completion HB sectors stated below. This is not a compiler result and does not prove the global strict half-norm gap.

The principal improvement is valid. Moreover, Pólya–Vinogradov is unnecessary: the already available asymmetric hyperbola estimate gives a stronger error without its logarithm. The entire argument below is universal; finite tests are supplementary.

## 1. Exact statement and scope

Let χ be the actual primitive real Dirichlet character of conductor D>1, let ν=1*χ, L=log D, log P=L^9, and retain the original assumption

    0 ≤ L(1,χ) ≤ C_A L^-2022,

where C_A is the original fixed constant (C_A=1 in the normalized form). For each integer 1≤q≤9, let r=2q and K=max(0,q(q−3)/2). Let τ_k=1^{*k}, including τ_0=δ_1, and define SqLift(τ_K)(h²)=τ_K(h), with value zero on nonsquares. Then

    ν(n)² τ_q(n) ≤ (ν^{*r} * SqLift(τ_K))(n)                 (1)

for every positive integer n. For every real Z≤P^4, the strict tail satisfies

    Σ_(D^20<n≤Z) ν(n)²τ_q(n)/n
      ≪_(q,C_A) L^(4q−2015)
         + D^-1/40 L^(4q−2) + D^-1/4 L^(4q).              (2)

For sufficiently large D, uniformly in the actual χ,

    Σ_(D^20<n≤Z) ν(n)²τ_q(n)/n ≪_(q,C_A) L^(4q−2015).    (3)

The sum is zero if Z≤D^20. The full conductor, zero character values, non-squarefree D, and the strict lower endpoint are all retained. Primitivity ensures nonprincipality when D>1; the analytic proof below actually needs only a nonprincipal character with period D. No Siegel lower bound, Burgess bound, or new hypothesis is introduced.

## 2. Universal local proof of (1)

For k≥1, τ_k(p^v)=binom(v+k−1,k−1), and τ_0(p^v) is 1 for v=0 and zero otherwise. All functions in (1) are nonnegative and multiplicative, including SqLift, so it suffices to prove every prime-power inequality.

Two combinatorial inequalities used here have universal proofs:

* τ_a(p^v)τ_b(p^v)≤τ_(ab)(p^v). A pair of weak compositions of v into a and b parts specifies row and column sums of a nonnegative integral a×b matrix. Such a matrix exists by the elementary greedy transportation construction. Choosing one deterministically injects the pairs into the matrices, since row and column sums recover the pair. There are τ_(ab)(p^v) such matrices.
* τ_q(p^(2v))≤τ_(q(q+1)/2)(p^v). A weak q-composition of 2v is a degree sequence of an undirected multigraph on q labeled vertices, allowing loops and repeated edges. Pair the 2v stubs in any deterministic order; a loop contributes degree two. Thus the map from multisets of v edges of the q(q+1)/2 possible types onto these degree sequences is surjective. Counting gives the inequality. This includes v=0 and q=1.

At a split prime χ(p)=1, ν(p^v)=v+1=τ_2(p^v), while ν^{*r}(p^v)=τ_(2r)(p^v). Applying the first inequality twice gives

    ν(p^v)²τ_q(p^v) ≤ τ_(4q)(p^v)=ν^{*(2q)}(p^v).

The h=1 summand of the square convolution already supplies this bound; its other summands are nonnegative.

At an inert prime χ(p)=−1, ν(p^v) is one at even v and zero at odd v. The local generating series of the right side of (1) is

    (1−T²)^−(2q+K).

Both sides are zero at odd valuations. At valuation 2v, its coefficient is τ_(2q+K)(p^v). For q≤3, 2q≥q(q+1)/2, and for q≥3 the equality 2q+K=q(q+1)/2 holds. The second combinatorial inequality and monotonicity in the divisor order prove the claim.

At a ramified prime χ(p)=0, ν(p^v)=1, and the h=1 summand gives τ_(2q)(p^v)≥τ_q(p^v). No unit assumption at p is imposed, and no ramified factor is deleted.

This proves (1), in fact for every integer q≥1. The restriction q≤9 enters only in the later tail threshold. For q=1,2,3, K=0 means exactly SqLift(δ_1)=δ_1; there is no unwanted square multiplicity.

## 3. A complete analytic input without PV

Put S(t)=Σ_(1≤n≤t)χ(n). Nonprincipality makes the sum over one complete period zero, hence |S(t)|≤D. The complete-period identity follows by choosing a unit a with χ(a)≠1 and permuting the residues by multiplication by a. For every interval, the difference of two initial sums is bounded by 2D. Abel summation therefore gives convergence at s=1 and

    |Σ_(n>Y)χ(n)/n|≤2D/Y                                 (4)

for integers Y≥1. The limit is L(1,χ).

For integers N≥D and 1≤Y≤N, write

    A(N)=Σ_(n≤N)ν(n)=Σ_(b≤N)χ(b) floor(N/b).

For b≤Y, replacing floor(N/b) by N/b costs at most Y. For b>Y, interchange the finite summation:

    Σ_(b>Y)χ(b)floor(N/b)
      =Σ_(a≤N/(Y+1)) Σ_(Y<b≤N/a)χ(b),

whose absolute value is at most 2DN/Y. Equation (4) bounds the omitted harmonic main term by another 2DN/Y. Consequently

    |A(N)−N L(1,χ)|≤Y+4DN/Y.

Choose Y=ceil(sqrt(DN)). Since D≤N, this integer lies in [1,N], with Y≤2sqrt(DN) and DN/Y≤sqrt(DN). Hence

    |A(N)−N L(1,χ)|≤6sqrt(DN).                           (5)

The Euler-factor formula above proves ν≥0; letting N→∞ in (5) proves L(1,χ)≥0 without an extra analytic positivity assumption. For real x≥D, N=floor x satisfies N≥D, so

    A(x)≤x L(1,χ)+6sqrt(Dx).                             (6)

This source argument is also present in `ZhangLS/Spec/Lemma31HyperbolaInputs.lean`, `ZhangLS/Spec/Lemma31HyperbolaError.lean` and `ZhangLS/Spec/Lemma31CumulativeBound.lean`. The arbitrary-endpoint upper-tail statement is in `ZhangLS/Spec/Lemma31LinearTail.lean`. These repository paths are pinned in [INPUTS.json](INPUTS.json). Those sources are supporting provenance, not unproved additional assumptions in this review.

For real z≥y≥D, Stieltjes/Abel summation with A(t)=Σ_(n≤t)ν(n) gives the literal endpoint identity

    Σ_(y<n≤z)ν(n)/n = A(z)/z−A(y)/y+∫_y^z A(t)/t² dt.

Discard the nonpositive −A(y)/y and apply (6). A convenient bound is

    Σ_(y<n≤z)ν(n)/n
      ≤L(1,χ)(1+log z)+18sqrt(D/y).                     (7)

At y=D^(21/20) and z≤P^4, for L≥1 this is

    B := Σ_(D^(21/20)<n≤P^4)ν(n)/n
       ≤5C_A L^-2013+18D^-1/40.                        (8)

There is no rounding gap: (7) is a real-endpoint identity and the cutoff is strictly n>y. If one instead derives symmetric hyperbola from PV, the proposed weaker error O(D^-1/40 L) is also sufficient; the stronger elementary route (5) is preferable.

The total harmonic mass has no log P loss. At n≤D², ν≤τ_2 and the divisor convolution give

    Σ_(n≤D²)ν(n)/n≤(Σ_(m≤D²)1/m)²≤(1+2L)²≤9L².

Apply (7) above D² to bound the rest by 5C_A L^-2013+18D^-1/2. Thus, with C_0=27+5C_A,

    H := Σ_(n≤P^4)ν(n)/n ≤ C_0 L².                     (9)

All constants are independent of χ and of the factor labels. No primitive-modulus substitution by its radical is made.

## 4. Convolution tail with every cutoff retained

Apply (1), write n=ah², and enlarge only nonnegative sums. If ah²>D^20, then either a>D^19 or h>D^(1/2), because the two complementary weak inequalities imply ah²≤D^20. This is an exact strict/weak partition; overlap may be counted twice for an upper bound.

In every r-fold factorization a=n_1...n_r>D^19, at least one factor exceeds D^(19/r). Since r=2q≤18,

    19/r ≥ 19/18 > 21/20,
    19/18−21/20=1/180.

Thus that factor exceeds the cutoff in (8). Every factor is at most P^4 because n≤P^4 and all factors are positive integers. The union bound gives

    Σ_(D^19<a≤P^4)ν^{*r}(a)/a ≤ r B H^(r−1).           (10)

Absolute convergence and positivity give the exact square mass

    Σ_(h≥1)τ_K(h)/h²=ζ(2)^K,

including K=0, and, since h>D^(1/2) implies h^-1/2<D^-1/4,

    Σ_(h>D^(1/2))τ_K(h)/h²≤D^-1/4 ζ(3/2)^K.            (11)

Consequently the complete strict tail is at most

    r ζ(2)^K B H^(r−1) + D^-1/4 ζ(3/2)^K H^r.          (12)

Combining (8)–(9) gives exactly (2). The two error/main-term ratios, apart from fixed q,C_A constants, are

    exp(−L/40)L^2013,  exp(−L/4)L^2015.

Both tend to zero. Explicitly they are at most one for L≥2,000,000: log(2,000,000)<15, and the corresponding functions L/40−2013log L and L/4−2015log L are positive there and increasing thereafter. The weaker PV route has exponent 2014 in the first ratio and is absorbed by the same threshold. This is a uniform explicit absorption condition; it changes neither the 2022 assumption nor the 2024 final target. Fixed constants in (12) remain legitimate constants in (3).

## 5. Recomputed HB two-completion budgets

Use only the exact completion and common-coefficient sieve framework of the accepted [multilinear completion proof](../multilinear_completion/PROOF.md) and its [independent review](../multilinear_completion/REVIEW.md), at the versions pinned in INPUTS.json. At HB level j, the uncompleted polynomial has 2j+3 factors. Completing two genuinely smooth factors and transferring both duals to C leaves q=2j+1 factors in D′. For j≤4, q≤9, so (3) applies to the entire original e>D^20 range.

Coefficient Cauchy costs τ_q at the total index. Its submultiplicativity separates this into one weighted ν tail and q−1 ordinary harmonic divisor sums. The latter are each

    Σ_(n≤P^4)τ_q(n)/n≪_q (1+log P)^q≪_q L^(9q).

Unit shifted powers, finite Möbius cutoffs, original bounded masks and the original strict e cutoff survive; absolute values are used only in this nonnegative estimate. Thus

    E(D′)≪L^d,  d=4q−2015+9q(q−1)=9q²−5q−2015.         (13)

C′ still has six degree-one divisor factors, so E(C′)≪L^324. The safe label count is L^(81+18j), and the family normalization costs L^77. Hence the full paired logarithmic exponent is

    b=158+18j+(324+d)/2.

| j | remaining q | r | K | weighted ν tail | E(D′) exponent d | label exponent | paired exponent b |
|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 6 | 0 | −2003 | −1949 | 99 | −1273/2 |
| 2 | 5 | 10 | 5 | −1995 | −1815 | 117 | −1103/2 |
| 3 | 7 | 14 | 14 | −1987 | −1609 | 135 | −861/2 |
| 4 | 9 | 18 | 27 | −1979 | −1331 | 153 | −547/2 |

The inherited exact common-support envelope after the two completions is

    C′,Y′≤P^3.003/Q_j,

where Q_j is the selected pair's scale product. Cauchy on actual Ψ1 followed by enlargement of its two nonnegative moments therefore yields

    |Δ_(j,sector)|≪a_norm^-1 L^b max(1,P^1.003/Q_j)
                    + O(a_norm^-1 P^-10).              (14)

The finite HB constants (4,−6,4,−1), pair choices and parity/sign choices are fixed constants. The normalization Mcal≥P²/(4L^77) is the same as in the accepted source. No extra L^519 symbol cost appears; that part is inherited from the accepted all-height completion. Its prime-p completions are not confused with the original M completion at conductor Dp. The original normalized Gauss square cancels the two new dual Gauss factors exactly before the positive-moment bound.

For Q_j≥P^1.003, the right side of (14) is o(1) for every j≤4 and every strict e>D^20. The convenient stronger Q_j≥P^1.01 condition certainly qualifies. In particular, the old low-e positive logarithmic budgets for j=3 and j=4 are genuinely removed, even when the selected pair includes new HB b variables. No original recombined ρ energy was assigned to these components.

At the accepted central j=2 geometry Q_2=P^(5/6), the unchanged safe length loss is P^.17, now with L^-1103/2 in place of the older L^-127/4. A fixed positive P power still overwhelms every fixed negative L power because log P=L^9.

### Additional original-polynomial budgets checked

The author proof's two ancillary improvements also check out. With no extra smooth completion, the restored original polynomial has q=5, hence E(G)≪L^-1815. Original C energy L^144 and old labels L^72 give

    72+77+(144−1815)/2=−1373/2.

Its natural-length multiplier is still P^.501. With one additional original smooth completion, q=4 gives the weighted ν exponent −1999, E(D) exponent −1891, C energy exponent 225 and labels 99; the paired exponent is −657. Two original smooth completions retain −1273/2. Accordingly, a centered moment of the actual recombined G with bound P²L^(-1815+B), B<1373, would be sufficient; this review does not establish that moment.

## 6. Optional formalization variant

The larger integer K_alt=max(0,q²−2q) gives the same conclusions and all the same L/P exponents. Only fixed zeta constants increase. At inert valuation 2v,

    τ_q(p^(2v))≤τ_q(p^v)²≤τ_(q²)(p^v),

while 2q+K_alt≥q². The first inequality follows from divisor submultiplicativity with the two arguments p^v,p^v; the second is the matrix-margin inequality with a=b=q. The split and ramified arguments are unchanged. Thus (1) is valid with K_alt in place of K, with no multigraph lemma needed.

This variant matches the source statements `proposition71_tau_submultiplicative` in `ZhangLS/Spec/Proposition71DivisorWeights.lean`, `divisorPower_tau_square` in `ZhangLS/Spec/DivisorSmallPowerBudget.lean`, and `lemma34_tau_product_le_all` in `ZhangLS/Spec/Lemma34TauProduct.lean`. Their displayed types cover noncoprime arguments and all positive divisor orders; τ_0 is separately the convolution identity. These sources were read, but no compiler or fresh dependency-closure check was run. The sharper K=q(q−3)/2 result accepted above remains valid.

## 7. Limits of the acceptance

This pays the strong-pair sectors, not the full finite HB expression. Weak-pair sectors remain, and the exact finite recombination with all its cross terms remains necessary for any proposed global moment theorem. It does not establish a strict half-norm gain for the signed operator. No bad-family term is dropped: (14) uses actual Ψ1 before positive-moment enlargement.

The local arithmetic majorant works for q≥10, but this particular a>D^19 union bound would have r≥20 and no longer force a factor beyond D^(21/20). Do not apply (3) to uncompleted HB j=4 with q=11. Nor does a positive fixed P power become paid merely because its logarithmic coefficient is now very small.

This review records the replacement arithmetic estimate, with its complete proof and supplementary checks. It does not certify any new Lean declaration or alter the recorded 51/51 Spec result. No Lean/compiler execution was performed for this source audit.

## 8. Independently checked source and finite evidence

The independently accepted author proof had SHA256 `f8fb761c54a90812614c48d563f20ea6a3e8eadd580766afd51a7a391cf4daa2`. [PROOF.md](PROOF.md) is its public mathematical edition. It retains the full Fourier/PV alternative and incorporates the self-contained asymmetric-hyperbola argument proved in this review. Its strict endpoints, zeta constants, all-e completion table, ancillary original-polynomial budgets and restricted stopping map agree with the acceptance above. The editorial changes and original-to-public hashes are recorded in [PROVENANCE.json](PROVENANCE.json); the reviewed original documents were preserved byte-exact at preparation.

`check_independent.py` is the original independent checker, byte-identical to the accepted version, and imports no author checker. It verifies the full local convolution through valuation 300, matrix and multigraph counts, explicit graph-degree surjectivity in small cases, and exact integer convolutions for six primitive real characters of conductors 3, 4, 5, 8, 8, 12 through n=4096. It also checks asymmetric-hyperbola identities, complete-period bounds, rational budgets, strict threshold margins and an explicit absorption base. [CHECKS.json](CHECKS.json) records 307,346 passing assertions. These finite checks supplement, and do not replace, the universal proofs in Sections 2–4.

[MANIFEST.json](MANIFEST.json) pins the public package and [INPUTS.json](INPUTS.json) pins the supporting repository sources at `cbcfbcbc7ceafaafcf3e711b7216d2f059da192d`. The portable verifier needs only this package and the listed repository input bytes. Preserved historical originals are provenance records, not verifier dependencies. Mathematical acceptance, finite regression success and Lean certification are separate: this package claims the first two only.
