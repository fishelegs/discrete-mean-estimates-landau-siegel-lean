# Step 113 — Lemma 5.9 closed-region polynomial and finite zero-product inputs

Full Lemma 5.9 remains **in progress**. Its actual L-function quotient
has not been proved. Full Lemma 5.6 also remains in progress, with the
faithful modulus-one principal target retained. The original 51-result
ledger is **17 complete, 2 in progress, 32 unstarted**. This step promotes
five auxiliary modules, twenty-seven proved interfaces and eight
expanded regression examples; it does not count an auxiliary result
as a completed original lemma.

## Original closed strip and actual offset

[Parameters and target](../ZhangLS/Spec/Lemma59Parameters.lean) retain
|Re s-1/2|<=alpha and the full closed height |Im s-Im s0|<=L^405+10.
The actual first shift is exactly i alpha(1-5c alpha L), using the
same offset definition as Lemma 2.3. The pending quotient target is
stated in a stronger uniform form for every fixed c>0 and eta>0,
with C and one natural threshold before all D, characters and points.
It retains genuine Psi1 membership and separation from every actual
L-function zero by eta alpha, with no zero-spacing, contour or
quotient conclusions assumed. This separation already implies that
the actual L-function denominator is nonzero.

## Enlarged actual polynomial estimates

The enlarged Omega1 has the same real bounds as the original Omega1
and height <L^405+20; enlarged Omega2 has the original narrow real
bounds and height <L^405+19. Original good partial-sum conditions
prove actual ||F||+||G||<=2L^79 and ||FG-1||<=4L^-227 there.
Actual F has two-sided bounds L^-88<=||F||<=L^88 and is nonzero.
Cauchy/Borel-Caratheodory estimates yield actual ||F'/F||<=140800L
throughout enlarged Omega2. The full original Lemma 5.9 closed strip
and all actual first-shift paths lie in the enlarged regions at the
proved parameter scales. One explicit natural threshold 3^(3^200)
is selected before all D, chi, psi and s; original Psi1 discharges
the good partial-sum input. Sources:
[polynomial bounds](../ZhangLS/Spec/Lemma59ExtendedPolynomialBounds.lean),
[logarithmic derivative](../ZhangLS/Spec/Lemma59ExtendedPolynomialLog.lean),
[uniform actual inputs](../ZhangLS/Spec/Lemma59UniformPolynomialInputs.lean).

## Finite complex zero-factor products

[Finite zero-product tools](../ZhangLS/Spec/Lemma59FiniteZeroProducts.lean)
prove the exact telescoping product prod_{k<N}(k+2)/(k+1)=N+1.
Ranked complex-zero distances (k+1)delta give a shifted polynomial
quotient norm <=N+1. Descending ordinate gaps imply those ranked
distances. Zeros above the shifted height give norm ratios <=1,
including the closed endpoint. Each eta-separated near factor is
at most 1+eta^-1; at most two such factors cost (1+eta^-1)^2.
These are explicit auxiliary hypotheses, not assumptions inserted
into the original target. Deriving actual enlarged-region zero
structure and connecting the actual L-function factorization to
these products remain pending.

## Verification

All five promoted modules build. All eight expanded
[regressions](Step113Lemma59AuxiliaryRegression.lean) pass: actual
finite Dirichlet polynomial, opposite closed strip boundary points,
actual L denominator, exact original first shift, shifted region,
and two actual finite polynomial quotient identities. All twenty-seven
[axiom reports](step113_regression_axioms.txt) use only propext,
Classical.choice and Quot.sound. autoImplicit is disabled.

All 488 Lean sources pass placeholder and structure checks. Coverage
is 345 trusted Spec modules, 423 imports and 62 audit regressions.
The strict static heuristic retains its nonzero exit and has 115
reviewed candidates. Its sole new candidate is ExtendedPolynomialLog:89,
`exact hlogL`. In a generic geometric helper, this uses the explicit
scalar input log L>=200 to prove L^-1<=log L/(200L), after cancelling
positive denominators. It forwards no original lemma conclusion.
The uniform theorem proves this scalar input from the explicit
modulus threshold. See [static output](step113_spec_audit.txt),
[coverage](step113_coverage.json) and [interface manifest](step113_interface_manifest.json).

Repository-wide kernel verification **PASS**: all 345 trusted Spec
modules, the Spec aggregate, the full 423-import project and all 62
audit regressions passed. All 488 source fingerprints stayed unchanged.
Verification interval: 2026-10-02 00:32:35–2026-10-02 01:03:17 Asia/Shanghai.
See [step113_kernel_verification.txt](step113_kernel_verification.txt),
[source fingerprints](step113_source_fingerprints.json) and
[full gate log](step113_full_verification.log).

## Independent following actual local-zero draft

The independently verified [actual local-zero draft](step114_lemma59_actual_local_zeros_draft.txt)
proves actual L growth on the radius-15/8 disk and actual finite zero
sets with actual analytic multiplicities on the radius-7/4 disk.
Both the total actual multiplicity and the actual zero count are
uniformly <=30 log P on the enlarged closed height window, including
both endpoints. Twelve standard-axiom interfaces and five expanded
examples pass. This draft is outside this frozen project gate.
See [metadata](step114_lemma59_actual_local_zeros_draft_metadata.json)
and [kernel output](step114_lemma59_actual_local_zeros_draft.log).
Full Lemma 5.9 quotient and original Lemma 5.6 q=1 remain unproved.
All 51 original numbered results remain in the active goal.
