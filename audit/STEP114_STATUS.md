# Step 114 — Actual enlarged local zero sets and uniform log P budgets

Full original Lemma 5.9 remains **in progress**. The actual L-function
quotient has not been proved. Full original Lemma 5.6 also remains in
progress with its faithful modulus-one principal target retained.
The original 51-result ledger is **17 complete, 2 in progress, 32 unstarted**.
This step promotes two actual-zero modules, twelve proved interfaces
and five expanded examples. No auxiliary result is counted as a
completed original lemma.

## Actual local disks and Jensen inputs

For every nonprincipal complex character theta, at every real height t,
actual L(theta) is entire. In the radius-15/8 closed disk around 2+it,
its actual norm is <=8q(4+|t|). At the actual center it is nonzero,
with actual norm >=1/4. Jensen's formula gives actual total divisor
multiplicity on the radius-7/4 closed disk <=15log(32q(4+|t|)).
No zero or growth conclusion is an assumption.

[Actual local zeros](../ZhangLS/Spec/Lemma59ActualLocalZeros.lean) are
exactly the finite support of the actual divisor on the radius-7/4
closed disk. Membership is exactly disk membership and L(theta)(rho)=0.
Each actual multiplicity is the natural analytic order and is >=1.
The actual divisor total is exactly the finite sum of actual analytic
orders; its actual finite zero count has the same Jensen upper bound.
The disk covers the full original Lemma 5.9 critical-line strip at the
proved parameter scale.

## Uniform actual log P budgets

[Scale budgets](../ZhangLS/Spec/Lemma59LocalZeroBudgets.lean) retain the
actual family prime q, actual center and genuine Psi1 membership.
Throughout the enlarged closed height |t-Im s0|<=L^405+20, the actual
height is <=10L^519, actual q<=2P and the Jensen logarithm <=2L^9.
Every actual Psi-family character is nonprincipal, proved from actual
primitivity and its actual prime conductor. There is one explicit
natural threshold 3^(3^200), before all D, chi, psi and t, such that
both the actual total zero multiplicity and actual finite zero count
are <=30L^9=30log P, including both height endpoints. No additional
zero-count, critical-line, spacing or contour hypotheses are added.

## Verification

Both promoted modules build. All five expanded
[regressions](Step114Lemma59ActualZerosRegression.lean) pass: actual
divisor sum, exact actual finite zero membership, exact natural
multiplicity sum, and both closed height endpoints. All twelve
[axiom reports](step114_regression_axioms.txt) use only propext,
Classical.choice and Quot.sound. autoImplicit is disabled.

All 491 Lean sources pass placeholder and structure checks. Coverage
is 347 trusted Spec modules, 425 imports and 63 audit regressions.
Strict static audit retains its nonzero exit and has 116 reviewed
candidates. Its one new candidate is ActualLocalZeros:74, `exact h`.
Here h is locally proved using the real inequality 1-1/x<=log x
at x=15/14, then numeric normalization gives 1/15<=log(15/14).
It is the Jensen denominator lower bound, not an assumed original
conclusion. See [static output](step114_spec_audit.txt),
[coverage](step114_coverage.json) and [interface manifest](step114_interface_manifest.json).

Repository-wide kernel verification **PASS**: all 347 trusted Spec
modules, the Spec aggregate, the full 425-import project and all 63
audit regressions passed. All 491 source fingerprints stayed unchanged.
Verification interval: 2026-10-02 01:11:10–2026-10-02 01:43:28 Asia/Shanghai.
See [step114_kernel_verification.txt](step114_kernel_verification.txt),
[source fingerprints](step114_source_fingerprints.json) and
[full gate log](step114_full_verification.log).

## Independently verified following actual factor inputs

The [independent actual factor draft](step115_lemma59_actual_factor_inputs_draft.txt)
proves actual L=P Q everywhere, including at removed zeros, actual
Q entire and nonzero on the closed local disk, normalized analytic
logarithms, Cauchy bounds and actual first-shift Q quotient <=exp(166400pi).
That absolute constant and one threshold precede all required parameters.
The exact actual L quotient equals the actual finite zero-factor
product times actual Q quotient. Actual local zeros satisfy 1/4<=Re rho<1
and lie in the enlarged height-13 window. Forty-five standard-axiom
interfaces (twelve prior and thirty-three new) and five expanded
examples pass independently outside this frozen project gate. See
[metadata](step115_lemma59_actual_factor_inputs_draft_metadata.json)
and [kernel output](step115_lemma59_actual_factor_inputs_draft.log).
The enlarged critical-line/simplicity/spacing conclusions and full
original Lemma 5.9 quotient remain unproved. All 51 original numbered
results remain in the active goal.

The independently verified [enlarged approximation draft](step116_lemma59_extended_approximation_draft.txt) passes 50 public standard-axiom interfaces and three expanded examples outside this gate. It proves the actual product approximate functional equation at strict height L^405+19 and the actual product Gamma logarithmic derivative at closed height L^405+20, with the original constants. The full actual quotient is still unproved.
