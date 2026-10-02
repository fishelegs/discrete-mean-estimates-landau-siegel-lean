# Step 98 — Actual local logarithmic derivatives and all-order remainder bounds

Step 97 was material progress: it constructed the exact actual zero set
in the whole original Lemma 5.5 region and passed the complete kernel
gate. This step continues the active all-51-results goal with the actual
zero-factor extraction and quantitative local logarithmic derivatives.
Original Lemma 5.5 remains partial; full-region exclusion is not claimed.

Six new trusted modules build on pinned Lean 4.30.0. The expanded
actual-object/removable-value/height-endpoint/all-order regression passes.
Thirty-three principal interfaces have only `propext`, `Classical.choice`
and `Quot.sound`. Coverage, placeholder and structure checks pass for
207 Spec modules, 285 project imports, 335 Lean sources and 47 regressions.
The full repository kernel gate **PASS** covers these new sources:
2026-10-01 10:01:34–10:20:09 Asia/Shanghai. Trusted Spec modules,
the Spec aggregate, the full project and all audit regressions pass.
See the authoritative [kernel report](step98_kernel_verification.txt)
and [Step 98 full verification log](step98_full_verification.log).
No project Lean source changed during the gate; subsequent finalization
only synchronizes these progress documents.

The ledger remains **15/51 complete, 1 in progress, 35 unstarted**.

## Actual zero factorization, including removed zeros

[`Lemma55ZeroFactorization.lean`](../ZhangLS/Spec/Lemma55ZeroFactorization.lean)
defines the factor P from the actual analytic divisor of L(s,χ) in the
closed radius-5/4 disk about c=2+it. The quotient L/P is put in mathlib's
meromorphic normal form at its removable singularities, giving Q.
Actual analytic orders and the finite local divisor prove that Q is
entire and nonzero everywhere in this whole closed local disk.

The actual pointwise identity L(s,χ)=P(s)Q(s) holds for **all** complex s,
including the removed zeros. Outside them Q equals the actual quotient.
No arbitrary analytic remainder or nonvanishing assumption is introduced.

## Actual multiplicities and factor bounds

[`Lemma55ZeroFactorBounds.lean`](../ZhangLS/Spec/Lemma55ZeroFactorBounds.lean)
identifies P with the actual finite product

\[
P(s)=\prod_{\rho\in S_t}(s-\rho)^{m_\rho},\qquad
m_\rho=\operatorname{ord}_\rho L(\cdot,\chi),\qquad N=\sum m_\rho.
\]

Here S_t is exactly the actual local zero set. The previous actual
Jensen bound gives N≤13L for L=log D≥2000 and |t|≤2D.
The center bound is |P(c)|≤(5/4)^N. On the outer radius-3/2 circle,
every zero is at distance at least 1/4, so |P(s)|≥(1/4)^N>0.

## Actual quotient growth and normalization

[`Lemma55ZeroRemovedBounds.lean`](../ZhangLS/Spec/Lemma55ZeroRemovedBounds.lean)
combines the outer factor lower bound with the actual |L(s,χ)|≤8D²
bound. The maximum modulus principle gives |Q(s)|≤8D²4^N on the
entire closed radius-3/2 disk. The actual center lower bound for L
and the factor upper bound imply |Q(c)|≥1/(4(5/4)^N). Consequently

\[
|Q(s)/Q(c)|\le32D^2 5^N,\qquad
\log(32D^2 5^N)\le55L.
\]

These bounds include both height endpoints and every closed-disk point.

## Actual normalized logarithm and Cauchy bounds

[`Lemma55ZeroRemovedLog.lean`](../ZhangLS/Spec/Lemma55ZeroRemovedLog.lean)
constructs a continuous normalized logarithm ℓ of Q(c+z)/Q(c) on
|z|<5/4. It proves ℓ(0)=0, analytic regularity, and the actual derivative
ℓ′(z)=Q′(c+z)/Q(c+z). The conclusions hold for every valid normalized
branch, whose existence is proved.

Borel–Carathéodory gives |ℓ(z)|≤990L on the whole closed |z|≤9/8 disk.
Cauchy's estimate then gives, for every natural n,

\[
|\ell^{(n)}(0)|\le n!\,990L\,(8/9)^n.
\]

## Actual local logarithmic-derivative formula

[`Lemma55LocalLogDerivative.lean`](../ZhangLS/Spec/Lemma55LocalLogDerivative.lean)
proves, wherever the actual L-function is nonzero,

\[
\frac{L'}{L}(s,\chi)
=\sum_{\rho\in S_t}\frac{m_\rho}{s-\rho}+\frac{Q'}{Q}(s).
\]

At c=2+it, the actual center is nonzero and the last term has norm
at most 176L. The zero sum uses actual multiplicities; neither the
partial-fraction identity nor its error is an assumed hypothesis.

## All-order actual remainder and summable aggregate

[`Lemma55HigherLogDerivative.lean`](../ZhangLS/Spec/Lemma55HigherLogDerivative.lean)
proves equality of the actual higher logarithmic-derivative remainder
with the higher derivative of Q′/Q. Let B_t(s) be the actual finite
zero sum above and define

\[
E_n=\frac{\left|\left(\frac{d}{ds}\right)^n(L'/L)(c)
-B_t^{(n)}(c)\right|}{n!}.
\]

Then for all n≥0 and every finite set I of natural orders,

\[
E_n\le990(n+1)L(8/9)^{n+1},\qquad
\sum_{n\in I}E_n\le71280L.
\]

The aggregate is proved from the exact geometric-series moments, and
its constant is independent of the size of I. This closes the actual
analytic-remainder budget proposed in Step 97's local continuation.

## Verification and static review

[`Step98Lemma55LogDerivativeRegression.lean`](Step98Lemma55LogDerivativeRegression.lean)
expands mathlib's actual L-function with its genuine nonzero-modulus
instance. It checks factorization at all points, nonzero quotient values
at actual removed zeros, the positive height endpoint for the first
derivative, the negative endpoint for arbitrary orders, every finite
order set, and existence of a branch with all closed-disk/all-order bounds.
Thirty-three axiom reports contain only standard Lean axioms.

Strict static audit reports **94 review candidates**, three more than
Step 97. The scanner and its strict nonzero exit are preserved. Each new
candidate has been inspected:

- `Lemma55HigherLogDerivative.lean:73` returns an iterated-derivative
  equality derived locally from the actual factorization and analyticity.
- `Lemma55ZeroFactorBounds.lean:68` returns the center-to-root norm bound
  derived from membership in the actual local closed disk.
- `Lemma55ZeroRemovedBounds.lean:50` supplies the original closed-disk
  membership after rewriting the maximum-principle closure domain. It
  does not supply the analytic growth conclusion as a hypothesis.

## Remaining original obligation

`Lemma55Target` and its full original Re s>1−2/L, |Im s|<2D region
are unchanged. The actual simple real zero and local uniqueness are
already proved. The new formulas and remainder budgets still do not
exclude every other actual zero in that entire region.

The next repulsion obligations include the finite-zero inverse-power
derivative formula, the weighted Fejér detection inequality, corresponding
actual zeta/pole data, and the positivity upper bound from the actual
von Mangoldt coefficients with the exceptional-zero contribution removed.
Their combination and the final uniform-threshold contradiction remain
unproved. The full Lemma 5.5 is therefore not promoted to complete,
and the full all-51-results goal remains active.

## Preparation for the next goal turn

During the full gate, a separate draft at
`/private/tmp/zhangmath-fejer-kernel.lean` passed `lake env lean` with no
errors. An exact textual copy is preserved as
[`step99_fejer_kernel_draft.txt`](step99_fejer_kernel_draft.txt), with its
three principal standard-axiom reports in `step99_fejer_kernel_draft.log`.
It is **not** a project Lean module or part of this step's full gate,
and is not counted among the 207 trusted modules.

The seven draft lemmas prove a positive squared-norm identity for finite
geometric sums, the equivalent weighted-power form, the Fejér kernel
bound F_J(z)≥−1/2 on the entire closed unit disk, and F_J(1)=J/2.
The positive identity avoids an additional harmonic-minimum argument.
These lemmas are ready for further development and later project import.

The proposed next detection step is to choose a largest normalized zero
term z₀ with |z₀|=1 and set v=z₀⁻¹. A weighted combination of
F_J(z), F_J(zv) and F_J(z conjugate(v)) would have contribution at least
J/4−N after summing over actual multiplicities N. Its coefficient at
each power lies between zero and two. This combination is **not yet
proved**; the draft only supplies its individual kernel bounds.

The current actual remainder sum budget would bound the corresponding
weighted analytic errors by 142560L per local formula. With J chosen
as a sufficiently large fixed constant times L, the proposed positive
kernel term could dominate those errors. The exceptional-zero upper
bound would then involve δJ² times a normalization factor bounded by
an absolute exponential, where δ≤64L^−2022. This is a planning inference,
not a completed zero-repulsion theorem. Actual zeta/pole data, the
von Mangoldt positivity identity, and the final uniform-threshold
contradiction still require formal proofs.
