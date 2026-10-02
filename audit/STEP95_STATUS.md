# Step 95 — Complete original Lemma 5.4

The preceding goal turn made substantive progress: actual Gaussian mass,
weighted exterior concentration and the actual central-window Mellin
normalization were proved and fully audited. This step closes the actual
positive-axis exterior integral, uniform exponential absorption, and final
common constants. The broad goal remains **all 51 numbered results**.

`lemma54_proved : Lemma54Target` builds on pinned Lean 4.30.0. Six new
trusted modules, the final target and the expanded original-statement
regression pass. Nineteen principal interfaces use only `propext`,
`Classical.choice` and `Quot.sound`. Full repository kernel verification
PASS: 189 Spec modules, 267 project imports, 314 Lean sources and
44 regressions; 2026-10-01 08:04:34–08:20:21 Asia/Shanghai. Original Lemma 5.4
is now complete. The ledger is **15/51 complete, 0 in progress,
36 unstarted**; the broad goal remains active.

## Faithful original requirements

The source was rechecked against the locally available paper Markdown,
`/private/tmp/zhangmath-paper.md`, lines 1620–1666. The original Lemma 5.4
requires actual positive-axis Mellin δ, full Re s>0 analyticity,
`1/2≤Re s≤2` decay with some absolute polynomial exponent, and the
entire original `|s−1|<10α` disk normalization `1+O(α log L)`.

[`Lemma54.lean`](../ZhangLS/Spec/Lemma54.lean) keeps both original target
definitions **unchanged**. All constants and the natural modulus threshold
are chosen before D and s. One common positive absolute C supplies both
estimates. The actual inverse Mellin Δ and actual δ definitions are not
replaced by a model or a prescribed remainder.

## The actual integral near zero

[`Lemma54NearZeroMellin.lean`](../ZhangLS/Spec/Lemma54NearZeroMellin.lean)
uses the original disk's proved `Re s≥1/2`. On 0<x≤1 the actual Mellin
weight has norm at most x^(−1/2). The exact integral and absolute
integrability are proved:

\[
\int_0^1x^{-1/2}\,dx=2.
\]

The original window is far above x≤1, and the already proved Gaussian
exterior estimate yields `g(x)≤sqrt(π) exp(-L^10/2)`. The actual Lemma 5.3
small-range bound then gives

\[
|\Delta(x)|\le C_n e^{-L^{10}/2},\qquad C_n=2\sqrt\pi+C_s,
\]

with the already proved `C_s=4(e+1)+2`. Consequently the **actual**
Mellin integral over (0,1] has norm at most `2 C_n exp(-L^10/2)`.
The singular endpoint is handled by an integrable dominating weight.

## Small-range exterior

[`Lemma54SmallExteriorMellin.lean`](../ZhangLS/Spec/Lemma54SmallExteriorMellin.lean)
works for every measurable S⊆(1,T] outside the original closed window,
where `T=t₀^(51/50)` is unchanged. On this interval the actual Mellin
weight is at most x, hence at most both 1+x² and T. The actual small-range
Δ estimate and the Step 94 quadratic exterior Gaussian mass give

\[
\left|\int_Sx^{s-1}\Delta(x)\,dx\right|
\le(288+C_s)L^{1838}e^{-L^{10}/2}.
\]

The uniform additive error is integrated by comparing the actual S
integral to the finite interval (1,T]; its measure is T−1≤T.
`T²≤L^1060≤L^1838` absorbs that cost. The Gaussian exterior term is
twice the already proved `144 L^1838 exp(-L^10/2)`.

## Both original large-x tails

[`Lemma54LargeTailDamping.lean`](../ZhangLS/Spec/Lemma54LargeTailDamping.lean)
proves, on the **entire original** x>T range,

\[
(B\log x/100)^2\ge L^{10},\qquad x^{99/100}/B\ge L^{10}.
\]

The first follows from log x≥1 and B/100≥L^5. The second uses the already
proved actual large-range parameter `x^(99/100)>4t₀` and
`B L^10=L^410≤t₀=L^519`. No large-range hypothesis is newly assumed.
Splitting the original exponentials gives

\[
e^{-(B\log x/100)^2}
\le e^{-L^{10}/2}e^{-((B/2)\log x/100)^2},
\]

\[
e^{-x^{99/100}/B}
\le e^{-L^{10}/2}e^{-\sqrt{x}/(2B)}.
\]

[`Lemma54LargeExteriorMellin.lean`](../ZhangLS/Spec/Lemma54LargeExteriorMellin.lean)
then integrates the actual Δ large-range bound with actual Mellin weight
≤1+x³. The Step 93 moment formulas at B/2 and 2B are integrable, and
their explicit masses give

\[
\left|\int_T^\infty x^{s-1}\Delta(x)\,dx\right|
\le C_lL^{3200}e^{-L^{10}/2},
\]

where the explicit positive absolute constant is

\[
C_l=(2+e)(200\sqrt\pi e)+(\sqrt\pi e^2)10082\cdot256.
\]

Here `(2B)^8=256 L^3200` and `L^3200≥1`. The original stretched
exponential and endpoint remain in the actual Δ theorem; the half-power
exponential is a proved integrable upper envelope only.

## Full actual disk budget

[`Lemma54FullDiskBudget.lean`](../ZhangLS/Spec/Lemma54FullDiskBudget.lean)
proves the original closed window lies in (1,T]. The actual Mellin
convergence permits all integral splittings: (0,1], the closed central
window J_D, its complement within (1,T], and (T,∞).

Combining all actual pieces with the previously proved central estimate,
and using `log L≥1`, `L^405≤L^3200` and `L^1838≤L^3200`, yields

\[
|\delta(s)-1|\le10403\alpha\log L+
 C_eL^{3200}e^{-L^{10}/2},
\]

uniformly on the **entire original** |s−1|<10α disk, where

\[
C_e=2+6C_s+2C_n+(288+C_s)+C_l>0.
\]

No piece of the actual positive axis is omitted, and all equality
endpoints use the original small/large domain convention.

## One threshold and one common constant

[`Lemma54DiskErrorAbsorption.lean`](../ZhangLS/Spec/Lemma54DiskErrorAbsorption.lean)
uses the proved asymptotic `L^3209 exp(-L/2)→0`. Since L^10≥L for
L≥1, it chooses a single natural D₀ such that, for every D≥D₀,

\[
L^{3200}e^{-L^{10}/2}\le\alpha\log L.
\]

The proof multiplies by the positive L^9 and uses α=π/L^9 and
π log L≥1. The same threshold also supplies D>1 and L≥2000.
It does not depend on s. Therefore `C_disk=10403+C_e` works on the
entire original disk.

[`Lemma54.lean`](../ZhangLS/Spec/Lemma54.lean) chooses the **same**
absolute `C=C_M+C_disk>0` for both estimates, with c=3200 and the same
threshold. The already proved actual strip bound, analyticity and
new disk bound give `lemma54_uniform_constants`, followed by
`lemma54_proved : Lemma54Target`.

The exponent and constants are explicit sufficient budgets, not claimed
optimal. The final modulus threshold is a uniform existence witness,
not claimed to be a closed numerical bound. There are **no remaining
proof obligations for the original Lemma 5.4**.

## Verification

[`Step95Lemma54CompletionRegression.lean`](Step95Lemma54CompletionRegression.lean)
expands the actual full positive-axis integral, preserves both original
domains, the same common C and original quantifier order, and checks
the actual s=1 threshold specialization. Six new trusted modules and
the final target build. Nineteen principal axiom checks have only the
three standard axioms; see
[`step95_regression_axioms.txt`](step95_regression_axioms.txt).

Generated coverage is 189 trusted Spec modules, 267 project imports,
314 Lean sources and 44 audit regressions. Placeholder and source
structure checks pass. Strict static heuristic count stays 87 with
no new candidate; its nonzero exit is separate from kernel verification.
See [`step95_spec_audit.txt`](step95_spec_audit.txt).

Repository-wide kernel verification **PASS**: all 189 trusted Spec
modules, the Spec aggregate, full project with 267 imports and all
44 regressions passed. Verification ran at 2026-10-01 00:04:34–00:20:21 UTC
(2026-10-01 08:04:34–08:20:21 Asia/Shanghai). See
[`step95_full_verification.log`](step95_full_verification.log) and the
authoritative [`lean_kernel_verification.txt`](lean_kernel_verification.txt).
