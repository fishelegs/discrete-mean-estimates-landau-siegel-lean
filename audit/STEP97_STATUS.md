# Step 97 — Actual zero counts on the whole original Lemma 5.5 region

This step continues the active goal of proving all 51 numbered results.
Original Lemma 5.5 remains partial: the previous step proved its actual
simple real zero and local uniqueness; the exclusion of all other zeros
throughout the original height-2D region is still unproved.

Six new trusted modules build on pinned Lean 4.30.0. The expanded
actual-object, actual-multiplicity and height-endpoint regression passes.
Twenty-seven principal interfaces depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Coverage and placeholder/structure
checks pass for 201 Spec modules, 279 project imports, 328 Lean sources
and 46 regressions. Full repository kernel audit **PASS**:
2026-10-01 09:22:21–09:39:55 Asia/Shanghai. The independent Spec modules, Spec
aggregate, full project build and all 46 regressions pass.

The ledger remains **15/51 complete, 1 in progress, 35 unstarted**.

## Original region and actual functions

The faithful `Lemma55Target` is unchanged. Its region is

\[
\Re s>1-2/L,\qquad |\Im s|<2D,\qquad L=\log D.
\]

All new zero sets use the actual analytic Dirichlet L-function and its
actual analytic orders. They do not receive growth, nonvanishing, zero
finiteness or a zero count as additional hypotheses.

## Actual center lower bound

[`Lemma55NearTwoBound.lean`](../ZhangLS/Spec/Lemma55NearTwoBound.lean)
proves an elementary telescoping HasSum of mass 1/2. For Re s≥2,
the n=1 term of the actual L-series is one, the n=2 term has norm at
most 1/4, and the n≥3 tail is bounded by that telescoping sum. Hence

\[
|L(s,\chi)-1|\le3/4,\qquad |L(s,\chi)|\ge1/4.
\]

## Actual high-height disk bound and Jensen estimate

[`Lemma55HighHeightDisk.lean`](../ZhangLS/Spec/Lemma55HighHeightDisk.lean)
uses the actual Abel representation to prove |L(z,χ)|≤8D² on every
closed radius-3/2 disk centered at 2+it, uniformly for |t|≤2D.
The disk has Re z≥1/2. Both height endpoints and the whole closed disk
are included. The center lower bound above is at least 1/4.

[`Lemma55JensenZeroCount.lean`](../ZhangLS/Spec/Lemma55JensenZeroCount.lean)
then applies mathlib's actual analytic divisor version of Jensen's
formula. For L≥2000, total zero multiplicity in the closed radius-5/4
disk centered at 2+it is at most 13L. The arithmetic uses
log(6/5)≥1/6 and log(32D²)≤2L+31.

## Actual finite zero sets and multiplicities

[`Lemma55ActualLocalZeros.lean`](../ZhangLS/Spec/Lemma55ActualLocalZeros.lean)
proves finite analytic order at every point, using global analyticity,
the identity theorem and the nonzero value at two. The actual divisor's
finite support is therefore exactly the actual zero set in each closed
local disk. Its sum is the sum of actual natural-number analytic orders.
Every zero has order at least one, so the distinct-zero count is also
at most 13L.

## Cover of the full original region

[`Lemma55OriginalRegionCover.lean`](../ZhangLS/Spec/Lemma55OriginalRegionCover.lean)
constructs centers 2+it_j with t_j=j/2−2D, 0≤j≤8D. Choosing
j=floor(2(Im s+2D)) gives 0≤Im s−t_j<1/2. On the original region
with Re s≤1 and L≥2000, the real displacement has norm at most 11/10.
Consequently every such point belongs to one of the closed radius-5/4
disks. No height portion of the original region is dropped.

[`Lemma55OriginalRegionZeros.lean`](../ZhangLS/Spec/Lemma55OriginalRegionZeros.lean)
uses actual Dirichlet nonvanishing on Re s≥1 to exclude the region's
unbounded right portion. A filtered finite union of the local zero sets
has membership **if and only if** the point is an actual zero in the
whole original region. Its distinct-zero cardinality satisfies

\[
N\le13(8D+1)L.
\]

In particular the whole original zero set is finite. Whenever it is
nonempty, a zero with maximal real part exists. Under actual (A) and
the same explicit D≥3^10,000,000 threshold, the simple real zero from
Step 96 belongs to this exact set, so a rightmost actual zero exists
without adding a zero-existence assumption.

## Verification and static review

[`Step97Lemma55FullRegionZerosRegression.lean`](Step97Lemma55FullRegionZerosRegression.lean)
expands the actual mathlib L-function with the genuine nonzero-modulus
instance. It checks Re s=2, both t=±2D endpoints, the actual sum of
multiplicities, exact membership in the full original region, its
cardinality bound, and the rightmost-zero conclusion under (A).
Twenty-seven axiom checks contain only standard Lean axioms.

The authoritative [kernel report](lean_kernel_verification.txt) and
`step97_full_verification.log` record the completed full gate. No Lean
source was changed during that gate. Final edits only synchronize these
status documents with its actual PASS result.

Strict static audit reports **91 review candidates**, four more than
Step 96. The four new candidates were inspected individually:

- `Lemma55NearTwoBound.lean:32` returns the locally derived finite
  telescoping identity from `Finset.sum_range_sub'` after normalization.
- `Lemma55NearTwoBound.lean:89` returns the locally derived n=2 bound
  from the proved actual L-series term estimate after normalization.
- `Lemma55JensenZeroCount.lean:45` returns the actual Jensen bound
  derived from `AnalyticOnNhd.sum_divisor_le` and the proved inputs.
- `Lemma55JensenZeroCount.lean:68` returns the locally derived numerical
  logarithm lower bound after normalization.

None is a desired conclusion supplied as an external hypothesis. The
scanner and its strict nonzero exit are preserved; the candidate count
is not represented as zero or as an unchanged 87.

## Remaining original obligation

The count and maximum are prerequisites for zero repulsion. They do
**not** prove that the actual original-region zero set is a singleton.
The exclusion of every other actual zero in the entire original region
remains the unresolved part of `Lemma55Target`. Original Lemma 5.5 is
not promoted to complete, and the broad goal remains active.

## Candidate continuation, not a completed proof

The local mathlib API `MeromorphicOn.extract_zeros_poles` supplies an
analytic nonzero factor after extracting a finite divisor. The existing
`Lemma23BorelCaratheodory` and Cauchy tools can then be reused, but an
actual quantitative quotient bound and higher logarithmic-derivative
formula still need proofs.

[Kadiri–Ng–Wong, *The least prime ideal in the Chebotarev density
theorem*, §2](https://www-math.nsysu.edu.tw/~pjwong/stuff/leastprime.pdf)
proves a real-part power-sum lower bound using weighted Fejér sums. That
is a primary reference for the algebraic detection step, not an axiom or
an installed Lean theorem.

A possible local variant would retain the analytic remainder: Cauchy
estimates would make its higher normalized derivatives decay with the
order, and their weighted aggregate could be bounded by a constant times
log D. A sufficiently long weighted power sum could dominate this
aggregate. Combining that with an upper bound derived from actual
nonnegative von Mangoldt coefficients and the exceptional zero is the
proposed repulsion mechanism. This is an inference for planning; the
Fejér inequality, quantitative remainder, coefficient identity, and final
contradiction all remain proof obligations. In particular, the present
finite-set/cardinality theorems do not supply the missing contradiction.
