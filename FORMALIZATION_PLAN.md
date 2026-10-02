# ZhangLS formalization repair plan

## Goal

The target is not merely `0 sorry`.  A theorem counts as migrated only when its Lean
statement represents the corresponding mathematical statement and its proof no longer
receives the essential conclusion as an input hypothesis.

## Status convention

- `LEGACY`: compiles/proves a surrogate statement but is not evidence for the paper.
- `SPEC`: mathematical object or theorem statement has been written faithfully enough to review.
- `BRIDGED`: legacy code has been connected to the SPEC object by proved lemmas.
- `VERIFIED`: theorem is proved from earlier VERIFIED/SPEC facts with no hidden analytic assumption.

## Phase 0 — specification audit [IMPLEMENTED]

1. Keep the original modules for comparison; do not silently reinterpret them.
2. Add `tools/spec_audit.py` to flag common proof-surrogate patterns.
3. Maintain `audit/STATUS.md` as the migration ledger.
4. The following are blocking defects:
   - artificial definitions of `L` or `L'`;
   - theorem conclusion repeated as a hypothesis;
   - arbitrary residual `o_p := lhs - main_term` without a quantitative error theorem;
   - `Float` used for theorem-level analytic quantities;
   - contradiction obtained only after assuming the whole contradiction-producing implication.

## Phase 1 — arithmetic objects [STARTED]

Create the trusted specification layer under `ZhangLS/Spec/`.

1. `RealDirichletCharacter.lean`: exact real Dirichlet-character-like structure with
   periodicity, complete multiplicativity, and vanishing off units.
2. Separate `primitive` as a property rather than putting an unverifiable label in a type name.
3. Later bridge this structure to mathlib's Dirichlet character API after the project is
   pinned to a known mathlib revision and compiled.

Exit criterion: every theorem using a “real primitive character” takes a value satisfying
explicit character and primitivity conditions.

## Phase 2 — Dirichlet L-series [STARTED]

1. Define the real Dirichlet series by an actual infinite sum.
2. Define the formal termwise derivative series separately; do not call it the derivative
   until differentiability/termwise differentiation is proved.
3. State Assumption (A) using the actual series at `s = 1` only after convergence/continuation
   at that point is established through the appropriate character hypothesis.
4. Prove the easy half-plane convergence facts first, then continuation / value-at-one bridges.

Exit criterion: no theorem in the trusted path imports the legacy artificial `L` or `L'`.

## Phase 3 — analytic infrastructure

Migrate, in dependency order:

- Abel/partial summation;
- character orthogonality and partial-sum bounds;
- Euler products and nonvanishing where needed;
- Perron/Mellin/contour-shift lemmas;
- Cauchy derivative formula and residue identities.

Each asymptotic result must expose an explicit norm/absolute-value error bound.

## Phase 4 — paper Section 2 structural chain

1. Main identity: instantiate the algebraic identity with the paper's concrete functions.
2. Non-negativity: prove positivity/non-negativity of the actual local factors.
3. Main terms: prove quantitative main-term + error estimates, not residual identities.
4. Proposition 2.4 / 2.5 / 2.6: state and prove them using paper quantities.

## Phase 5 — Lemma 5.7 and coefficient lower bound

Rebuild the contour/residue argument for `L'(1, χ)` and derive the lower bound from it.
The definition of `L'` must never contain `D / φ(D)` by construction.

Step 32 fixes the exact Mellin integrand and vertical integrals, proves the
Dirichlet-product identity and the full local residue coefficient
`L'(1,χ) + (γ + 4 log D)L(1,χ)`, and reduces the remaining work to three
explicit obligations: Mellin inversion, contour shifting, and the analytic
error bound under Assumption (A).

Step 33 splits the Mellin-inversion obligation at its natural scalar seam.  It
proves absolute integrability of the Gaussian kernel on every nonzero vertical
line, identifies the paper integral with mathlib's `mellinInv`, and reduces
kernel evaluation to the single explicit transform
`M[x ↦ g_D(x⁻¹)](s) = ω₁(s)/s`.  After this transform is proved, only the
Dirichlet-series/integral interchange remains for `Lemma57MellinIdentity`.

Step 34 discharges that scalar transform.  In logarithmic coordinates it proves
the cumulative Gaussian derivative, evaluates its complex Gaussian Laplace
transform, establishes two-sided integrability, and applies improper integration
by parts.  The exact `HasMellin` statement and hence the scalar inverse-Mellin
formula are now proved.  Only the Dirichlet-series/integral interchange remains
inside `Lemma57MellinIdentity`.

Step 35 discharges the full `Lemma57MellinIdentity`.  Absolute convergence of
the divisor-character L-series at real part `2` supplies a common summable
coefficient majorant, while Step 34 supplies the integrable scalar Gaussian
kernel.  The Bochner integral is exchanged with the infinite sum and every
coefficient integral evaluates to its Gaussian-smoothed term.  The remaining
Lemma 5.7 obligations are now only the contour shift and the explicit analytic
error bound under Assumption (A).

Step 36 proves the limiting layer of the contour shift.  It defines symmetric
truncated vertical integrals and the oriented horizontal-edge error, proves
that integrability gives convergence of the truncations, and derives the exact
infinite contour identity from finite rectangle residue formulas plus
horizontal decay.  The remaining contour work is now precisely left-line
integrability, the finite rectangle theorem around the pole at zero, and the
horizontal-edge estimate; the Assumption-(A) analytic error bound follows as a
separate final obligation.

Step 37 proves the local complex-analysis layer.  The regularized zeta factor,
Gaussian factor, and pole-removed residue numerator are entire; the genuine
Mellin integrand is analytic away from zero.  Cauchy's derivative formula then
computes its normalized integral around every positive centered circle as the
exact residue value.  Thus the finite rectangle theorem now needs only the
global deformation between that circle and the rectangle in the punctured
region, followed by the already-isolated edge estimates.

Step 38 fixes the positively oriented finite rectangle and proves its exact
winding integral `∮ ds/s = 2πi` by real rational integration and arctangent
identities.  It also proves that `Lemma57FiniteRectangleShift` is equivalent to
the standard unnormalized rectangle residue identity.  The remaining local
task is now algebraic-analytic: split the genuine integrand into its `s⁻²`
principal part, residue multiple of `s⁻¹`, and an entire remainder, then apply
Cauchy–Goursat and the two kernel boundary evaluations.

Step 39 completes that local task.  Two iterated divided differences construct
the entire remainder after removing the numerator's constant and linear Taylor
terms.  Rectangular Cauchy–Goursat kills this remainder, an explicit four-edge
antiderivative calculation kills the `s⁻²` term, and Step 38 evaluates the
residue multiple of `s⁻¹`.  Thus `Lemma57FiniteRectangleShift` is now a theorem;
only left-line integrability and horizontal decay remain for the infinite
contour shift, followed by the Assumption-(A) analytic error bound.

Step 40 packages the missing global input as an explicit exponential bound for
the undamped factor `ζ(1+s)L(1+s,χ)/s` on the closed strip, away from its pole.
The exact norm of Zhang's Gaussian factor is computed on arbitrary vertical
lines, and its negative quadratic exponent is proved to absorb every allowed
linear exponential.  This yields left-line integrability, horizontal-edge
decay, and hence the exact infinite contour-shift identity.  The contour shift
is therefore reduced to proving the stated classical growth estimate for the
actual zeta and Dirichlet L-functions; the Assumption-(A) error bound remains
the next separate analytic obligation.

Step 41 proves that the right half of Step 40's strip is not genuinely an
input.  Absolute convergence at `Re(1+s) ≥ 3/2` gives explicit summable
majorants for both the actual Riemann zeta function and the actual Dirichlet
L-function, and the cutoff on `|s|` controls the remaining denominator.  The
full strip-growth condition, and therefore the exact contour shift, now
follows from exponential growth only on the true critical half-strip
`-1/2 ≤ Re(s) ≤ 1/2`.  This remaining estimate must be obtained from analytic
continuation/functional equations or a suitable direct representation; it is
not supplied by the absolutely convergent series.

Step 42 begins the functional-equation route through mathlib's actual
construction.  For every weak functional-equation pair, the pole-corrected
completed function is a Mellin transform of a rapidly decreasing modified
kernel.  Endpoint Mellin integrability and monotonicity of real powers give a
single integrable majorant for every imaginary part and every real part in a
closed strip.  This proves uniform completed-function boundedness and, for
Riemann zeta, also bounds the meromorphic completed function away from its two
explicit poles.  A reciprocal-Gamma exponential estimate is now the next
bridge from these completed bounds to ordinary zeta/L growth.

Step 43 supplies that bridge for Riemann zeta. Euler's integral bounds Gamma
on positive vertical strips, and reflection converts the reciprocal into a
bounded Gamma factor times a complex sine. This proves exponential growth for
`Gammaℝ(s)⁻¹` and hence for ordinary Riemann zeta on the required strip away
from `s=1`. Completing the Dirichlet L part still requires its finite Hurwitz
representation and control of the shifted odd Gamma factor.

Step 44 proves the completed Dirichlet L bound. The odd Hurwitz kernel forms
a strong functional-equation pair; its Mellin transform has the same endpoint
majorant argument as the weak-pair transform. Both parities are therefore
uniformly bounded, and the finite Hurwitz sum is bounded after the factor
`N^{-s}` is controlled. For a nontrivial primitive character the two rational
pole terms vanish. The shifted odd Gamma factor is the remaining bridge to
ordinary Dirichlet L growth.

Step 45 controls that odd factor by bounding reciprocal Gamma on a compact
central region and applying recurrence plus reflection outside it. The
ordinary Dirichlet L-function now has exponential growth on the needed
strip. Combined with the corresponding zeta bound, this proves the remaining
critical-strip growth interface and the exact infinite contour shift for
primitive real characters of modulus greater than one.

Step 46 extracts the exact `D⁻²` Gaussian envelope on the shifted line and
integrates a separately stated sub-Gaussian growth condition to an explicit
Gaussian moment. That condition is not yet derived for the actual zeta/L
factor. The exponential growth from Step 45 cannot by itself yield Zhang's
small error, since the Gaussian has width `(log D)^15`.

Step 47 proves strict positivity of the actual real `L(1,χ)` by combining
mathlib's nonvanishing theorem, convergence of the L-series to one at real
infinity, reality on the half-line, continuity, and the intermediate value
theorem. Assumption (A) therefore controls the absolute residue correction.
The analytic error is reduced to that explicit small term plus the shifted
Gaussian-weighted zeta/L integral. A quantitative polynomial-type vertical
bound with effective modulus dependence remains the main analytic gap.

Step 48 makes the residue budget numerical. For `log D ≥ 2`, which holds
eventually for natural moduli, the correction is at most `1/32` and thus at
most `(1/32) D/φ(D)`. The desired `(1/16) D/φ(D)` analytic-error bound now
follows from a single `(1/32) D/φ(D)` estimate on the shifted integral or
its Gaussian envelope. Neither such estimate is claimed proved here.

Step 49 proves an explicit quadratic Gaussian moment inequality and applies
it to the actual shifted integral under a pointwise bound of the form
`‖ζ(1/2+it)L(1/2+it,χ)/(-1/2+it)‖ ≤ C(1+t²)`.
The Gaussian-weighted integral is then bounded by
`C(1+8(log D)^30)√(8π(log D)^30)`. No such pointwise bound or suitable
modulus dependence of `C` is yet established for the analytic functions.

Step 50 proves that `C ≤ D` would be sufficient uniformly for all
sufficiently large moduli. The explicit Step 49 expression is bounded by a
fixed constant times `((log D)^30+8(log D)^60)/D`, which tends to zero.
Combined with Step 48, this gives the full analytic-error budget under the
stated quadratic-growth input. Establishing that input for the actual
zeta/Dirichlet-L product remains the central missing analytic proof.

Step 51 proves unconditional cancellation for the actual primitive
Dirichlet character: every complete residue period sums to zero and every
natural-number partial sum has norm at most `D`. This is a concrete
arithmetic input for later L-function estimates, not yet the required
critical-line quadratic bound. The numbered-paper-result inventory is in
`progress.md`.

Step 52 converts that concrete partial-sum bound to the `O(1)` hypothesis
of Abel summation and proves an integral representation for the actual
Dirichlet L-function on `re s > 1`. Extending the representation to
`re s > 0` and deriving an explicit conductor-dependent critical-line
bound are still open.

Step 53 proves that the Abel integral is genuinely integrable for
`re s > 0` and has norm at most `D / re s`. Combined with Step 52,
this yields `‖L(s,χ)‖ ≤ ‖s‖ D / re s` for the actual L-function when
`re s > 1`. Applying the same bound to the actual L-function at
`re s = 1/2` still requires an analytic-continuation identity, and
the zeta factor needs a separate estimate.

Steps 54–55 subsequently close those gaps. The character Abel identity is
continued to `re s > 0`, a critical-line zeta bound is proved, and these are
combined into unconditional strip growth and the full contour shift. Step 56
proves the actual left-line quadratic growth and closes the Gaussian error for
all sufficiently large moduli under (A). Step 57 aligns the Lemma 5.7 target
with the paper's standing large-modulus convention and proves it with constant
`1/16`; see `MIGRATION_STEP_57.md` and `audit/STEP57_STATUS.md`. The threshold
is proved to exist, but an explicit numeric/effective encoding of it is not
separately extracted.

## Phase 6 — contradiction and top theorem

The final theorem may import proved propositions, but it must not take a hypothesis of the form
`AssumptionA -> False` or an equivalent packaged version of the whole paper.

## Phase 7 — CI gate

Required checks:

- `lake build` on a pinned Lean/mathlib toolchain;
- `#print axioms` for exported theorems;
- `tools/spec_audit.py --strict`;
- no `sorry`/`admit` in trusted modules;
- no `Float` in trusted theorem statements;
- theorem-to-paper mapping reviewed in `audit/STATUS.md`.

## Reproducibility rule added in Step 02

The project must pin both `lean-toolchain` and mathlib to a release/tag or
commit.  Development against floating `master` is not accepted for a proof
artifact, because API drift makes audit results non-reproducible.
## Step 25 status

Compilation-risk cleanup is now prioritized over adding new proof content until a real Lean 4.30.0 kernel run is available. Definite v4.30 API mismatches in the trusted Spec layer were corrected, and all bootstrap/CI paths now converge on the same strict verifier. The mathematical frontier remains the Gaussian cubic-decay/summability step.
