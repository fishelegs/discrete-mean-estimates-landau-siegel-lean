# Original Lemma 16.2 center: quantitative conditional audit

Status: VERIFIED. Both production modules, all 12 source-expanded regressions, all 14 public-declaration axiom checks and compiler module-owner coverage passed. The only axioms are propext, Classical.choice and Quot.sound. This is a bounded conditional audit, not completion of the original Lemma 16.2 or Section 16.

The target is the displayed center formula in arXiv:2211.02515v1, TeX lines 4646–4653. Its literal main term remains

(6/π²) · φ(D)/(D·mathfrak p) · ∏_{q|D} q/(q+1),

where mathfrak p is lemma161MainTerm χ, including the exceptional χ(2)=1 branch with its literal factor 2 and its product over q>2. Although the existing function is named lemma162CorrectedCenterMain, it is precisely this unchanged source expression; the regressions expand it literally.

## Exact quantitative result

Let B = lemma152ProductBound, the existing positive exponential of a convergent prime majorant, and let E = exp(2/log 2). The exact absolute constant is

K = 6 / (π² · (2B) · E²) > 0.

For every actual primitive real character χ modulo D with log D > 1, the packet proves

K/(1+log log D)^12 ≤ |(6/π²) · φ(D)/(D·mathfrak p) · ∏_{q|D} q/(q+1)|.

The arithmetic proof uses the existing uniform reciprocal-totient estimate, the exact finite product inequality ∏_{q|D} q/(q+1) ≥ φ(D)/D, and |mathfrak p| ≤ 2B. It does not drop ramified factors or the prime 2. No numerical approximation is used for K, E or B.

For every fixed error constant C and every fixed c′>0, one modulus threshold D₀ is chosen before D, χ, the shift index j and U. For every D≥D₀, every actual primitive real χ, both original shifts β₁ and β₂ with that same c′, and every U continuous at 1 and agreeing on Re(s)>1 with the actual source Dirichlet series divided by ζ(s)^3 L(s,χ)^3, the conclusion is

C/(log D)^4 < |U(1) − source main term|.

The existing stage-2 theorem forces U(1)=0; the new lower bound proves the strict inequality. The actual source arithmetic/Euler bridge is an already proved dependency, not an assumed corrected factorization. A separate theorem supplies an explicit continuous old extension for every actual χ, along with its quotient agreement and strict error.

## Conditional source scope and limits

The source-scoped theorem explicitly retains NormalizedAssumptionA χ, namely L(1,χ)<(log D)^−2022 from source lines 345–348. Source line 1560 makes (A) a standing hypothesis for the rest of the paper. Another theorem starts from the exact original Lemma162OriginalContinuation, deriving continuity and quotient agreement from that premise. The compatible constant from the proved original Lemma 5.2 can be selected before all error constants and thresholds.

No theorem in this packet asserts that an (A)-character exists, that such characters occur for arbitrarily large D, or that an old analytic continuation exists on the full printed strip. The concrete extension theorem establishes continuity at 1 only. The universal estimate applies to every actual primitive real character without needing (A); that broader theorem is not a counterexample satisfying (A).

Precisely, if a source-admissible (A)-character and a claimed old continuation exist at D beyond the threshold for the proposed uniform C and c′, then the printed center error bound cannot also hold there. In the absence of such an existence witness, this packet does not prove the negation of an asymptotic theorem universally conditional on (A), and it does not prove the paper's main theorem false. No proof uses a theorem of not-(A) or obtains the result by vacuity.

The paper's remaining Section 16 Mellin, contour, truncation, unsmoothing and aggregate-error work is outside this bounded audit. The original formula has not been silently replaced by the repaired factorization.


Central integration subsequently rebuilt both modules and the actual-a lower-bound module, all four audit drivers, and the full 5565-job project. All 18 combined declarations have only the standard three axioms and all 18 expanded regressions pass. No mathematical proof changes were made during import qualification.
