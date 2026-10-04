# Finite Möbius / Heath–Brown identity: scoped Lean PASS

The universal finite identity is now proved in [FiniteMobius.lean](../../ZhangLS/Spec/FiniteMobius.lean). For every positive J and n<=U^J, it uses the literal sharp truncation m_U(n)=mu(n)1_(n<=U). The J=4 coefficients are exactly (4,-6,4,-1). Complex coefficients, the inclusive endpoint and n=1 are checked separately.

Central fresh compilation, semantic regression, and an exact audit of all 23 owned declarations (19 public) pass. All transitive axioms are among propext, Classical.choice, Quot.sound. The module has three direct Mathlib imports and no other ZhangLS imports; the actual loaded environment contains 3293 modules. [Verification scope](VERIFICATION.json) and [semantic review](SEMANTIC_REVIEW.md) record the boundaries.

This is a focused verification after the execution environment was replaced. The existing full project is still undergoing controlled fresh revalidation. This scoped PASS does not assert a new full-project PASS. The numbered ledger remains 37 original + 3 repaired = 40/51.

The finite arithmetic identity supports the accepted [multilinear decomposition](../multilinear_completion/STATUS.md). It does not prove its analytic completion estimates, the new weighted square-factor tail, the remaining weak-pair arithmetic covariance, or the final strict signed half-norm inequality.

## Reproduce

With the repository-pinned Lean 4.30.0 and Mathlib dependency:

    lake build ZhangLS.Spec.FiniteMobius
    lake env lean audit/CloudFiniteMobiusChecks.lean
    lake env lean audit/CloudFiniteMobiusAxioms.lean > finite-mobius-axioms.log
    python3 audit/finite_mobius/check_audit.py finite-mobius-axioms.log
    python3 audit/finite_mobius/verify_package.py

The independent exact integer regressions are supplementary finite checks; the universal identity is established by the Lean proof.
