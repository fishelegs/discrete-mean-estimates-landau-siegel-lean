# Migration step 01 — foundations

Implemented in this patch:

1. Added a project-wide repair plan (`FORMALIZATION_PLAN.md`).
2. Added the theorem migration ledger (`audit/STATUS.md`).
3. Added a static proof-surrogate scanner (`tools/spec_audit.py`).
4. Added a trusted character specification based on mathlib's actual
   `DirichletCharacter ℝ D` and `DirichletCharacter.IsPrimitive`.
5. Added an actual infinite Dirichlet L-series expression and a separately named
   termwise-derivative series.  No derivative lower bound is embedded in either definition.
6. Added `audit/LegacyAssumptionARegression.lean`, which records that the old Assumption A
   is definitionally impossible up to elementary linear arithmetic.

Not claimed complete:

- compilation has not been executed in this environment because `lean`/`lake` is absent;
- convergence of the L-series has not yet been proved;
- termwise differentiation has not yet been proved;
- the analytic continuation/value-at-one bridge is not yet implemented;
- legacy theorem modules have deliberately not been rewired to SPEC yet.

Next implementation step:

- pin the Lean/mathlib revision;
- make the new SPEC modules compile;
- prove character-value bounds and absolute convergence for `s > 1`;
- only then introduce the trusted statement of Assumption (A) used by downstream modules.
