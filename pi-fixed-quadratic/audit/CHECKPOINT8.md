# Checkpoint 8 — actual packet arithmetic, counts and row scalars

Partial Lean formalization. No fixed-field pi finiteness theorem.

The core is unchanged from CP7, whose focused CI attempt 2 passed 50 checks /
265 actual declaration audits; the previous attempt failed during network
installation before Lean replay. Its logs match the full local ordinary replay
after source-path normalization. The separate old-pi CI passed 93 checks /
622 declarations with matching source/log/axiom reports. Both validations are
committed here. The installer now fails correctly on download error and uses
finite network retries, in the same normal checkpoint commit.

Fresh executable continuation:

- legal actual row/column packet budgets; actual rebate in [0,theta];
- actual selected upstream matrix determinant normalized arithmetic bound;
- actual primitive-height row-count and row/low-index ratio limits;
- actual primitive-height approximation -> exact exponential center error;
- source row-scalar translation estimate with actual ceiling tail orders;
- diagnostic-matched expected failure when exp(nu) rounding cost is dropped.

`scripts/audit_packet_analysis.py` rehashes the fully replayed 50-check core,
revalidates 872 original upstream receipts, freshly checks six upstream APIs
and the five-declaration exact entry bridge, then compiles the two new bridge
modules and one expected failure. Nine new exact type/axiom reports permit only
propext, Classical.choice and Quot.sound. No sorry/admit/new axiom, native_decide,
unsafe declaration or external proof hook. The OAI-dependent bridge replay is
separate from focused Linux CI and is not counted as part of its 50 checks.

Remaining: arbitrary-center compactification/blowup and jet surjectivity,
translated determinant expansion and full collision/holomorphic analytic
aggregate, actual remainders/parameters assembly and exceptional-set finiteness.
The actual nonzero minor is still an input, not assumed to exist by a hidden
surjectivity axiom. Whole-kernel CI for later commits may remain pending;
previous successful full-kernel CP2/CP4 validation is retained separately.
