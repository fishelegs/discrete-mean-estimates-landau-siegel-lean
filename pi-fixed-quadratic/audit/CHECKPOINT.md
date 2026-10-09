# Checkpoint 1 — partial fixed-quadratic arithmetic

Ordinary Lean 4.34.1 verification passed: 18 compiler invocations, comprising
10 proof modules, one aggregate, positive regressions, the exact type/axiom
fixture, and five diagnostic-matched expected failures. All 42 exported
proof/definition/regression declarations use only `propext`, `Classical.choice`,
`Quot.sound`; there is no project axiom, sorry, admit, or native_decide.

The protected original Lean 4.30 aggregate was freshly replayed and passed:
93 compilation checks and 622 declaration axiom audits. Preservation hashes
cover 274 original files. The original branch remains clean at cae0ad9.
The upstream dependency audit revalidated 872 existing successful checks by
source, log, and olean hash, then freshly compiled one six-axiom-report fixture.
These are ordinary Lean checks; full Comparator was not run.

Exact statements: `TypesAndAxioms.log`; compiler commands, pins, exit codes and
hashes: `local-replay-receipt.json`; preserved inputs: `preservation.json`;
upstream API and axioms: `UpstreamAudit.log` and `upstream-audit.json`.

This checkpoint does not establish fixed-field pi finiteness. Its principal
remaining dependencies are the same-field multivariate primitive norm
integrality proof and the generalized upstream geometric/analytic interfaces.
README.md lists all hypotheses and the further coefficient/parameter work.
GitHub CI results are checked after pushing this checkpoint; this local report
does not assert a not-yet-observed CI outcome.
