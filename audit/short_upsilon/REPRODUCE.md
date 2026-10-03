# Reproduction and trust boundary

Run `lake build`, then `lake env lean -j1 audit/CloudShortUpsilonAxioms.lean`, followed by the repository placeholder, source-structure, generated-import and strict-audit checks. The strict heuristic check deliberately returns1 for the existing442 reviewed candidates; this release adds none.

The audit driver checks the exact56 public declarations, all80 declarations owned by the five new proof/regression modules, all five nonempty owner inventories, and the allowed three standard axioms. It also prints full public types and direct proof-term references. The published inventory makes omitted or extra owned declarations detectable. No custom axiom, sorry, admit or native_decide was added.

Run `python3 -B audit/short_upsilon/check_actual.py` for the separate finite arithmetic regressions. They include ramified characters of conductors3,5,8,12, N=0 and both sides of the closed D^4 cutoff, with56 endpoint cases through22000. These are not simulations of assumption(A); the uniform analytic bounds are proved by Lean.

The central source/object pin check covered6067 external modules. The original manifest has6073 nodes including its audit root, while the imported Lean header has6072 modules. The proof package was integrated onto the recorded base commit and the whole project passed5709 build jobs. `cloud_short_upsilon_verification.json` records source and log fingerprints, counters and command outcomes. Binary caches and third-party source copies are deliberately not part of this evidence package.
