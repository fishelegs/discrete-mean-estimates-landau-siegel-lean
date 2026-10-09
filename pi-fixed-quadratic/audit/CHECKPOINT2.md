# Checkpoint 2 — independent sign parity and square-root evaluation

Build follows checkpoint 1 (`e3ee00d6c4053690a19a8be2e6a1683f5d8132a7`).
Ordinary Lean 4.34.1 verification passed: **23** compiler invocations, with
12 proof modules, one aggregate, positive regressions, actual type/axiom
checks and eight diagnostic-matched expected failures. All **55** exported
declarations use only the allowed standard axioms. No project axiom, sorry,
admit, native_decide, unsafe code or external proof hook occurs.

The actual type audit uses `#check @declaration` for complete signatures and
`#print axioms`; proof terms need not be dumped to inspect a theorem type.
The first checkpoint's original longer type/proof print remains available in
its Git commit. The latest local receipt and compact types are in
`local-replay-receipt.json` and `TypesAndAxioms.log`.

New statements: explicit even/odd polynomial factorization, Gaussian integer
values or alpha-times-Gaussian values at alpha^2=d, nonzero norm >=1 for alpha>=1,
and a generic determinant row-permutation bridge. Exact hypotheses, including
the unproved actual interpolation packet symmetry, remain visible.
The counterexample `3-2X` at sqrt(2) makes the parity hypothesis substantive.

Checkpoint 1's new-subproject GitHub workflow and original pi-algebraic
aggregate both succeeded. The new workflow's downloaded artifact matched all
18 local compiler results and all 42 axiom audits (see
`checkpoint1-ci-validation.json`). The original root project CI is a separate
run and is not asserted successful until its completion is actually observed.

Neither the original fixed-field pi finiteness theorem nor mu(pi/sqrt(d))=2 is
formalized here. Original same-field norm integrality and geometric/analytic
ports remain pending; the independent parity path additionally needs the actual
paired-row packet. README.md identifies the exact scopes and remaining work.
