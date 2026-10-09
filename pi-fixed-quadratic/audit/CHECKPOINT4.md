# Checkpoint 4 — actual formal entry and pinned upstream bridge

Follows checkpoint 3 (`f13e2cf7e0d867028042bd5be1ce7fba8105f608`).

`FormalEntry.lean` constructs the binomial-product polynomial of paper formula
(3.1), keeping time as variable 0 until coefficient extraction. The actual
elaborated types prove, over a general commutative ring:

- splitting into a time polynomial with formal-center coefficients;
- exact evaluation at any center tuple;
- zero entries for incompatible row/column exponent matches;
- coordinate degree <= alpha_i-b_i, without a degree-bound hypothesis;
- the determinant polynomial degree bound with the row rebate.

The generic `G_i` can be the actual truncated logarithms, and `c_i=2*j*I` gives
the desired centers. These constructions and proofs have no rational p/q input.
Positive regressions check the binomial factor for alpha=2,b=1 and the coefficient
of time^2 for G=time-time^2/2. An expected failure rejects removing binom(2,1).

Ordinary isolated replay passed **31** compiler checks and **84** declaration
audits: 16 proof modules, aggregate, regressions, exact type/axiom fixture and
12 diagnostic-matched expected failures. The allowed axiom set is unchanged:
`propext`, `Classical.choice`, `Quot.sound`. No project axiom, sorry/admit,
native_decide, unsafe code or external proof hook occurs.

## Direct upstream connection

`checks/UpstreamFormalEntryBridge.lean` imports the pinned upstream
`MatrixArithmetic` and proves the exact equation:

`eval beta (formalEntry (2*j*I) G s h b a)`
`= InterpolationMatrix.entry (2*I*beta) G j s b h a`.

The equation holds for every complex beta, including algebraic tuples. The
bridge was separately kernel-checked against upstream pin adc7f124...;
its full type and its one axiom report are in `UpstreamFormalEntryBridge.log`.
The bridge adds **one** fresh compiler check and declaration audit. This
cross-project fixture is **not** included in the standalone mathlib CI replay.
`scripts/audit_entry_bridge.py` reproduces it after revalidating the prior 872
upstream source/log/olean hashes and the current standalone replay hashes.
The upstream type fixture is also freshly compiled (six upstream axiom reports).
No full 869-module rebuild or Comparator run is claimed.

Checkpoint 3's standalone CI and old pi-algebraic aggregate both succeeded and
were downloaded and matched to local sources/axioms/path-normalized logs:
29/73 and 93/622 respectively. Their validation records are included here.
The whole root Lean kernel workflow is independently tracked; unfinished runs
are not counted as passing. Static placeholder and structure scans passed
across 2190 Lean files. All original 4.30 pins and 274 protected files remain
unchanged, with the original branch clean at cae0ad9.

## Remaining dependencies

This closes the actual entry/degree connection, not the full determinant
arithmetic estimate. Next: clear the actual truncated-log entry polynomial,
prove the radius-1/2 coefficient-l1/Cauchy and factorial determinant envelope,
and preserve the exact joint weighted budget and two denominator costs.
The actual fixed-field/minpoly tower instantiation and proved geometric,
analytic and parameter ports also remain. No fixed-field pi finiteness theorem
or mu(pi/sqrt(d)) theorem is exported.
