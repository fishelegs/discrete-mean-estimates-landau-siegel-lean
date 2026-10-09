# Checkpoint 6 — actual height and normalized arithmetic

This is a partial Lean checkpoint, not the fixed-field pi finiteness theorem.

- 26 proof modules, aggregate, positive regressions, actual type/axiom audit,
  and 15 diagnostic-matched expected failures: **44 checks / 219 declarations**.
- Exact actual-minor theorem: `formal_minor_fixed_field_normalized_lower`.
  It derives the displayed normalized estimate from the already proved norm,
  actual truncated-log clearing and factorial coefficient bound. Inputs left
  visible are the degree-two Gaussian fraction-field/Galois tower, primitive
  root-pair data, compatible complex embedding, actual nonzero minor, geometric
  weighted budgets and Mahler-to-weight bound. No norm-integrality hypothesis.
- Actual primitive integer minpoly and max height: degree two, primitive,
  irreducible, positive leading coefficient, gcd 1, real conjugate/factorization,
  coefficient box, unbounded height, Mahler and rounded-log bounds all proved.
- Successive centers are selected from the actual infinite degree-two set
  against arbitrary previous-weight thresholds; zero centers are excluded.
- Changed error identity and dimension margin use `Lambda=log 4+4`,
  `C_k=2k+2`, `log(3/2)/w0`, and both Q costs. Joint degree control also improves
  the coarse denominator estimate, giving `log Q/D <= Lambda*(F/v+1/wmin)`.
- Dimension is fixed first using actual floor-power K; the complete remaining
  height coefficient is then fixed and absorbed by a common lower weight.
  Polynomial row growth gives the final factorial remainder limit in N.
- Expected failures additionally prohibit using the degree-two construction
  on a rational zero and dropping the second denominator log cost.
- Only `propext`, `Classical.choice`, `Quot.sound`; no sorry/admit/new axioms,
  native_decide, unsafe declarations or external proof hooks.
- Separate fresh upstream bridge checks five actual types/axioms. The 872
  prior upstream source/log/olean receipts are rehashed, with six fresh API
  axiom reports. This is not 872 fresh compilations or a Comparator run.
- CP5 CI artifacts validate 38/148 focused and 93/622 old-pi checks. CP2 whole
  kernel run 37883746053 completed success: 1565 trusted Spec modules, Spec
  aggregate, lake build, audit regressions and Gaussian closure. Later whole
  kernel runs remain separately tracked; no in-progress run is counted passed.

Remaining: actual fixed real quadratic field F(i)/Gaussian fraction field
tower and involution, primitive root data instantiation there, generalized
complex-center geometry and analytic aggregate, actual packet count/budget
instantiation and the final exceptional-set contradiction/finiteness theorem.
