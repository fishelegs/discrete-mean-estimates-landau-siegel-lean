# General product inequality for the actual divisor functions

For every natural k,l,n, the genuine arithmetic divisor functions satisfy

    tau_k(n) * tau_l(n) <= tau_(k*l)(n).

The positive-order theorem is `lemma34_tau_product_le`; `lemma34_tau_product_le_all` also covers zero orders. Order zero is the actual Dirichlet-convolution identity, not a constant sequence. The proof uses the real multichoose recurrence at prime powers and the actual multiplicative factorization. The recurrence inequality (e+k)(e+l)<=(e+1)(e+kl) is proved for all positive k,l.

The package also proves real-cast and square forms, mixed harmonic/logarithmic sum bounds with the explicit order k*l, and harmonic energy for any coefficients genuinely bounded by B*tau_k. It does not absorb k,l-dependent powers or divisor factors into an unspecified uniform constant.

Central validation: one production module with14 declarations,14 named edge/object regressions and28 standard-only axiom checks. Orders0/1, arguments0/1, actual prime-square values, composite12, orders12/10 and40/40, and the X=1 harmonic endpoint are checked. All eight pre-existing project source and compiled-input hashes match. Whole-project build PASS5366 jobs;1513 sources pass guards;1112 SPEC/1377 full imports. Strict audit remains414 candidates, no new candidate.

[Source](../ZhangLS/Spec/Lemma34TauProduct.lean), [regressions](CloudTauProductRegression.lean), [verification](cloud_tau_product_verification.json), [axioms](cloud_tau_product_axioms.log), [hashes](cloud_tau_product_source_hashes.json).

Reproduce `lake build ZhangLS.Spec.Lemma34TauProduct`, `lake env lean -j1 audit/CloudTauProductRegression.lean`, and `lake build`.

This is a shared arithmetic lemma for the active7.1/14.1 conductor and tail estimates. It does not complete either numbered proposition. Numbered count remains34 original +2 repaired=36/51.
