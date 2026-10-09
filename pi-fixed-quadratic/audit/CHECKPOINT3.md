# Checkpoint 3 — exact multivariate same-field norm integrality

Follows checkpoint 2 (`4dfd4ecf9fa325346e3ec47b99367d37bceff6fe`).
The implementation proves the original finite-place argument and closes the
abstract same-field arithmetic interface. It does not prove pi finiteness.

## Exact new result

`quadratic_cleared_product_gaussian` has these explicit hypotheses:

- `G` is a field and the fraction field of `GaussianInt`;
- `K` is a number field with compatible `GaussianInt -> G -> K` algebra maps;
- `K/G` is finite-dimensional Galois with `finrank G K = 2`;
- `tau` is a nonidentity `G`-automorphism;
- `P` has Gaussian coefficients and coordinate degrees at most `e_i`;
- each integer triple `(a_i,b_i,c_i)` is primitive, expressed by gcd = 1;
- each polynomial has the actual factorization
  `a_i X^2+b_i X+c_i = a_i (X-x_i)(X-tau(x_i))` in `K[X]`.

It **concludes** that
`(product a_i^e_i)*P(x)*P(tau(x))` belongs to the image of Gaussian integers in
`K`. No integrality, Gaussian membership or norm descent is assumed.
Coordinates may repeat or depend on one another; the exponent remains `e_i`.
`quadratic_cleared_norm_one_le` adds nonzero leading coefficients, nonzero target
value and a compatible complex embedding, and concludes complex norm >= 1.
The conjugate nonzero value is derived from the same automorphism.

The proof chain is:

1. Three-coefficient Bezout -> primitive Gauss norm 1 -> local root identity.
2. Ultrametric multivariate evaluation bound -> exactly cleared local product <=1.
3. All finite places of `K` -> ring-of-integers membership -> integral over Z.
4. The actual Galois automorphism group has two elements -> `norm(q)=q*tau(q)`.
5. Proved norm descent -> integral reflection -> Gaussian integral closedness.

This avoids a valuation-extension construction: all local estimates are made
in the ambient number field itself. It includes finite places above 2.

## Verification

Ordinary Lean 4.34.1 replay: **29 compiler checks**, **73 declaration audits**.
There are 15 proof modules, one aggregate, one positive regression fixture,
one complete type/axiom fixture, and 11 separately diagnostic-matched expected
failures. Every axiom report is a subset of
`{propext, Classical.choice, Quot.sound}`. No project axiom, sorry, admit,
native_decide, unsafe code or external proof hook is used.

New regressions cover three-coefficient primitivity, nonmonic root pairs,
repeated dependent sqrt(2) coordinates and an exact `a^2` two-coordinate
Gaussian product. New expected failures reject a relative degree-four
substitution, a nonprimitive coefficient triple, and the false root-pair
factorization of beta=1/2 (whose actual other root is 1).

Checkpoint 2's new workflow and old pi aggregate succeeded; downloaded artifacts
were checked against all local source and axiom hashes and path-normalized logs.
See `checkpoint2-ci-validation.json` and
`checkpoint2-original-ci-validation.json` (23/55 and 93/622 respectively).
The root Lean kernel workflow remains separately tracked; an unfinished run
is not counted as passing. Latest ordinary replay and actual types are archived
in `local-replay-receipt.json` and `TypesAndAxioms.log`.

The original branch remains clean at cae0ad9, and all 274 protected tracked
files and original 4.30 pins were freshly checked byte-identical. Repository
placeholder and structure scans pass across 2187 Lean files.

## Remaining main-proof work

Construct the fixed real quadratic field/compositum tower and instantiate the
relative-degree-two, actual conjugate, primitive minpoly and embedding interfaces.
Combine this norm bound with the multivariate l1/Mahler envelope. Construct the
actual formal-center matrix entries and Cauchy/factorial coefficient estimate,
then port proved interpolation and analytic aggregates and enlarged parameter
limits. The rational-only upstream `FixedData` APIs do not already supply them.
No final fixed-field pi theorem or mu(pi/sqrt(d)) theorem is exported.

The separately reviewed elementary pairing proof can remove primitive and
finite-place dependencies in a later generic variant. It is not part of this
Lean checkpoint and is not a remaining obstacle to the now-proved norm result.
