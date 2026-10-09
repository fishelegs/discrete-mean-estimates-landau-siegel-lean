# CP9: actual complex-center geometry through nonzero minors

Partial formalization. No final fixed-field pi finiteness theorem is claimed.

## Exact proved endpoint

`FixedQuadratic.fixed_field_cofinal_nonzero_minor` uses actual centers
`2*I*beta_i` and `ceil(log primitiveMinpolyHeight(beta_i))` weights. Given
explicit positive rational geometry, inflated volume/fibre conditions,
separated weight products and a truncation tail budget, for every real L it
proves existence of H >= L and an injective full-row column selection whose
literal truncated-log matrix determinant is nonzero. Surjectivity, ampleness
and nonzero-minor conclusions are not assumptions in this endpoint.

The supporting chain extracts `FixedFieldGeometryData` from the rational-only
upstream data type, derives its arbitrary-center curve inequality, constructs
compactification and blowup, proves exact curve degree identities and uniform
margin, applies numerical ampleness, obtains jet surjectivity and weighted
formal packets, and proves cofinal literal matrix surjectivity. The full record
and 155 declaration types/axioms appear in the committed GeometryAudit log.

## Evidence

Separate ordinary Lean 4.34.1 replay: 17 proof modules, aggregate, positive
numeric geometry regression, all-declaration type/axiom audit, 2 diagnostic
negative fixtures = 22 new compiler checks. All 155 axiom reports are subsets
of propext/Classical.choice/Quot.sound. No sorry, admit, new axiom,
native_decide, unsafe or other trust bypass. `geometry-port-audit.json` records
all source/log/olean hashes and compiler exits. Its prerequisites revalidate the
existing 50/265 arithmetic core receipt and 872 pinned upstream receipts;
these are reused checks, not 872 fresh builds. Six upstream API audits and
five entry-bridge audits are freshly printed separately.

CP8 focused arithmetic CI 37896844437 and preserved original pi CI
37896844425 completed successfully. Downloaded receipts, source/log hashes
and type/axiom outputs match local replay after source-path normalization;
validation files are committed here. CP5--CP8 whole-repository CI remain
running at this checkpoint. The 22 geometry checks are a separate local
upstream-dependent replay, not part of the 50-check focused Linux CI.

Protected 4.30 pins and all 274 preservation hashes still match; the original
checkout remains clean at cae0ad9b2069acf3c8814b31af36a1842519ce9e.

## Remaining dependencies

The endpoint retains explicit geometry and tail conditions. They must be
constructed from the same successively selected exceptional approximants and
the changed error budget. Complete analytic determinant expansion, collision,
summation and remainder transfer is being implemented separately. Then connect
both bounds and geometric existence, discharge all parameter margins and
prove the exceptional set finite. No conditional interface is called a pi
theorem; no paper-level hypothesis has been introduced as an axiom.
