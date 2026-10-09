# CP10: complete literal analytic transfer and a common actual minor

Partial formalization, not a fixed-field pi finiteness theorem.

## Proved results

`FixedFieldAnalyticData` uses actual degree-two coordinates in one real field,
actual primitive-minimal-polynomial maximum heights, the asserted approximation
inequality and explicit scalar parameters. It contains no assumed determinant
bound, translation expansion, collision bound, remainder limit or geometry.

The literal analytic port proves the exact finite row/determinant expansion,
height-linked scalar bound with exp(nu) ceiling cost, holomorphic collision
bound, two-alternative saving, polynomial term count, summation bound and a
vanishing analytic remainder. It also proves the actual factorial arithmetic
remainder vanishes for real auxiliary degrees and the collision-rate limit.

`actual_minor_two_sided` applies the proved fixed-field norm/Mahler lower bound
and the complete analytic upper bound to one common actual determinant with
one actual row rebate. `cofinal_nonzero_actual_minor` derives actual minor
existence from CP9 geometry with the same height weights and actual ceiling
tail orders. `no_geometric_packet` derives False by combining that proved
existence, the two bounds and their vanishing remainders, under explicitly
stated elementary geometry conditions and strict total-error/collision
margins. These inputs still need construction from an infinite exceptional
set; this conditional packet contradiction is not named a final pi theorem.

## Validation

Separate ordinary Lean 4.34.1 replay: six proof modules, aggregate, positive
exact-changed-budget regression, 61-type/axiom audit and two expected failures:
11 new compiler checks. All 61 axiom sets are subsets of propext,
Classical.choice, Quot.sound. No sorry, admit, new axiom, native_decide, unsafe
or other bypass. Source/log/olean hashes and actual compiler exits are in
`analysis-port-audit.json`; full types and record fields are in its committed
logs. Reused core, CP8 arithmetic/row-scalar and CP9 geometry receipts are
rehash-validated, not counted as freshly rebuilt here. 872 upstream receipt
hashes are revalidated; six exact upstream API reports are freshly printed.

CP9 focused arithmetic CI 37901252361 passed 50 checks/265 declarations;
original pi aggregate CI 37901252353 passed 93 checks/622 declarations.
Downloaded receipts/logs/source hashes/axioms match local after source-path
normalization. Whole-repository CP5 CI 37889982449 has now completed successfully; its
artifact verification is in progress. CP6--CP9 root CI remain running, with no
completion claim. New geometry/analysis ports are separately verified local replays,
not included in the 50-check focused Linux CI.

## Remaining work

Construct parameters and the successively selected exceptional coordinates
meeting all explicit geometry and strict changed-error margins in
`no_geometric_packet`; then conclude finiteness for fixed F, nu > 2. No paper
hypothesis is introduced as an axiom, and no conditional interface is claimed
as the final pi result. Old 4.30 pins and verified A7/W2/sqrt(2)/Log-Pade
sources remain protected by the 274-file preservation audit.
