# Verified full Section 8 xi-factor replacement

The actual full second-inner-sum replacement changes the literal Section 8 smoothed-coefficient expression by **o(alpha)**. Both P1/T<=dr<P1 and P2/T<=dr<P2 boundary layers, equality at the left cutoff, all mixed iota terms and the actual first factor are included. This supplies the previously named boundary target with a genuine proof, not an assumed envelope.

The final interface is `lemma84_section8_full_xi_replacement_little_o`. Direct right-line Perron proves the small-x bound, the exact arithmetic band has width at most 2+logT, and the total boundary error is C(1+9logL)^K(logT)^5 L^-15. The identity (logT)^10=L^11 and proved polylog absorption give the required o(alpha). Constants are fixed before D and character. See the [full mathematical scope](CLOUD_LEMMA84_BOUNDARY_SCOPE.md).

## Central checks

- Six production modules; 21 public declaration checks use only propext, Classical.choice and Quot.sound
- One direct capstone regression plus source-weight, cutoff, target and endpoint interface checks
- Focused dependency build: 3984 jobs PASS; full project: 5181 jobs PASS
- 1303 Lean source files; placeholder and structure guards PASS; 927 SPEC and1192 full aggregate imports
- Strict audit remains389 candidates/nonzero exit; no new candidate relative to the preceding weighted-interior package
- Frozen source hashes remained unchanged during central validation. [Verification record](cloud_lemma84_boundary_verification.json), [axioms](cloud_lemma84_boundary_axioms.log), [source hashes](cloud_lemma84_boundary_source_hashes.json)

Reproduce with `lake build ZhangLS.Spec.Lemma84BoundaryLittleO`, `lake env lean audit/CloudLemma84BoundaryRegression.lean`, and `lake build`.

## Remaining scope

Original Lemma8.4 uniform additive L^-6 is unchanged and unproved. The first-factor replacement, coefficient identity(8.10), varying-D arithmetic summation/partial integration to(8.11), and the independent Proposition7.1 support interface remain open. The numerical Section8 obstruction independently blocks the current final argument. This is a genuine local repair-compatibility component; numbered completion stays **34 original +2 repaired =36/51**.
