# Fixed quadratic field: ordinary Lean checkpoint

**Partial formalization, not a proof of the fixed-field pi finiteness theorem.**
The paper proof supplied on 2026-10-09 remains the target. No new mathematical
axiom is declared, and no hypothesis asserting the desired multivariate norm
integrality has been hidden in a final pi theorem. No such final theorem is
exported here.

This subproject uses **Lean 4.34.1** and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, matching the isolated, previously
verified openai/math PiExponent project at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The enclosing repository's Lean/Mathlib 4.30.0 files and its A7, W2, sqrt(2),
weighted-colon, and Log-Pade checkpoints are preserved. This subproject does not
import the upstream PiExponent proof; a separate audit reads its actual APIs.

## Proved statements

The exact elaborated types and complete axiom reports are printed by
`checks/Audit.lean`; `scripts/replay.py` verifies every exported declaration.

- `quadratic_resultant_identity` (in namespace `FixedQuadratic`): for
  Gaussian-coefficient polynomials `f,P`, `natDegree P <= d`, and the explicit
  complex factorization `map f = C a * (X-C x)*(X-C y)`,
  `cast (resultant f P 2 d) = a^d * eval(map P,x) * eval(map P,y)`.
  `quadratic_product_gaussian` derives membership in the Gaussian-integer range
  from this identity. Integrality is proved, not assumed.
- `quadratic_norm_lower`: with `a`, both displayed evaluations nonzero, the
  product of their norms and `norm(a)^d` is at least 1. The conjugate nonzero
  hypothesis is explicit; this theorem alone does not construct a quadratic
  field or its automorphism.
- `quadratic_l1_mahler_lower`: the same hypotheses imply
  `R^d / (B * (norm(a)*R*S)^d) <= norm(eval(map P,x))`, where
  `R=max(1,norm x)`, `S=max(1,norm y)`, and `B` is the coefficient-l1 norm.
  This uses one coefficient cost and the exact leading exponent `d`.
- `quadraticMahler_le_l2` and `quadraticMahler_le_sqrt_three_height`: with real
  roots, `a>=0`, `b=-a*(x+y)`, `c=a*x*y`, and coefficient bounds by `H>=0`,
  `a*max(1,abs x)*max(1,abs y) <= sqrt(a^2+b^2+c^2) <= sqrt(3)*H`.
  These are elementary quadratic identities; no Jensen theorem is assumed.
- `simultaneous_conjugate_ne_zero`: evaluation is nonzero after one field
  automorphism that fixes the coefficient homomorphism, regardless of
  coordinate dependencies. `cartesian_trap` verifies the repeated sqrt(2)
  example: target nonzero, mixed tuple zero, genuine simultaneous product -8.
- `multi_eval_norm_le`: for a complex multivariate polynomial with coordinate
  degrees bounded by `e_i`, its value has norm at most
  `B * product_i max(1,norm beta_i)^e_i`.
- `det_degreeOf_le`, `row_total_le_column_total`, `weighted_rebate`: a
  determinant polynomial whose entries vanish on incompatible matches has
  coordinate degree at most `e_i=sum columns alpha_i - sum rows b_i`; a nonzero
  determinant implies the row totals do not exceed the column totals. The
  weighted total equals the column total minus the row total. Actual degree
  equality is not claimed.
- `determinant_clearing`: for any subring, if each compatible entry is cleared
  by `product L_i^(alpha_i-b_i)`, the entire determinant is cleared by
  `product L_i^e_i`. This is a proved generic transport theorem; the actual
  truncated-log entry polynomial and its clearing membership still need to be
  constructed. It can specialize to a Gaussian-coefficient polynomial subring.
- `finite_boundedQuadraticRoots`: positive-leading integer quadratic roots
  with all coefficient magnitudes bounded by a fixed natural `H` form a finite
  set, even without primitivity or irreducibility. `height_unbounded_of_infinite`
  explicitly takes the coefficient-box property for a height function and
  derives unbounded heights. The canonical primitive-minimal-polynomial height
  has not yet been constructed and connected to that property.
- `height_rpow_le_rounded_exp`, `quadratic_center_period_error`, and
  `quadratic_centers_injective`: the actual input
  `abs(pi-beta)<=H^(-nu)` transfers to the period-center error bound
  `2*k*exp(nu)*exp(-nu*ceil(log H))`, and each nonzero center gives distinct
  multiples. These use `H>=1`, `nu>=0`, and `j<=k`.
- `primitive_quadratic_root_identity`: a primitive integer quadratic factored
  over a field satisfies `v(a)*max(1,v(x))*max(1,v(y))=1` for **every**
  nonarchimedean real absolute value. Three-coefficient Bezout proves the unit
  Gauss norm; no finite-place exception, including above 2, is assumed.
- `cleared_product_nonarch_le_one` and `cleared_product_isIntegral`: with
  coordinate degrees `<=e_i` and the root-pair factorizations, the product
  `(product a_i^e_i)*P(x)*P(y)` is locally bounded by 1 and is an algebraic
  integer in an ambient number field. Integrality is a conclusion.
- `quadratic_cleared_product_gaussian`: if `G` is the fraction field of
  Gaussian integers, `K/G` is a degree-two Galois number-field extension, and
  `tau` is a nonidentity `G`-automorphism, the factorizations with pairs
  `(x_i,tau(x_i))` imply that the exactly cleared product belongs to the image
  of Gaussian integers in `K`. It assumes no integrality or descent conclusion.
  Descent is proved using the actual two-automorphism norm, followed by
  integrality reflection and Gaussian integral closedness. The number of
  coordinates may be arbitrary and they may coincide or depend on each other.
- `quadratic_cleared_norm_one_le`: additionally, nonzero leading coefficients,
  a nonzero target value and a compatible complex embedding imply the product
  of the target/conjugate norms and the exact leading-coefficient factors is
  at least 1. Simultaneous nonvanishing is proved, not separately assumed.
- `comparison_contradiction`: the explicitly stated normalized lower/upper
  scalar estimates contradict the two strict margins. It assumes those
  estimates and margins and concludes `False`; it is **not** named or used as
  a fixed-field pi theorem.

## Remaining dependencies, in implementation order

1. Construct a fixed real quadratic field, its simultaneous involution and the
   primitive integer minimal polynomials of all selected elements. Connect the
   exact polynomial maximum height and root coefficient identities.
2. Instantiate the now-proved **multivariate same-field** Gaussian integrality
   theorem for the actual fixed real quadratic field after adjoining `i`.
   Construct its compatible fraction-field tower, relative degree two, Galois
   involution, complex embedding and primitive root-pair factorizations.
   These are mathematical structure obligations, not an unproved norm-integrality
   hypothesis. Combine its exact `e_i` factors with the multivariate coefficient
   envelope and Mahler bounds. Full Cartesian resultants remain invalid.
3. `FormalEntry.lean` now constructs the actual binomial-product formal entry,
   proves its complex specialization, incompatible zero rule, coordinate degree
   bound and determinant rebate. Instantiate the source's weighted row/column
   packet, and prove clearing for the actual truncated-log polynomials. Prove the coefficient-l1 Cauchy estimate at radius 1/2,
   the determinant factorial envelope, and the normalized errors with two
   denominator costs.
4. Generalize the upstream **proved Lean** geometric surjectivity and analytic
   aggregate from rational `FixedData` to height-linked fixed-field data. The
   upstream complex-center minor extraction is conditional on surjectivity;
   it does not itself prove the needed generalized geometric input. Audit the
   underlying geometry rather than treating the paper statement as an axiom.
5. Prove the enlarged dimension error limits, successive height choices and
   factorial remainder limit, then supply the estimates and margins to
   `comparison_contradiction` and conclude exceptional-set finiteness.

The target fixes the field and `nu>2` before choosing the packet. It does not
concern varying quadratic fields, pi BA/non-BA, a degree-exactly-two lower
exponent, or a height defined using absolute Weil height.

## Reproduction

With dependencies provisioned from this subproject's committed manifest:

```sh
lake exe cache get
python3 scripts/replay.py --lean "$(elan which lean)" \
  --mathlib "$PWD/.lake/packages/mathlib" \
  --packages-dir "$PWD/.lake/packages" --out /tmp/fixed-quadratic-replay
```

The script compiles all new sources and the aggregate, positive regressions,
actual type/axiom prints, and twelve separately checked expected failures. It
rejects `sorry`, `admit`, project `axiom`, `native_decide`, unsafe code and
external proof hooks. Only `propext`, `Classical.choice`, `Quot.sound` are allowed
in axiom reports. It records source, compiler, imported cache and output hashes.

For the existing isolated upstream verification workspace, run
`scripts/audit_upstream.py --verification-root <existing-workspace> --out <output>`.
This rechecks all 872 prior successful source/log/output hashes and freshly
compiles `checks/UpstreamAudit.lean`. It does not rerun full Comparator or
rebuild the entire old 869-module closure.

The new CI workflow runs this subproject on Linux; the existing pi-algebraic
workflow also runs its original 93-check aggregate on changes here. The two
jobs retain separate toolchains. Passing these checks verifies the listed
checkpoint only, not the unfinished target theorem.

## Independent parity checkpoint

`Parity.lean` proves the newly supplied algebraic lemma directly:

- if `P.comp (-X)=P`, then `P=(P.contract 2).comp (X^2)`;
- if `P.comp (-X)=-P`, then `P=X*Q.comp (X^2)` for a Gaussian polynomial `Q`;
- if either sign identity holds, `alpha^2=d` for a natural `d`, `alpha>=1`, and
  the complex evaluation is nonzero, then its complex norm is at least 1.

`ParityDeterminant.lean` also proves a generic determinant bridge: if a **given
Gaussian-polynomial square matrix** transforms entrywise by a **given** index
permutation under `X -> -X`, its determinant has sign parity. Thus the same
nonzero evaluation lower bound applies. The row permutation identity is an
explicit input, not a claim that the actual interpolation matrix has already
been constructed or verified.

Positive regressions cover both parity branches at sqrt(2). The explicit
non-parity polynomial `3-2X` evaluates to a number of norm less than 1 there.
Expected failures prevent removing the sign hypothesis, the odd factor `X`,
or the nonzero evaluation condition.

This independent algebraic work does not prove `mu(pi/sqrt(d))=2`. Remaining
work for that proposed paper extension is the actual paired +/-j row packet,
its entrywise sign-substitution identity after clearing, surjectivity under
those centers, and analytic/parameter transfer. It also does not discharge
the actual fixed-field instantiation and packet obligations:
general elements of Q(sqrt(d)) have rational offsets, and sign substitution
need not send such a center to its negative. No BA result is asserted.

## Same-field norm checkpoint

The third checkpoint follows the original finite-place proof, now closed at the
abstract arithmetic interface. In particular, the exact exponent is `e_i`,
not `2*e_i`, and no independent Cartesian conjugates are introduced.
`quadratic_norm_identity` proves that the true relative norm is `q*tau(q)`
using relative degree two. A degree-four substitution and the false repeated-root factorization of the
base-field root 1/2 are expected failures.
Positive regressions include nonmonic local roots, three-coefficient Bezout,
and two repeated coordinates cleared by `a^2`.

The independently reviewed elementary monomial-pairing alternative could
remove primitivity and finite-place dependencies from a later proof variant.
It is not required for this checkpoint, and is not counted as Lean verified.
The current theorem's primitive gcd and explicit root-pair factorization
hypotheses remain in the actual type. A mere quadratic root equation for a
base-field element does not supply that factorization.

## Formal entry checkpoint

`formalEntry` represents formula (3.1) over a general commutative ring, with
variable 0 reserved for time before coefficient extraction and successor
variables for formal centers. `formalEntry_eval` proves its exact specialization;
`formalEntry_degree` proves degree <= alpha_i-b_i without a degree hypothesis.
`formal_minor_degree` connects the actual entry construction to the determinant
budget already proved. The arbitrary logarithm polynomials can be specialized
to truncated log; no p/q assumption is present in these proofs.

Regressions check the binomial factor at j=1, alpha=2, b=1 and the time-degree-2
coefficient of t-t^2/2. An expected failure rejects deleting binom(2,1).
This checkpoint does not yet prove the actual log-polynomial clearing, Cauchy
coefficient-l1 envelope, weighted-packet nonzero minor or full interpolation
and analytic transfer.

To kernel-check the exact pinned upstream entry bridge after the standalone
replay, use `scripts/audit_entry_bridge.py --verification-root <existing-upstream>
--checkpoint-verification <replay-output> --out <separate-output>`. It revalidates
both caches and compiles the bridge; the standalone CI does not contain this
cross-project fixture. See `audit/CHECKPOINT4.md` and `audit/entry-bridge-audit.json`.
