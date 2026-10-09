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
weighted-colon, and Log-Pade checkpoints are preserved. The arithmetic core does not import upstream PiExponent. The separately replayed
geometry and analysis ports reuse its hash-audited Lean closure and exact APIs.

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
  `product L_i^e_i`. This generic transport theorem is now instantiated for the actual
  truncated-log entries by `formal_minor_truncatedLog_cleared_gaussian`.
- `finite_boundedQuadraticRoots`: positive-leading integer quadratic roots
  with all coefficient magnitudes bounded by a fixed natural `H` form a finite
  set, even without primitivity or irreducibility. `height_unbounded_of_infinite`
  explicitly takes the coefficient-box property for a height function and
  derives unbounded heights. The canonical primitive-minimal-polynomial height is now constructed and
  connected to that property by `PrimitiveHeight.lean`. Its irreducibility,
  primitivity, positive leading coefficient, three-coefficient gcd, actual
  real factorization, Mahler bound, and height-linked ceiling log bound are proved.
  `Selection.lean` proves successive selection from an infinite degree-two set
  for every center-independent threshold depending on previous weights.
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

1. The actual fixed-field arithmetic construction is now complete in
   `GaussianField.lean`, `Complexification.lean`, `FieldMinpoly.lean` and
   `FixedFieldArithmetic.lean`: for a real intermediate field `F` of degree
   two, construct `F(i)`, the Gaussian fraction field, relative degree two,
   Galois structure, simultaneous nonidentity involution, compatible complex
   embedding and actual primitive root-pair factorizations. No tower, norm
   integrality, relative degree, root-pair or Mahler-to-weight assumption remains
   in `fixed_real_field_minor_normalized_lower`.
2. `fixed_real_field_multi_mahler_lower` and
   `fixed_real_field_multi_height_lower` prove the actual same-field bounds for
   arbitrary dependent degree-two coordinates. There is one coefficient-l1
   factor and the leading-coefficient exponents are the coordinate degree caps.
   The primitive maximum height is used, not absolute Weil height. Repeated
   sqrt(2) regression verifies relative degree two and simultaneous product -8.
3. `FormalEntry.lean` now constructs the actual binomial-product formal entry,
   proves its complex specialization, incompatible zero rule, coordinate degree
   bound and determinant rebate. Actual truncated-log clearing, radius-1/2
   coefficient envelope and factorial envelope are now proved. Instantiate the
   source's weighted row/column packet. The normalized actual-minor estimate
   is now `formal_minor_fixed_field_normalized_lower`, with both denominator
   costs and explicit geometric and Mahler-to-weight budgets.
4. The geometry and complete analytic transfers are now proved in the separate
   upstream-dependent ports. CP9 derives cofinal nonzero actual minors from
   explicit geometry. CP10 derives literal translation expansion, scalar bounds,
   holomorphic collision bounds, determinant summation, real-degree vanishing
   remainders and two-sided bounds for exactly the same actual minor.
5. Construct the same packet from an infinite fixed-field exceptional set:
   discharge the explicit inflated volumes, separated products, tail budget and
   strict changed total-error/collision margins in `no_geometric_packet`.
   That theorem currently proves a conditional packet contradiction and is
   explicitly not the final fixed-field pi finiteness theorem.

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
actual type/axiom prints, and seventeen separately checked expected failures. It
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
Checkpoint 4 did not yet prove log-polynomial clearing or its coefficient
envelope. Checkpoint 5 below closes these connections. A weighted-packet
nonzero minor and full interpolation/analytic transfer still remain open.

To kernel-check the exact pinned upstream entry bridge after the standalone
replay, use `scripts/audit_entry_bridge.py --verification-root <existing-upstream>
--checkpoint-verification <replay-output> --out <separate-output>`. It revalidates
both caches and compiles the bridge; the standalone CI does not contain this
cross-project fixture. See `audit/CHECKPOINT4.md` and `audit/entry-bridge-audit.json`.

## Actual log-minor arithmetic checkpoint

`LogClearing.lean` uses the actual `PowerSeries.log` truncations and the exact
`lcmUpto (T-1)` denominators. It proves each entry and the whole polynomial
minor clear to Gaussian coefficients, without an entry-membership premise.
`exists_gaussian_cleared_minor` constructs that Gaussian polynomial and proves
its degree caps are the exact coordinate rebates.

`L1Norm.lean` proves coefficient-l1 subadditivity and submultiplicativity and
the determinant factorial envelope. `TimeEnvelope.lean` uses absolute time
coefficients weighted by `(1/2)^s`, finite convolution, and the geometric sum.
This proves the same `2^s` coefficient control as a radius-1/2 Cauchy estimate
without constructing a new Banach polynomial space. The uniform truncated-log
bound is the explicit coarse constant 2, replacing the paper's sharper log 2;
the center constant is therefore `2k+2`. These constants do not depend on `T`
and introduce no log-log height remainder.

`formal_minor_fixed_field_arithmetic` combines the actual polynomial with the
proved degree-two norm theorem and the complete coefficient envelope. In its
actual type the product of target root factors is at most `Q^2` times the
factorial/row/column envelope, the Mahler product, and the target minor norm.
There is one coefficient cost and exactly two denominator costs. Its field
tower, primitive factorization and nonzero minor inputs remain explicit; it
is not the final pi theorem. See `audit/CHECKPOINT5.md` and the exact type audit.

The cross-project bridge now also proves exact actual selected-minor equality,
nonvanishing transport and the legal selected columns' joint weighted budget.
Its five declaration audits are separate from the 38/148 standalone replay.

## Normalized arithmetic and changed error closure

Checkpoint 6 checks 44 compiler invocations and 219 actual declaration
type/axiom reports. `ArithmeticErrors.lean` proves the actual minor log estimate
and its normalized bound. With `D=M*N`, it is

```text
log ||Delta|| / D >= -(1-rebate) - E_F - log(M!)/D
E_F = 2 Lambda F/v + log(2)/v + log(3/2)/w0
      + [2 Lambda + log(2(2k+2)) + log(sqrt(3))]/wmin
Lambda = log(4)+4
```

The stronger denominator estimate uses the same joint degree budget before
summing truncation costs: `log Q <= Lambda*(F*D/v + D/wmin)`. This legitimately
improves the paper's coarser coordinatewise `m/v` and reciprocal-sum costs; it
does not omit either copy of `log Q`. The coefficient bound is still the actual
constant `2k+2`, uniformly in every truncation degree.

`ErrorLimits.lean` proves the changed total error identity, dimension margin
selection for actual `floor(C^m)` data, and subsequent common-height margin.
It also proves `log(M!)/(M*N) -> 0` for positive polynomially growing `M(N)`.
The analytic expression in its error identity is the intended transfer cost;
its bound for generalized quadratic packets remains unproved. Hence this
error closure is not a substitute for the outstanding geometric/analytic port.

The dimension estimates are adapted, with attribution, from the pinned
upstream elementary dimension files. Their coefficient 100 is generalized
to a nonnegative constant and all adapted proofs are freshly kernel checked.

For the fixed-field geometric contact bridge, run
`scripts/audit_geometry_bridge.py` with the same `--verification-root`,
`--checkpoint-verification` and separate `--out` arguments used for
`scripts/audit_entry_bridge.py`. Its result is independent of the focused CI,
which does not provision the upstream OAI closure.

## Actual source-packet and row-scalar continuation

`checks/UpstreamPacketArithmetic.lean` instantiates the arithmetic in the actual
pinned upstream Row/Column packet. Legal membership proves the time, first-column
and transverse-degree budgets. Nonzero matching proves the joint degree rebate;
`actual_selected_minor_lower` then concludes the normalized bound for the actual
selected upstream matrix determinant. The rebate lies in [0,theta]. Its inputs
are the actual degree-two field/coordinates, positive packet scales, common
lower weight, displayed truncation upper bound, and an actual nonzero minor.
It assumes no norm integrality, coefficient envelope, weighted budgets or jet
surjectivity. Primitive-height row count and row/low-index ratio limits also
instantiate the purely combinatorial upstream counting theorems.

`checks/UpstreamAnalysisBridge.lean` transfers the actual primitive-height
approximation to the precise exponential center error and instantiates the
source row-scalar translation bound with actual ceiling truncation orders.
The exp(nu) rounding cost is retained; a separately matched expected failure
prohibits dropping it. This proves row scalars, not the complete determinant
analytic aggregate or fixed-field pi finiteness.

Replay these using `scripts/audit_packet_analysis.py` with the same three
arguments as the entry bridge. The script revalidates the fully replayed core,
all 872 prior upstream receipts and the exact entry/minor bridge, then freshly
compiles packet arithmetic, row scalars and the expected failure. Nine new
exact types/axiom reports are checked. These OAI-dependent bridges are separately
verified locally; the focused Linux CI provisions only the independent Mathlib
subproject and replays its 50 checks / 265 declarations.

Remaining implementation work is the general compactification/blowup/jet
surjectivity, exact translated determinant expansion and collision/holomorphic
summation, and assembling the actual count/remainder limits, parameter selection
and exceptional-set contradiction. No final pi theorem is exported.

## Geometry checkpoint (CP9)

`FixedQuadratic/GeometryPort` extracts the upstream geometry wrappers from the
rational-only admissible-data type. `FixedFieldGeometryData` contains explicit
positive rational weights, injective complex centers, inflated total/fibre
volumes, separated product inequalities and the coordinate ratio. It contains
no assumed curve bound, ampleness, jet surjectivity or nonzero minor. The actual
arbitrary-center curve theorem implies the curve inequality; the port then
constructs weighted projective compactification, the center ideal and blowup,
proves the uniform curve margin and ampleness, and obtains jet surjectivity.

`FixedFieldInterpolation.cofinal_nonzero_full_row_minor` derives arbitrarily
large auxiliary degrees with an injectively selected, nonzero full-row minor
of the literal truncated-log matrix. `fixed_field_cofinal_nonzero_minor`
instantiates its centers with `2*I*beta_i` and weights with the ceilings of the
logs of the actual primitive-minimal-polynomial heights. Explicit geometric
volume/separation/tail-budget inputs remain in that theorem's type. Selecting
and pricing a packet from the infinite exceptional set is still required; this
is not the final pi finiteness theorem.

`checks/GeometryAudit.lean` prints all new declaration types/axioms and the full
geometry record. `checks/GeometryRegression.lean` proves a numerically
consistent geometry packet, its jet surjectivity and its cofinal actual minor
existence. Its weight 100000 is a geometry regression, not an asserted
primitive height of sqrt(2). Negative fixtures reject a missing tail budget and
an attempted assumed-surjectivity record field. Run `scripts/audit_geometry_port.py`
with the exact upstream verification root and a passed core replay receipt.
This separate replay is not included in the 50-check arithmetic Linux CI.

## Complete analytic transfer (CP10)

`FixedQuadratic/AnalysisPort` contains actual fixed-field primitive-height data,
complete translation expansion and determinant summation, collision bounds,
vanishing analytic and factorial remainders for real auxiliary degrees, and
the collision-rate limit. It retains the exact ceiling `exp(nu)` approximation
cost and the joint row rebate. `actual_minor_two_sided` proves both bounds for
one common nonzero determinant using the actual degree-two field norm theorem.
`cofinal_nonzero_actual_minor` connects CP9 geometry to exactly this matrix.
`no_geometric_packet` obtains its minors from the proved geometric chain and
concludes False under explicitly displayed elementary geometric conditions and
strict total-error/collision margins. These margins are not claimed to follow
from every infinite exceptional set yet.

Separate ordinary Lean replay: six proof modules, aggregate, positive changed
budget regression, 61-type/axiom audit and two diagnostic failures = 11 checks.
All axioms are among `propext`, `Classical.choice`, `Quot.sound`. Source, logs,
compiler exits and olean hashes are in `audit/analysis-port-audit.json`; exact
types and the whole input record are in `audit/analysis-port-logs/checks.AnalysisAudit.log`.
Run `scripts/audit_analysis_port.py` with passed core, geometry and packet
receipts and the exact upstream verification root. This local replay is
separate from the unchanged 50-check arithmetic Linux CI.
