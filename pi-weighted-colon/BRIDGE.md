# Actual endpoint ideals to quadratic remainders

This milestone proves the local divisibility bridge from the existing, explicit
ideals `endpointJ ε * endpointK ε ^ N` for both endpoints and all natural N.
The new final theorem has no local divisibility hypotheses. It still takes an
explicit decomposition and the two univariate degree bounds as inputs.

## Exact final statement

In `src/RightRemainderBridge.lean`, namespace `PiWeightedColon`:

```lean
theorem dataIntersection_remainder_zero (N : ℕ) (f h : Plane) (A B : Line)
    (hf : f ∈ dataIntersection N)
    (he : f = globalQ * h + linearRemainder A B)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1) :
    A = 0 ∧ B = 0

theorem dataIntersection_factor_Q (N : ℕ) (f h : Plane) (A B : Line)
    (hf : f ∈ dataIntersection N)
    (he : f = globalQ * h + linearRemainder A B)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1) :
    f = globalQ * h
```

Here `linearRemainder A B` is the actual plane polynomial A(t)+y B(t), using
`lineEmbedding` to embed the univariate t polynomials into `Plane`.
The quantified polynomials, ideal membership, decomposition and degree bounds
are explicit proof inputs. No assumption identifies the ideals with a guessed
condition on A or B.

## Quadratic model and coordinate identities

`QuadraticRemainder.lean` defines W=t²(t+1)² and
`Quad = AdjoinRoot (Y²-C W)` over `Line = F₂[t]`.
Every element has a proved canonical, unique representation `quadMk A B`, with
coefficient projections `quadA`, `quadB`. Multiplication is proved to be

```text
(A+B y)(D+E y) = (AD+WBE) + (AE+BD)y.
```

The ring homomorphism `reduction : Plane →+* Quad` sends the actual t and y
to these coordinates. The proof checks `reduction globalQ = 0`, so a supplied
plane decomposition yields `reduction f = quadMk A B`. We use this explicit
map, without assuming a kernel description or a ring isomorphism for Plane/(Q).
The identities are checked against the actual endpoint generators:

```text
reduction(z)       = t+y
reduction(z−1)     = u+y,             u=t+1
reduction(z²)      = t⁴
reduction((z−1)²)  = u⁴
reduction(y³)      = W y.
```

The monic quadratic construction and coefficient projections are fully proved;
`remainder_coordinates_unique` additionally checks that the projections
separate any two proposed linear remainders.

## Ideal images supply the local conditions

`EndpointRemainderBridge.lean` constructs the actual ideal of Quad defined by
`t^(N+1) | quadA q` and `t^N | quadB q`. It proves closure under arbitrary
multiplication, inclusion of the image of J₀, and a step for each generator of
K₀. Induction proves the image inclusion for J₀ K₀^N. Thus
`endpoint_zero_remainder_divisibility` derives

```text
t^(N+1) | A,    t^N | B.
```

`RightRemainderBridge.lean` constructs two ideals at an independent order m:

```text
E_m: u^m | A,B;       u^(m+3) | A+uB
O_m: u^(m+1) | A;     u^m | B;     u^(m+3) | A+t²uB.
```

Ideal closure uses the exact coupled multiplication identity with correction
W+v², where v=u or t²u. These corrections are u⁴ and t²u⁴, respectively.
The image of J₁ lies in E₀. Multiplication by each image generator of K₁,
u⁴ or Wy, maps E_m into O_(m+3) and O_m into E_(m+3). These are proved
inclusions of actual ideals. Induction on N, including N=0, gives E_(3N)
when N is even and O_(3N) when N is odd. Therefore
`endpoint_one_remainder_divisibility` derives precisely all u-power and
coupled conditions used by `remainder_by_parity`.

Combining the two endpoint memberships with the earlier remainder theorem
proves the displayed vanishing and explicit Q factorization.

## Verification and remaining scope

The combined replay checks 155 declarations in seven proof modules and three
regression modules. It compiles all 13 positive modules (including three audits)
and checks five intentional compiler failures. The new regressions cover
unique remainder coordinates, the concrete t⁴ endpoint-square identity,
actual J₁ K₁ and J₁ K₁² generator products, and the scale-zero intersection.
The new negative check rejects replacing t⁴ by t²; its corresponding positive
regression proves that replacement false. Every previous proof, regression,
and audit source is preserved byte-for-byte and remains in the replay.

Every declaration has a printed type or definition and an exact axiom report.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. No proof source
uses `sorry`, `admit`, `native_decide`, a custom axiom or unsafe declaration.
The compiler treats warnings as errors. Receipt, source hashes and full logs
are in `verification/`; binary outputs stay outside the repository.

Use the command in `README.md`, with `--out /tmp/pi-bridge-replay` on MC6.
The dedicated `.github/workflows/pi-algebraic.yml` job runs the same expanded
script and uploads its receipt and all logs. The Lean 4.30.0 and mathlib pins,
existing root workflow and old π checkpoints remain unchanged.

This is a proved ideal-to-remainder bridge, not the full V_N∩I_N={0} theorem.
Still required are monic division respecting the staircase, the remainder
and quotient degree/support bounds, and the final induction. The matrix
invertibility equivalence, determinant parity and residual-polynomial bridge
are also unformalized. No archimedean bound or π badly-approximability theorem
has been proved. The older Lean 4.34.1 regression suite was not rerun.
