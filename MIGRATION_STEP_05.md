# Migration Step 05 — reality in the absolutely-convergent half-plane

## Implemented

This step adds the first nontrivial analytic proof to the trusted `Spec` layer.
For a real primitive character `χ` and a real parameter `x > 1`:

1. each `LSeries.term` has zero imaginary part;
2. absolute convergence allows `Complex.im` to pass through the topological sum;
3. hence `dirichletLSeries χ x` is real;
4. mathlib's `LFunction_eq_LSeries` bridge then shows the analytically continued
   `dirichletLFunction χ x` is real in the same half-plane.

The proof uses mathlib's exact real/complex power bridge `Complex.ofReal_cpow`
and `Complex.im_tsum`; it does not introduce an analytic hypothesis.

## Deliberately not claimed yet

This step does **not** prove reality at `x = 1`, nor reality on the entire real
axis.  The next step must transport the half-plane result through analytic
continuation.  Two viable routes are:

* a Schwarz-reflection/conjugation identity followed by the identity theorem; or
* for the value at `1` specifically, continuity of the nontrivial L-function at
  `1` plus a real sequence `x_n > 1` tending to `1`.

The second route is smaller and should be attempted first because Theorem 1 only
needs `L(1, χ)`; the full reflection identity can be proved later for derivative
compatibility.

## Verification status

The current execution container still has no Lean binary and no outbound network,
so this code has not yet been kernel-compiled here.  The source was written against
mathlib APIs checked in the upstream repository, but the first networked CI run
remains authoritative.
