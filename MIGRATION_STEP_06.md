# Migration Step 06 — close the real-axis endpoint at s = 1

## Goal

Upgrade the Step 05 theorem

`x > 1 -> Im L(x, χ) = 0`

to the endpoint needed by the paper:

`Im L(1, χ) = 0`

for a real primitive character with modulus `D > 1`.

## Mathematical argument

1. `D > 1` and primitivity imply that `χ` is nontrivial.
2. mathlib's `DirichletCharacter.differentiable_LFunction` therefore makes
   `L(s, χ)` differentiable, hence continuous, on all of `ℂ`.
3. Restriction to the real axis is continuous.
4. Its imaginary part is a continuous real-valued function.
5. By Step 05 this imaginary part vanishes on the open ray `(1, ∞)`.
6. The zero set of a continuous function is closed.
7. Since `1` lies in the closure of `(1, ∞)`, the imaginary part also vanishes
   at `1`.

This avoids prematurely proving a full Schwarz-reflection identity.

## Added Lean interface

`ZhangLS/Spec/RealAxisAtOne.lean` adds:

- `dirichletLFunction_im_eq_zero_at_one`
- `LAtOne_im_eq_zero`
- `LAtOne_eq_realLAtOne`
- `real_value_at_one_milestone`

## Remaining analytic bridge

The next target is derivative compatibility:

`Im L'(1, χ) = 0`

and

`deriv (x ↦ Re L(x, χ)) 1 = Re (deriv L 1)`.

A robust route is to use differentiability of the complex L-function plus the
real-axis restriction and the chain rule.  Once this bridge is proved, Lemma
5.7 can be stated entirely in the real interface without hidden coercions.

## Verification status

The current execution container still has no Lean toolchain and no outbound
network path from the shell, so this step has not been kernel-compiled here.
The proof uses standard mathlib topology/calculus APIs (`Differentiable.continuous`,
`Complex.continuous_ofReal`, `Complex.continuous_im`, `isClosed_eq`,
`closure_minimal`) and is intentionally small so that the first networked CI
run can isolate API spelling/version issues quickly.
