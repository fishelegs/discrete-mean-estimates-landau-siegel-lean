# Exact rational/Taylor enclosure method

All arithmetic in `certify.py` uses Python integers and `fractions.Fraction`. No binary or decimal floating arithmetic enters the certificate. Decimal inputs are parsed as exact rationals; decimal output endpoints are integer-rounded outward.

## Pi

The code uses the closed bracket

 314159265358979323846/10^20 <= pi <= 314159265358979323847/10^20.

The stronger strict bracket is supplied by mathlib `Real.pi_gt_d20` and `Real.pi_lt_d20` (pinned mathlib4.30.0). Shared occurrences of pi are enclosed by standard interval arithmetic; ignoring dependency only enlarges enclosures.

## Rectangular complex intervals

`R(a,b)` encloses real numbers in [a,b]. Addition, negation, multiplication, and division by a zero-excluding interval use exact rational endpoint arithmetic. `C(r,i)` is a rectangle. Complex multiplication uses its standard real/imaginary formulas, enclosing every correlated input. The upper bound `r.mag()+i.mag()` dominates the complex norm.

## Polynomial plus a uniform norm remainder

`M(p,e,H)` represents a polynomial with interval complex coefficients, plus a uniform complex norm error <=e on 0<=t<=H. Polynomial coefficients contain all possible pi-dependent true Taylor coefficients.

For any coefficient-enclosed polynomial p, `pnorm(p,H)=sum_k mag(p_k)H^k` bounds |p(t)| on the interval. The operations use:

- addition: errors e_p+e_q
- multiplication: error <= |p|_upper e_q + |q|_upper e_p + e_p e_q
- integral_0^L: polynomial integration plus norm error <=L e, for 0<=L<=H
- integral_t^H: primitive polynomial P(H)−P(t), plus norm error <=H e

Every error-radius enlargement adds ±e to each rectangular component, which contains the complex error disk. This is conservative and does not claim the whole rectangle has norm <=e.

## Exponentials

For z=i*pi*(a+b*t), a,b rational, and 0<=t<=H, put

 M=pi_upper*max(|a|,|a+bH|).

The absolute power series remainder after degree N is bounded by

 R_N = M^(N+1)/(N+1)! / (1−M/(N+2)), provided M<N+2.

Indeed every later absolute term ratio is <=M/(N+2); summing the resulting geometric series bounds the tail. The Section12 part uses N=14 and M<.032. The Section8 extension uses N=40 and M<4. In each case the same explicit rational tail formula is used, rather than an omitted asymptotic error. The argument does not require numerical evaluation of exponential, sine, cosine, or factorial.

`exp_affine` constructs the exact Taylor polynomial with interval pi coefficients and the above uniform rational error. Multiplication by polynomial prefactors, the variable-upper-limit integral in W2, products f*W2 and g*W1, and all fixed integrations then use the generic error rules.

## Scope and trusted components

The certificate is a computer-assisted exact-rational enclosure with a documented elementary analytic error proof. It is not fully kernel-checked: Python interpreter correctness, implementation of interval operations, source-formula transcription, the power-series tail argument, and integral error rules remain outside the Lean kernel. Separate Lean auxiliary checks concern only pi and conditional arithmetic, not these integral enclosures; they are not used to overstate this certificate as kernel-checked.

A full Lean integral certificate would still need to connect these model definitions to an interval integral, formalize Taylor/interval propagation, and then instantiate the arithmetic bounds. A separate true character-sum-to-model bridge is also needed regardless of numerical certificate technology.

## Section8 extension

The six f/g tables are entered independently and directly as exact rational coefficient tuples. For c1, the four integral constructions are f6(t)g6(t) on [0,.504], f7(t)g7(t) on [0,.5], f7(t)g6(t+.004) on [0,.5], and f6(t+.004)g7(t) on [0,.5], weighted by (1/2,2,3/2) and the source denominators. Exponentials use N=40. This extension does not depend on the exploratory mpmath code or the parent's separate closed-form evaluator. It introduces no source correction.
