# Independent semantic review: actual Λ replacement

The bridge proves replacement of the existing literal `lemma83Lambda` by
`(φ(n)/n)²`, then propagates that replacement through the stated finite sum with
actual character norms, totients, a bounded complex profile, and the actual
`LDerivAtOne χ` scalar. It assumes no instance of the desired approximation.
The final weighted theorem does not require assumption (A), so it applies in
particular when the original (A) holds. This does not prove the arithmetic main
term, the complex Abel step, or the final `m_H` asymptotic.

## Literal local factor and normalization

`lemma83LambdaFactor β p s` is the existing product of all three factors
`1-p^(-s-β_i)`, divided by `1-p^(-s)`. Equivalently it is the reciprocal of the
actual three-shift κ rational function. `lemma83Lambda` is the product over every
prime divisor; none is filtered out. At `s=1-β_j`, the imported finite-shift lemma
proves additive error at most `32 b log(p)/p` for purely imaginary shifts with
`||β_i||≤b`. It bounds the unshifted denominator below by `1/2` using `p≥2` and
`||p^(-(1-β_j))||=1/p`; the three shifted factors are retained. It does not assume
nonvanishing of a potentially vanishing numerator to cancel it.

The new proof derives `1-1/p≥1/2>0` and `(1-1/p)²≥1/4`, including equality in the
second inequality at `p=2`. Dividing the additive error by this positive baseline
gives the normalized error `128 b log(p)/p`. The exact totient Euler product is
used to identify the normalized full product; no approximate arithmetic identity
is substituted. Baseline nonvanishing is derived from primality and `n>0`.

## Prime sum and product bound

The imported prime-log bound splits at the real cutoff `B>1`. For `p≤B`, it bounds
`log p` by `log B` and the reciprocal sum by the harmonic sum through `floor B`,
yielding `log B(1+log B)`. For `p>B`, it replaces `1/p` by `1/B` and uses the product
of distinct prime divisors to bound the sum of their logarithms by `log n`.
Thus the large-prime part is at most `log n/B≤1`; the total is at most
`(1+log B)²`. This argument includes `n=1` and small positive integers directly.

The Mathlib finite-product inequality
`||∏(1+u_p)-1||≤exp(∑||u_p||)-1` applies to the normalized factors minus one. This
is a finite norm inequality and requires no Euler-product convergence or assumed
relative approximation. It gives exponent `128 b(1+log B)²`.

For the actual shifts, `b=3α`, `α=π/B`, and `B=log P=L⁹`. The proved paper-shift
bounds apply beyond a threshold depending on the fixed `c>0`. The polynomial
condition `(384π)(1+9 log L)²≤L` and `L≤L⁹` ensure the exponent `E≤1`.
Then `exp E-1≤e E`, giving the explicit witness `C=384π exp(1)`.

## Uniformity and endpoints

`paper_relative_error_uniform` chooses the constant and then `D₀` before `D,j,n`;
the proof uses the same explicit constant for every fixed `c>0`. Its displayed
existential is inside the argument `c`; universality of this particular witness
is visible in the proof and in `paper_relative_error`'s explicit bound. The
threshold combines only eventual conditions in `D`, never a condition chosen
after `n` or `j`. The range is every `n>0` satisfying the inclusive bound
`log n≤(201/400)log P`, uniformly for `j : Fin 3`.

At `n=1`, the prime product is empty and the normalized error is exactly zero.
At `p=2`, the denominator baseline is exactly `1/4`; the regression states the
normalized factor is four times the original factor. All three indices are
retained. `n=0` is intentionally excluded. The nondividing absolute form follows
by multiplying by the exact positive real baseline, not by adding a new
nonvanishing hypothesis.

## Actual weighted outer sum

`outerSum` uses the literal scalar `(LDerivAtOne χ)²/B²`, actual `||χ.evalNat n||`,
actual `Λ`, denominator `φ(n)`, and `K(log n/B)`. Its baseline uses exactly
`||χ.evalNat n|| φ(n)/n²`. Both sums run over
`1≤n≤floor(exp((201/400)B))`. The kernel is any complex-valued function supported
on the closed interval `[251/500,201/400]` with norm at most the fixed `M≥0` there;
no differentiability or real-valuedness is required. Support extends the bound
to all real arguments. Both closed endpoints are included.

The weighted local error is derived by division by the proved positive totient,
using `(φ/n)²/φ=φ/n²` and `φ(n)≤n`. It is at most `e/n`, including `n=1`.
`χ.evalNat_norm_le_one` is a proved property of the actual real primitive
character. The cutoff implies the needed logarithmic window, and its harmonic
mass is at most `1+(201/400)B≤2B` for `B≥1`. The finite sum therefore has error at
most `M e(2B)`.

The scalar bound uses the genuine analytic derivative theorem at `s=1`, obtained
from Cauchy's derivative estimate for the actual Dirichlet L-function:
`||L'(1,χ)||≤16 exp(1)L²`. Squaring and dividing by positive `B²` gives
`(16 exp(1))²L⁴/B²`. Combining this with
`e=Cerr(1+log B)²/B` yields final error
`C L⁴(1+log B)²/B²`. The chosen witness is
`2(16 exp(1))² Cerr(M+1)`, positive even for `M=0`.

`outer_error_uniform` quantifies `C,D₀` before `D,χ,j,K`, so it is uniform across
all characters and all kernels with the fixed norm bound. There is no assumed
norm envelope for an unknown arithmetic main term. The theorem controls only
the Λ-to-totient replacement; obtaining the baseline asymptotic remains a
separate obligation.
