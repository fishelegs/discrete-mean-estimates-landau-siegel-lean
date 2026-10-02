# Migration Step 16 — finite smoothed main sum

Step 16 introduces the finite initial segment of the arithmetic sum appearing in
Zhang's Lemma 5.7:

\[
  \sum_{1\le n\le D} \frac{\nu_\chi(n)}{n}\,g_D(D^4/n).
\]

The new module `ZhangLS/Spec/Lemma57SmoothedSum.lean` defines the individual
smoothed term and this initial sum.  Since every divisor of `D` lies in `[1,D]`, the
initial segment contains the entire divisor subsum treated in Steps 09--15.

For every `n` in `[1,D]`, the argument `D^4/n` is at least `1`, so the explicit
Gaussian estimate from Step 15 gives `g_D(D^4/n) >= 1/2` throughout the initial
segment.

The remaining arithmetic sign assertion is exposed as
`DivisorCharacterSumNonnegative χ`, namely

\[
  \forall n,\quad 0 \le \nu_\chi(n).
\]

This is a genuine lower-level property of the convolution coefficient `ν = 1 * χ`;
it is not equivalent to the Lemma 5.7 main-sum lower bound.  Under this property the
new theorem `lemma57DivisorSubsum_le_initialSmoothedSum` proves that the initial sum
dominates the divisor contribution.

Combining it with the Step-15 `1/8` divisor estimate yields
`lemma57_initial_gaussian_arithmetic_scale`:

\[
  \frac18\frac D{\varphi(D)}
  \le \sum_{1\le n\le D}\frac{\nu_\chi(n)}n g_D(D^4/n).
\]

Finally `lemma57InitialArithmeticLowerBound` packages this finite sum as a
`Lemma57ArithmeticLowerBound` with constant `1/8`.

The next arithmetic task is to prove `DivisorCharacterSumNonnegative` from the real
quadratic character structure, via prime-power local factors and multiplicativity.
After that, the finite arithmetic side is unconditional and the remaining work is
the infinite-sum/Mellin and contour approximation layer.

No Lean executable is available in the current container, so these additions are
source-level only and are not claimed to be kernel-verified.
