# Corrected Lemma 16.2: bounded quantitative center component

## Proved scope of this candidate

Seven new modules extend the independently accepted immutable actual analytic stage two. They do not replace its arithmetic objects. The correction is still

V(s) = RawEulerProduct(s) / M2star(1-beta_j),

and the actual convergent Dirichlet series still has the identity

F(s) = V(s) zeta(s)^2 zeta(s-beta_j) L(s,chi) L(s-beta_j,chi)^2.

The central theorem is `lemma162_corrected_quantitative_proved`. Its constants are defined before the fixed positive c′, and its one eventual threshold is chosen before D, the real primitive character chi, j, and s. The two original shifts are `lemma52PaperBetaOne D c` and `lemma52PaperBetaTwo D c`, indexed by `Fin 2` values 0 and 1. `lemma162_corrected_quantitative_shared_constant` accepts exactly the compatible c′ supplied by Lemma 5.2. No assumption(A) or construction of an(A)-character occurs.

## Exact center simplification, retaining finite shifts

For every unramified prime q, with a=q^(-beta_1), b=q^(beta_j), u=1/q, the actual four rational local factors satisfy

RawPrimeCorrection(q,1) = 1 - a*b*u^2.

This is proved for both chi(q)=+1 and -1, at the genuine finite-D shifts, by exact rational algebra and actual-local-data identification. It includes q=2. At ramified primes the exact factor is (1-1/q)^2 and is independent of the shifts. No F00,2 division occurs. In particular the actual raw numerator for j=1 is exactly its zero-shift numerator for every D. This is not a limit statement.

The zero-shift numerator is evaluated only after this exact identification:

R0 = (6/pi^2) * (phi(D)/D) * product_(q|D) q/(q+1).

A direct finite-shift comparison gives |R-R0| <= C_R (|beta_1|+|beta_j|), using the summable local bound 10(|beta_1|+|beta_j|) q^(-9/5). Ramified factors cancel in this comparison. The original Lemma 16.1 gives both the comparison M2star(1-beta_j) = mathfrak_p + O(alpha) and a positive absolute lower bound for that denominator. Its exact published two-branch mathfrak_p is `lemma161MainTerm chi`; chi(2)=1 uses twice the product over q>2.

Consequently, for both original shifts,

|V(1) - (6/pi^2) phi(D)/(D*mathfrak_p) product_(q|D) q/(q+1)|
  <= C_center * alpha
  = (C_center*pi)/(log D)^9.

The constants are explicit in `Lemma162CorrectedCenter.lean`, positive and independent of D, chi, j, and c′. The original printed O((log D)^(-4)) rate is therefore available for the CORRECTED V, with an explicit same-constant inequality in `lemma162_paper_corrected_center_four`. It has not been assigned to the old quotient.

## Bounds adequate for subsequent Cauchy work

The actual unramified product has an absolute majorant. The finite ramified product obeys two different useful bounds:

1. In Re(s)>=9/10 and Re(s)>=1-1/log D, the complete V is bounded by C_strip (1+log log D)^18. The loglog power is explicit.
2. In Re(s)>=9/10 and |Im(s)| log D<=1, each ramified factor has norm at most 1; hence |V(s)|<=C_sector absolutely.

For sufficiently large D, the closed disk |s-1|<=1/(10 log D) lies strictly inside the analytic half-plane and the latter sector. Cauchy's estimate now proves, for every natural n,

|V^(n)(1)| <= n! * C_sector * (10 log D)^n.

Both the factorial and logarithmic factors are visible. This is an actual D-uniform bound on an explicit shrinking neighborhood, not the previously D-dependent RawDBound(D) estimate.

## Original/repaired status and remaining work

This package completes the bounded thin-strip/center/Cauchy component for the actual corrected V. It does not prove the original literal Lemma 16.2: the literal F/(zeta^3 L^3) quotient still has continuous center 0, as proved by unchanged stage two. This package does not claim that a zero center alone refutes the printed O(L^-4) assertion or the final main theorem.

Still unproved here: the corrected Mellin inversion and smoothing errors, the two-pole contour shift, exact residue calculations for the actual Section 16 integrand, the cancellation/error budget for coalescing poles, the finite-cutoff comparison, and the final per-prime o(p) or summed-prime error estimates. `NEXT_MELLIN.md` formulates the required terms without assigning them Lean proof credit.

