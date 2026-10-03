# Fixed logarithmic support windows

2026-10-03. Addendum to the frozen [dyadic report](DYADIC_REPORT.md) (accepted source hash before path normalization), SHA256 `1839df7636ee4adcdacae99228c5ecf4b089556815fcc6c17d5b0888e3a91ea2`. The original report and its checks are unchanged. No repository edits or Lean execution.

## Result

The C1 and T1 completion theorems extend to the following fixed logarithmic-width box, with the same errors:

    A support: [P^.502, P^.504]
    B support: [P^.499, P^.500]
    J support: [P^.500, P^.504]

The coefficient sequences are uniformly bounded and common to all p,psi, exactly as in the frozen report. C1 uses kappa cutoffs P^.9995 on the right and P^1.005 on the left. T1 uses P^1.005 on both sides. The C1 right completion costs O_C(M L^-200); its left costs O_C(M L^-14). Each side of T1 costs O_C(M L^-14). After the original normalization aM, both completed representations have uniform error O_C(a^-1 L^-14)=o(L^-8).

There is no extra power of L from the enlarged intervals. The proof works with whole-interval endpoint bounds; it does not partition into O(log P) dyadic blocks. The exact arithmetic kernels and every parity, conductor, branch, and character restriction remain those in Sections 7 and 8 of the frozen report.

These statements still do not evaluate a Gram entry, establish a signed gain, or justify normalizing a small residual. They improve the legal candidate class without making a variational claim.

## 1. Precise class and unchanged source hypotheses

Fix a finite number of coefficient sequences and a constant C independent of D. Let

    Aminus=P^.502, Aplus=P^.504,
    Bminus=P^.499, Bplus=P^.500,
    Jminus=P^.500, Jplus=P^.504.

Assume |a(m)|,|b(n)|,|j(n)|<=C and the respective supports lie in the three intervals above. Dependence on D, chi, and the prescribed source shifts is allowed; dependence on p or psi is not. The original J1 is included exactly, with coefficient bound 1. Every A belongs to the allowed J class, so T1[A_i,A_j] and T1[A,A] are included.

All the source assumptions, the range of primitive real chi, both parities, the good family, the original zeros and weights, beta3=beta1+beta2, and the inherited gamma branch are unchanged. The exceptional-zero assumption remains L(1,chi)<L^-2022. No change to the requested final exponent 2024 is made.

The support ceilings stay at P^.504, so they are below PT^-2 for sufficiently large D. Cube lengths are

    length(A^3) <= P^1.512,
    length(B^3) <= P^1.500,
    length(J^3) <= P^1.512,

all strictly below P^2. Constants depend on the fixed coefficient bounds and finite trial count, not on the individual coefficients or D. Thresholds may also depend on the fixed source gap constant c'.

This is a changed class with fixed widths .002, .001, and .004 in u=log n/log P. For example a fixed bounded profile f on [.502,.504], sampled as a(n)=chi(n)f(log n/log P), has a uniform coefficient bound. Smoothness is not needed for completion. A later arithmetic evaluation may impose additional profile regularity, but this addendum does not presume such an evaluation.

## 2. Uniform endpoint bounds replace dyadic counting

The only support-sensitive part that needs a new argument is the tail estimate. For X>=2 and sigma>=3/2,

    sum_{n>=X} n^-sigma
      <= X^-sigma + X^(1-sigma)/(sigma-1)
      <= 3 X^(1-sigma).                                    (2.1)

One obtains the first inequality by starting at ceil(X) and comparing the remaining decreasing series with its integral. It is uniform for all sigma>=3/2, in particular up to sigma=1/2+L^9. Consequently

    |A(s)| <= 3C Aminus^(1-sigma),
    |B(s)| <= 3C Bminus^(1-sigma)                            (sigma>=3/2).

For sigma<=-1/2, counting all integers below the upper endpoint gives

    sum_{n<=X} n^-sigma <= X^(1-sigma),                      (2.2)

and therefore

    |A(s)| <= C Aplus^(1-sigma),
    |B(s)| <= C Bplus^(1-sigma)                             (sigma<=-1/2).

For the dual J factor, the two corresponding bounds are

    |Jbar(1-s,bar(psi))| <= C Jplus^sigma                   (sigma>=3/2),
    |Jbar(1-s,bar(psi))| <= 3C Jminus^sigma                 (sigma<=-1/2).

The second follows from (2.1) with exponent 1-sigma. These estimates never introduce the ratio of an upper endpoint to a lower endpoint. A bound obtained by multiplying the upper-endpoint count by the lower-endpoint term would needlessly lose powers of P; that bound is not used here.

## 3. C1 tail contours

Retain the finite source window, S=L^9, and exact gamma estimates of frozen Section 4. Put

    Q(t)=Dp^2(t/(2pi))^2,
    kappaRight=P^.9995,
    kappaLeft=P^1.005.

### Right tail

On sigma>=3/2, using (2.1), the tail of the exact C1 right integrand is bounded, before omega, by

    O_C((log kappaRight)^3 Q(t)^(1/2)
       [Q(t)/(kappaRight*Aminus*Bminus)]^(sigma-1)).         (3.1)

The power calculation is

    .9995 + .502 + .499 - 2 = .0005.

Thus, uniformly over the original p and t windows,

    Q(t)/(kappaRight*Aminus*Bminus)
      <= D t0^2 P^-.0005 (1+o(1)) <= P^-.00025             (3.2)

for sufficiently large D. This follows from log(D t0^2)=L+1038 log L=o(L^9). Move the tail from sigma=3/2 to sigma=1/2+S. The far vertical side is exp(-cL^18), and the two horizontal sides are exp(-cL^10), because the bound in (3.1) decreases as sigma increases. The exact gamma branch and its bounded multiplier are unchanged.

### Left tail

On sigma<=-1/2, using (2.2) and the exact conductor scalar |tau(chi)D^(s-1)|=D^(sigma-1/2), the tail is bounded by

    O_C(Aplus*Bplus*D^-1/2 (log kappaLeft)^3
       [D*kappaLeft/(Aplus*Bplus)]^sigma).                 (3.3)

Here

    1.005 - .504 - .500 = .001,

so the bracket is D P^.001, in particular at least P^.0005. Move the tail to sigma=1/2-S. The same exponential bounds result. No factor such as P^.002, P^.004, or log P is needed to compensate for the broader support interval.

These are contour bounds for the oscillatory Mellin integrals themselves. They do not infer truncation from stationary points. In particular the right and left cutoffs remain distinct and the D,p,t0 factors have been paid inside the inequalities.

## 4. T1 tail contours

Set targetCutoff=P^1.005 and q1(t)=pt/(2pi). The exact right and left integrands are still frozen (8.1) and (8.2), including epsilon_{chi psi} on the right and r_psi epsilon_psi on the left.

On sigma>=3/2, the right tail is bounded by

    O_C(targetCutoff*Aminus*q1(t)^-1/2 (log targetCutoff)^3
       [q1(t)*Jplus/(targetCutoff*Aminus)]^sigma).          (4.1)

Its unsimplified power gap is

    1.005 + .502 - 1 - .504 = .003.

Since t0=P^o(1), the bracket is at most P^-.002 for sufficiently large D. On sigma<=-1/2, the left tail is bounded by

    O_C(Aplus*q1(t)^1/2 (log targetCutoff)^3
       [targetCutoff*Jminus/(Aplus*q1(t))]^sigma).          (4.2)

Its unsimplified power gap is

    1.005 + .500 - .504 - 1 = .001.

The bracket is at least P^.0005 for sufficiently large D, after paying the pt0 factor. The same outward shifts give exponentially negligible tails and horizontal pieces. Thus both T1 sides have honest slack beyond their largest natural lengths P^1.002 t0 and P^1.004 t0.

## 5. Moments, family completion, and exact representations

The frozen small-shift Euler arguments apply uniformly on the unchanged fixed exponent range X<=P^2. In particular

    sum_{n<=X}|kappa(n)|^2/n << (log(2X))^4,
    sum_{n<=X}(|kappa|*|kappa|)(n)^2/n << (log(2X))^16.

The positive convolution majorant, not the full complex convolution, still controls the square of a truncated kappa polynomial. Now

    kappaRight^2 = P^1.999 < P^2,

so C1's right fourth moment remains O(P^2 L^144). Each left/target cutoff has length P^1.005<P^2, so its second moment remains O(P^2 L^36). The sixth moments of A,B,J remain O_C(P^2 L^81) by the cube-length bounds in Section 1. Their lower endpoints do not enter these moment bounds.

The exact Holder calculations therefore remain

    C1 right: 144/4 + 81/6 + 81/6 - 739*5/12 + 77*7/12 = -200,
    left and targets: 36/2 + 81/6 + 81/6 - 739/6 + 77*5/6 = -14.

No factor counting subintervals occurs, because the full windows are handled at once. No hidden norm of a varying profile occurs, because all polynomial estimates use the same fixed coefficient bound C.

All finite-polynomial inward contour moves, exact unit-modulus critical-line factors, good-family residue deformation, good-family reciprocal-L horizontal bounds exp(O(L^9 log L)), and pole exclusions are identical to frozen Sections 5–6. The broadened upper endpoints stay within P^.504, so their horizontal polynomial envelopes are still exp(O(L^9)). Bad characters' full reciprocal L-functions are never moved through their zeros.

Accordingly, with R_C,L_C and R_T,L_T defined by the exact finite-window arithmetic kernels in frozen Sections 7–8, but with the present coefficient class, the completed theorems are

    C1[A,B] = (R_C(A,B)-L_C(A,B))/(aM) + O_C(a^-1 L^-14),
    T1[A,J] = (R_T(A,J)-L_T(A,J))/(aM) + O_C(a^-1 L^-14).

These retain every p not dividing ell*m*n restriction, both parity corrections, chi(p), tau(chi), the exact B_beta branch, and the three-Gauss left target kernel. Their absolute convergence on the two safe finite lines is unchanged. The cutoff values are proof devices and do not alter the infinite absolutely convergent sums in those representations.

For the old target C0[J1,B], the same second-moment attachment works with cutoff P^1.005 on both sides: its product support lies between P^.999 and P^1.004, giving right gap .004 and left gap .001. This is only a completion observation, not its arithmetic evaluation.

## 6. What widening does and does not establish

Unlike a dyadic [U,2U] interval, whose width in log n/log P is log(2)/log P, the present coefficient box has fixed positive logarithmic widths. It therefore allows fixed bounded profiles without forcing their profile domains to shrink with D. The completion error remains uniform for a fixed finite collection of such profiles.

This does not itself bound their actual weighted zero energies by constants or prove that a residual has a nonvanishing normalized norm. A bounded coefficient profile can still have an ordinary harmonic coefficient sum of order log P; that growth is already permitted by the moment estimates. Establishing actual energies and the smallest relevant Gram eigenvalue requires the main-term calculations. No profile or residual is rescaled by a growing factor in this addendum.

The complete three-direction Gram/target algebra from frozen Section 9 applies, now on this wider box. The lower-support pieces of the original broad H1/H2 remain outside the stated class. The next stopping condition is unchanged: evaluate all required old and new entries with joint errors adequate for the proposed normalization, then assess the signed margin. No gain is claimed beforehand.

## Reproducible checks

[the author fixed-window check](../scripts/check_fixed_log_author.py) uses exact rational arithmetic for all support widths, gaps, length inequalities, and Holder budgets. It also checks the normalized endpoint inequalities on finite integer windows. Output is saved in [the author fixed-window results](../results/FIXED_LOG_AUTHOR_ORIGINAL.txt). The frozen report and its previous check files are not modified. These regressions supplement, and do not replace, the uniform proof above.
