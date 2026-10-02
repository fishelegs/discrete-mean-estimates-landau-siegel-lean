# Step 35 — Full Mellin identity

Step 35 discharges `Lemma57MellinIdentity`, the full-series obligation left
after the scalar Gaussian transform in Step 34.  The trusted implementation is
`ZhangLS/Spec/Lemma57MellinIdentity.lean`.

## Proved in Lean

On the vertical line `s = 1 + it`, the shifted Dirichlet series is evaluated at
real part `2`.  The proof:

1. identifies `ζ(1+s)L(1+s,χ)` with the L-series of
   `divisorCharacterSum χ`;
2. imports absolute convergence at real part `2` from mathlib's
   `DirichletCharacter.LSeriesSummable_zetaMul` theorem;
3. expresses the norm of every coefficientwise integrand as its L-series
   coefficient norm times one common integrable Gaussian kernel;
4. proves summability of the coefficientwise norm integrals;
5. applies `integral_tsum_of_summable_integral_norm` to justify the exact
   series/integral interchange;
6. evaluates every normalized coefficient integral using the scalar inverse
   Mellin formula from Step 34;
7. identifies the resulting complex series with the coercion of Zhang's real
   full smoothed sum.

Consequently `lemma57MellinIdentity_proved` supplies both honest vertical
integrability and the exact integral identity for every `D > 1`.

## Remaining analytic work

The right-line Mellin identity is complete.  The remaining Lemma 5.7 work is
the contour shift from `Re(s)=1` to `Re(s)=-1/2` and the explicit bound for the
shifted integral plus the `L(1,χ)` residue correction under Assumption (A).

## Verification

The authoritative command `tools/verify_all_lean.sh` passed on 2026-09-13:

- all 23 trusted Spec modules passed individual kernel checks;
- the trusted Spec aggregate passed;
- the full project build passed with 3534 jobs;
- all 7 audit regression modules passed;
- the placeholder and declaration-structure gates passed across 111 Lean files.

The machine-readable record `audit/lean_kernel_verification.txt` contains
`LEAN_KERNEL_VERIFICATION=PASS`.
