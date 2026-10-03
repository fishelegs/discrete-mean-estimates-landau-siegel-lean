# Independent review of finite algebra and normalization

2026-10-03. Target: `weighted-phase-correlation-evaluation/REPORT.md`, primarily §§3,5,8. This is an independent mathematical source review. Analytic contour movement, tail localization, Poisson derivative bounds, and literature applicability are outside this subreview.

## Verdict

The finite identities (3.1), the functional-equation conversion in §3, (5.1)–(5.4), and (8.1)–(8.2) are correct, with both parities and every Fourier zero mode. The transformed eta argument has q in the numerator. The stated uncompleted, once-completed, and twice-completed absolute volume costs have the correct fixed P powers: respectively `P^(1+theta)`, `P^(.5+theta)`, and `P^theta` at the reference block. No finite-algebra correction is needed.

One notation clarification would help: the definition of B must read `B=Z(s)·(∏_j Y(s+beta_j))/Y(s)`, with exactly one denominator Y(s). Reading the unparenthesized expression as a product of three separate ratios would give a different quantity. The subsequent formulas in the report unambiguously use the correct single-denominator definition.

These findings do not verify a sign gap, a bad-family estimate, or the analytic localization and smoothing hypotheses needed to exploit the finite transform.

## 1. Exact branch algebra

Write `Z=epsilon h` and suppose `Y^2=Z^(-1)` on the connected high domain. Set

    R_Y(s) = [Y(s+beta_1)Y(s+beta_2)Y(s+beta_3)]/Y(s),
    B(s) = Z(s) R_Y(s).

Then, without selecting a new square root,

    B(s)^2 = Z(s)^3 / ∏_j Z(s+beta_j),
    B(s)^(-2) = [∏_j h(s+beta_j)]/h(s)^3.

A global sign change of Y leaves R_Y unchanged because the numerator has degree three and the denominator degree one. For two characters of the same p and parity, the quotient of their branches is a constant c with `c^2=epsilon_other/epsilon_this`. The product ratio changes by c² and the leading Z changes by the reciprocal factor. Thus B itself, including its sign, is common to that family. This is stronger than merely showing that B² is common.

With `m=YL` and `K=∏L(s+beta_j)/L(s)`, the source definition is

    Ctilde = -i R_Y K = -i B Z^(-1) K.

At a simple L-zero rho, `(YL)'(rho)=Y(rho)L'(rho)`, so its residue is exactly the actual c* quotient. The source definitions agree: `Lemma81KernelReplacement.lean` defines Ctilde with a single denominator, and `Lemma23.lean` gives the derivative normalization.

Applying the four functional equations in K gives

    K = [∏_j Z(s+beta_j)/Z(s)] Kd
      = Z(s)^2 B(s)^(-2) Kd.

Multiplying Ctilde by `Phi=Z Z_chi` therefore gives respectively

    -i B Z_chi K,       -i B^(-1) Z^2 Z_chi Kd.

The gamma degree of the left is three. The shifts in `Lemma52Product.lean` are all purely imaginary, so the coefficient sequence in the dual Dirichlet series is indeed `conjugate(kappa)`.

For a finite polynomial B, its analytic reflection expands as

    B^dagger(s)=Σ_v conjugate(Bhat(v)) conjugate(psi(v)) v^(s-1).

Consequently the series monomials are exactly

    right: kappa(ell) Ahat(u) conjugate(Bhat(v))/v · (ell u/v)^(-s),
    left:  conjugate(kappa(ell)) Ahat(u) conjugate(Bhat(v))/(ell v)
           · (ell v/u)^s.

No conjugation or denominator factor is missing in (5.4).

## 2. Parity orthogonality and the primitive correction

Let `tau(psi)=Σ_x* psi(x)e_p(x)` and `epsilon_psi=i^(-a)tau(psi)/sqrt(p)` on parity a. Including the principal character temporarily,

    Σ_(psi parity a) psi(y)
      = (p-1)/2 [1_(y=1)+(-1)^a 1_(y=-1)].

Open tau(psi)^d and apply this identity with `y=t x_1...x_d`. The all-character result is

    i^(-da) (p-1)/(2 sqrt(p))
      [Kl_d(t^(-1))+(-1)^a Kl_d(-t^(-1))].

Here the normalization follows from

    p^(-d/2) p^((d-1)/2) = p^(-1/2).

The principal character is even and has Gauss sum −1. Its artificial conductor-p algebraic contribution is `(-1)^d p^(-d/2)`. Removing it gives `+p^(-d/2)` for d=1,3, inside the stripped brace. This is precisely (5.1). It does not use any primitive functional equation for the principal character.

The result is valid at p=3 as well: the even primitive family is empty, and the even brace is identically zero. The original application only needs large odd p.

## 3. CRT, including the 2-part and both parities

For `(D,p)=1`, standard CRT factorization of the finite Gauss sum gives

    tau(chi psi) = chi(p) psi(D) tau(chi) tau(psi).

One direct derivation writes the residue n modulo Dp in CRT coordinates `n=ap p^(-1) mod D + bD D^(-1) mod p`. The additive character factors as `e_D(a p^(-1))e_p(b D^(-1))`. Changing the a and b variables produces chi(p) and psi(D), respectively. This uses no oddness assumption on D.

If c is chi's parity and `b=(a+c) mod 2`, division by `i^b sqrt(Dp)` gives the factor

    i^(a+c-b) = (-1)^(ac).

Therefore

    epsilon_(chi psi)
      =(-1)^(ac) chi(p) psi(D) epsilon_chi epsilon_psi.

The surviving character arguments are then

    right: psi(D ell u/v),       left: psi(D u/(ell v)).

After inversion in the Gauss moment their Kl arguments are

    v/(D ell u),                ell v/(D u).

For an arbitrary subset called Bad, the good-family sum is the complete primitive moment minus that exact subset sum. This gives (5.3), including both i powers and the outer `C_(p,a)`. There is no hidden condition that u, v, ell, or a kappa factor be a D-unit. Only p-unit conditions are needed for these modular inverses. Test tuples with u or v divisible by D are included in the independent checker.

## 4. Double Fourier transform, including all zero modes

Define

    F(c;h,k)=Σ_(r,s != 0) Kl_3(c r s) e_p(hr+ks),
    A(j)=Σ_(x != 0) e_p(jx) = p·1_(j=0)−1.

Opening the two free Kl variables gives

    F = (1/p) Σ_(x,y != 0) e_p(x+y)
                       Σ_(r,s != 0) e_p(c r s/(xy)+hr+ks).

Sum r first. When h is nonzero, exactly one nonzero s makes its coefficient vanish, namely `s=−hxy/c`. Thus

    F = Σ_(x,y != 0) e_p(x+y−hkxy/c) − A(k)/p.

For h,k nonzero, the sum over y in the first term selects `x=c/(hk)`, giving

    Σ_(x,y != 0) e_p(x+y−hkxy/c)=p e_p(c/(hk))+1,
    F=p e_p(c/(hk))+1+1/p.

For h nonzero and k zero, the first double sum is 1, so `F=1−(p−1)/p=1/p`. If h=0, there is no allowed s with vanishing r coefficient, so `F=−A(k)/p`: again 1/p for k nonzero, and `−(p−1)/p` for k zero. This proves every case of (8.1).

Put `C=(p−1)/(2sqrt(p))`, `delta=1_(a=0)`, and

    G_(3,a)(c)=C[Kl_3(c)+(-1)^a Kl_3(-c)]+delta p^(-3/2).

Its transform is exactly

    C[F(c;h,k)+(-1)^a F(−c;h,k)] + delta p^(-3/2) A(h)A(k).

For odd a, all constant terms cancel by antisymmetry. For even a:

* Exactly one zero: `2C/p − (p−1)p^(-3/2)=0`.
* Both zero: `−2C(p−1)/p + (p−1)^2 p^(-3/2)=0`.
* Both nonzero: the constant is

      2C(1+1/p)+p^(-3/2) = sqrt(p).

Therefore the full answer for nonzero h,k is

    (p−1)sqrt(p)/2 · [e_p(c/(hk))+(-1)^a e_p(−c/(hk))]
      +delta sqrt(p),

and it vanishes on both axes. It equals `p G_(1,a)(c/(hk))`. This equality concerns stripped braces; the external `i^(-3a)` from (5.3) must still be retained. Switching to a d=1 root-number sum would introduce an additional `(-1)^a`; the report does not claim to switch it.

The raw Kl transform has nonzero axes. Dropping the small even primitive correction before the finite transform would therefore invalidate the exact zero-mode statement.

The original Kl argument after ell=qrs regrouping is `c r s` with `c=qv/(Du)`. The transform sends it to `c/(hk)=qv/(Duhk)`. The variable q cannot move to the denominator by an additive Fourier convention: negating both h and k leaves hk unchanged. Expanding `q=d b` with eta=mu*power yields a linear phase `e_p(A d)` when b,u,v,h,k are fixed.

## 5. Exact normalization bookkeeping

This section verifies algebraic scaling conditional on the report's analytic weights having the stipulated bounds; it does not establish those bounds.

Let `Y=QRSUV=R_ell U V`. On the center line the scalar Dirichlet monomial has modulus `Y^(-1/2)` up to fixed dyadic constants. The finite character completion has main size `sqrt(p)` times a bounded normalized Kl_3. The original normalized sum is therefore schematically

    [a Mcal sqrt(Y)]^(-1) Σ_p sqrt(p) S_p,

with p in the original interval and `Mcal=Σ_p p`. Since p is comparable to P, an exact sufficient bound is

    Σ_p |S_p| <= a Mcal sqrt(Y)/sqrt(P) · P^(-epsilon).

Using `Mcal >= P²/(4L^77)` and a>1/2, (6.2)'s scale `P^(3/2)sqrt(Y)P^(-epsilon_0)` is sufficient after reducing the fixed saving to pay L^77 and weight norms. It must be applied to the actual sum with every correction handled.

Double Poisson in r,s supplies the factor `RS/p²`; the raw complete Kl transform supplies p. Thus the original sqrt(p) prefactor becomes

    sqrt(p) · RS/p² · p = RS/sqrt(p).

For the main transformed exponential sum, the normalized prefactor is

    RS/[a Mcal sqrt(p) sqrt(Y)].

An exact sufficient prime-summed scale is consequently

    Σ_p |S_dual,p| <= a Mcal sqrt(P) sqrt(Y)/(RS) · P^(-epsilon),

which is (8.4)'s `P^(5/2)sqrt(Y)/(RS)` after the same logarithmic budget. The parity and principal term in (8.2) remains part of the transformed sum. Its smaller finite coefficient does not license deletion without its own estimate.

At the reference `Q,R,S=P^(1+o(1))`, `U,V=P^(theta+o(1))`:

    sqrt(Y)=P^(3/2+theta+o(1)),
    Hfreq Kfreq=P² Tstar²/(RS)=P^o(1),
    trivial prime-summed dual count=P Q U V Hfreq Kfreq
                                  =P^(2+2theta+o(1)),
    required dual scale=P^(2+theta+o(1)).

The residual fixed loss is therefore P^theta. More generally, the uncompleted trivial normalized size is

    [P·sqrt(P)·Y]/[P² sqrt(Y)] = sqrt(Y/P),

which becomes P^(1+theta). One pure-variable completion uses

    Σ_(r != 0) Kl_3(c r s)e_p(hr)
      =sqrt(p) Kl_2(−cs/h)−1/p             (h != 0).

Its Poisson factor `R/p` changes the original sqrt(p) prefactor into R. The remaining prime-summed count is `P Q S U V·(P/R)`, producing the normalized volume

    Q S U V/sqrt(Y)=P^(.5+theta+o(1)).

Thus even a uniform maximal 1/24 power saving in the chosen coefficient variable leaves the report's losses `P^(1+theta−1/24)` and `P^(.5+theta−1/24)`. A fixed logarithmic saving cannot absorb P^theta; independently, an uncanceled fixed positive D power cannot be absorbed by any fixed log P power when `log P=(log D)^9`.

## 6. Independent checks and reproducibility

Run `python checks/check_algebra.py` from this directory. This script does not import or run the evaluated report's checker. It counts triple products directly to build the unnormalized cubic sums, and verifies the entire double Fourier identity in the exact cyclotomic quotient ring, with denominators cleared.

Results:

* 3,650 exact raw cubic identities for every unit c and every h,k, for p=3,5,7,11,13.
* 7,300 exact complete primitive-brace identities, including both parities and all zero modes, over those primes.
* 384 numerical primitive Gauss moments over p=3,5,7,11,13,17,19,29.
* 1,436 numerical CRT root-number checks over 17 positive/negative primitive discriminants, including even conductors with 2-parts 4 and 8.
* 1,440 arbitrary good-subset/bad-correction checks, including D-divisible coefficient indices.
* 72 high-precision branch/common-factor/functional-equation multiplier checks at sigma=−1/2,1/2,3/2, both parities, two root-number phases and both branch signs.

All passed. The largest ordinary floating-point error was below 2.0e−14; branch tests were below 1.0e−65. Detailed counts and errors are in `results/ALGEBRA_ORIGINAL.json`. These regressions supplement the exact derivations; they are not a Lean certificate or an analytic estimate.
