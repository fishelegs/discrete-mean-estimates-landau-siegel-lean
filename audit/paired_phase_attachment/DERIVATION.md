# Paired main-term route: a weighted attachment and the remaining signed estimate

Source-level derivation, independently reviewed in the bounded finite trial class. The new analytic combination is not yet a Lean theorem. Original source version: arXiv:2211.02515v1. Original mathematical report and review fingerprints are preserved in MANIFEST.json; portable links replace local research paths in this rendering.

## Result first

The weighted-error and bad-family gaps in the proposed paired route can be
closed at source level using genuine existing inputs. The key is to move an
analytic error to the good-family line `Re(s)=1/2+α/2` and retain the raw
`O(L^-179)` AFE error until after Hölder. No eighth moment of an L-function and
no new moment of `L(s,χψ)` are needed.

With all original conductors, shifts, supports, root factors, gamma factors,
and the inherited branch retained, the actual entries satisfy

    T1[A,J] = (aM)^-1 Σ_{ψ∈Ψ1} ∫_{J0}
        -i rψ Bβ^-1 Zp Qdualβ A Jdual Gdual (𝒜-2) ω ds/(2πi)
        + O_C(a^-1 L^-14),                                      (R-T)

    C1[A,B] = (aM)^-1 Σ_{ψ∈Ψ1} ∫_{J0}
        -i rψ Bβ^-1 (Zp/Zχ) Qdualβ A B Gdual (𝒜-2) ω ds/(2πi)
        + O_C(a^-1 L^-14).                                      (R-C)

Here `𝒜=L(s,ψ)L(s,χψ)/F(s,ψ)` is the actual good-family normalized product,
not a model. In particular its `-2` term is retained. The additional error
from replacing `H=ZpZχ G-Gdual` by `Gdual(𝒜-2)` is

    O_C(a^-1 L^-105) + O_C(a^-1 L^-42),                         (R-E)

which is below the inherited `O_C(a^-1 L^-14)` attachment error. The original
coefficient replacement costs `O_C(a^-1 L^-225)`; its sharper version remains
available. All constants and eventual thresholds are uniform in the original
real primitive χ family, both parities, and the bounded fixed finite trial
class. The assumptions `L(1,χ)<L^-2022` and final exponent `2024` are unchanged.

This is useful progress on attachment, **not an evaluated main term**. The
remaining integral is a concrete signed mixed mean. Neither the functional
equation, Lemma 8.1, Proposition 7.1, Proposition 14.1, nor the available
single-L fourth moments supply a nonzero Schur target residual for it. The
exact paired Mellin/Fourier transformations below expose that signed problem;
without a new signed evaluation they remain equivalent representations.
Actual Gram nondegeneracy (R5) and error after normalization (R6) remain open.

## 1. Fixed definitions and quantifiers

Keep

    L=log D, P=exp(L^9), α=π/log P,
    T0=2πL^519, H0=L^405, W=L^400,
    Jσ={σ+it: |t-T0|≤H0}, J0=J_(1/2),
    ω(s)=sqrt(π)/W · exp((s-(1/2+iT0))²/(4W²)),
    M=Σ_{P<p<P(1+L^-68)}p,     M≥P²/(4L^77).

The normalized measure in the actual discrete means is the original
`c*(ρ,ψ)ω(ρ)/(aM)` with `a` bounded below. The source shifts are purely
imaginary, `β3=β1+β2`, and `|βj|≤4α` eventually; the first shift is the one
covered by the actual Lemma 5.9. The fixed source gap parameter is not changed.

The common coefficient sequences, independent of p and ψ, obey `|a|,|b|,|j|≤C`
and have supports

    A: [P^.502,P^.504],  B: [P^.499,P^.500],
    J: [P^.500,P^.504].

The original χ-weighted tent J1 is included; so is J=A. A finite fixed number
of sequences may depend on D, χ and the prescribed shifts. Constants may
depend on C, that number, and the fixed source gap parameter, never on the
individual sequences or characters. Smooth χ profiles are needed only when
one additionally invokes the previously accepted principal-correction removal;
the good-family character-contour argument here needs only bounded coefficients.

For a primitive character ψ modulo p, let `cψ` and `cχψ` be its parity and the
parity of χψ. Keep exactly

    h_j(s,q)=(q/π)^(1/2-s) Γ((1-s+j)/2)/Γ((s+j)/2),
    Zp=εψ h_cψ(s,p),     Zχ=εχψ h_cχψ(s,Dp),
    Z=Zp Zχ,            rψ=εψ εχψ.

The inherited branch `Bβ` satisfies

    Bβ(s,p)^-2 = Π_j h_cψ(s+βj,p) / h_cψ(s,p)^3.

No new square-root choice is made. The short polynomials and degree-four
product are

    F(s)=Σ_{d≤D⁴}ν(d)ψ(d)d^-s,
    G(s)=Σ_{d≤D⁴}υ(d)ψ(d)d^-s,
    Fd(s)=Σ_{d≤D⁴}ν(d)barψ(d)d^(s-1),
    Gd(s)=Σ_{d≤D⁴}υ(d)barψ(d)d^(s-1),
    Q(s)=L(s,χψ) Π_j L(s+βj,ψ),
    Qd(s)=L(1-s,χbarψ) Π_j L(1-s-βj,barψ).

The notation `Fd,Gd,Qd,Jd` in this report already includes the dual argument
`1-s`. In particular `Jd(s)=Σ bar(j(n))barψ(n)n^(s-1)` and equals `bar(J(s))`
on J0. Reality of ν and υ gives `Fd(s)=bar(F(1-bar(s)))` and the same for G.
Membership of barψ in the good family is not assumed or needed.

The accepted exact arithmetic identity is

    κshort=υ·1[d≤D⁴] * χ * powerβ1 * powerβ2 * powerβ3,
    Kshort(s)=G(s)Q(s)                        when Re(s)>1,
    Kshort_dual(1-s)=Gd(s)Qd(s)               when Re(s)<0.

The coefficient is globally bounded by τ6, including ramified arguments;
there is no condition that d or any pure-power factor be a unit modulo D.

## 2. Bad characters: do this before resumming

Start with the accepted finite central-contour expressions. For every side,
its q cutoff is common to the entire p,ψ family and lies below `P^1.005<P²`.
The upper cutoffs are

    C right P^.9995; C left P^1.005; T right/left P^1.005.

If the accepted low blocks were already deleted, first restore them. Their
integrated contributions are exponentially small under the τ6 envelope. This
does not claim their polynomials are pointwise small on J0.

Write `κshort=κ-Δκ`. On any subset of characters, the whole-family positive
Hölder estimate for the Δκ contribution remains an upper bound. Hence its
normalized contribution on Ψ2 is `O_C(a^-1 L^-225)`, exactly as in the accepted
replacement proof. For the original κ contribution use its genuine small-shift
coefficient energy `Σ_{q≤R}|κ(q)|²/q ≪L^36`, not the τ6 fourth-moment envelope.
With the two bounded polynomials' sixth moments, Hölder gives

    Σ_{Ψ2}|K_R A V|
      ≪ (P²L^36)^(1/2) (P²L^81)^(1/6)
         (P²L^81)^(1/6) (M L^-739)^(1/6),                 (2.1)

where V is B or Jd as appropriate. The source fact is
`|Ψ2|≪M L^-739`, **not** `P² L^-739`. The unit central multipliers and bounded
Gaussian mass add no cost. Dividing (2.1) by aM gives

    a^-1 L^[18+13.5+13.5-739/6+77·5/6] = a^-1 L^-14.   (2.2)

Thus restricting all four finite short-κ expressions from Ψ to Ψ1 costs
`O_C(a^-1 L^-14)`. C right has a better original fourth-moment bound, but this
uniform second-moment argument suffices. No τ6 fourth-moment substitution
is used to claim an original logarithmic exponent.

This order avoids ever applying the good-family F,G approximation to Ψ2, and
avoids moving a bad character's untruncated reciprocal L-function through a
zero. The full-family completion already paid an O(L^-14) cost; paying another
fixed multiple does not change the exponent.

## 3. Finite-to-infinite resummation and contour order

For each good character, move each finite polynomial integral from J0 back to
its accepted safe segment, `J_(3/2)` on the right and `J_(-1/2)` on the left.
These are finite polynomials times the exact analytic gamma/root multiplier.
They have no reciprocal-L poles. At the two fixed endpoint heights the Gaussian
is `exp(-L^10/4+o(1))/W`; all other factors over the fixed strip have total
envelope `exp(O(L^9))`, even after summing the family. These horizontal errors
are exponentially small.

On the safe segments, insert the absolutely convergent full short-κ series.
The accepted fixed-window tail proof applies with `log^5(2R)` in place of
`log^3(2R)`, because `|κshort|≤τ6`. Its strict exponent gaps are unchanged:

    C right:  .9995+.502+.499-2 = .0005,
    C left:   1.005-.504-.500 = .001,
    T right:  1.005+.502-1-.504 = .003,
    T left:   1.005+.500-.504-1 = .001.

The unsimplified conductor ratios still include D, p, t and t0. Moving each
tail outward to `Re(s)=1/2±L^9` pays them exactly as in the fixed-window proof,
and leaves `exp(-cL^10)` after summation. The extra fixed logarithmic power does
not consume a support gap. No factorwise replacement of the constraint
`q=d r0 r1 r2 r3<R` is performed.

Only now identify the full series with GQ and GdQd on their convergence sides.
All four individual L-functions in Q and Qd are entire: ψ is primitive
nonprincipal modulo p and χψ is primitive nonprincipal modulo Dp. Both G and
Gd are finite polynomials. The inherited Bβ and each gamma multiplier are
holomorphic and nonzero in the high finite strips in use. The resulting
integrands can therefore be moved to J0 with no pole crossings. Crude standard
polynomial conductor/height growth on the fixed strip again gives
`exp(O(L^9))`; the horizontal Gaussian absorbs it.

This is an identity for integrated expressions with paid errors, not the false
pointwise statement `Kshort_R(s)=G(s)Q(s)` on J0. It also does not continue the
chosen Bβ branch down an unrestricted full vertical line.

## 4. Exact functional-equation pairing

The four degree-one functional equations give

    Q(s)=Zχ(s) Zp(s)^3 Bβ(s,p)^-2 Qd(s).                 (4.1)

Define `H(s)=Z(s)G(s)-Gd(s)`. The exact common-contour right-minus-left
integrands, before ω, are

    T: -i rψ Bβ^-1 Zp Qd A Jd H,
    C: -i rψ Bβ^-1 (Zp/Zχ) Qd A B H.                    (4.2)

For example the T right multiplier is `-i rψ Bβ/Zp`. Substituting (4.1)
produces `-i rψ Bβ^-1 Zp Qd (ZG)`; the left expression has the same prefactor
times Gd. The C calculation is identical with an additional `Zχ^-1`.

The missing degree-two gamma/root factor is precisely `ZpZχ`. It includes
`h_cχψ(s,Dp)`, including the χ parity and conductor D. Neither (4.1) nor a
completion converting both target trace functions to Kl2 makes H vanish.

## 5. Exact defect remainder, before taking norms

For ψ∈Ψ1 and s in the thin central strip put

    δ(s)=F(s)G(s)-1,
    δd(s)=Fd(s)Gd(s)-1,
    e(s)=L(s,ψ)L(s,χψ)-F(s)-Z(s)Fd(s),
    𝒜(s)=L(s,ψ)L(s,χψ)/F(s).

The genuine good-family theorems give

    |δ|,|δd|≤4L^-227,       |e|≤C44 L^-179,
    |G|≤2L^79,             F≠0, G≠0.                    (5.1)

The dual assertions follow by reflection to the same ψ at positive height.
Exactly, with no asymptotic substitution,

    H = Gd(𝒜-2) + R,
    R = [ ZG(δ-δd) - e G Gd ]/(1+δ).                   (5.2)

One can check (5.2) directly using `FG=1+δ` and `FdGd=1+δd`. This separates
the extremely small short-inverse error from the raw AFE error. Taking the
bound `|F^-1|≪L^79` first would produce only a pointwise `L^-100` error and
discard the useful short polynomial G inside the averaged error.

At actual good zeros the normalized product 𝒜 is zero, but (5.2) is required
throughout a contour. The fact `H≈-2Gd` at those zeros does not justify dropping
the 𝒜 term from the contour integral.

## 6. The off-central line reduces four L factors to two

Fix `θ=1/2` and use `Jθ=J_(1/2+θα)`. For sufficiently large D, its entire
closed segment, its reflection, and every horizontal connector to J0 lie in
the genuine Ω1, Ω2 and Ω3 domains needed here. The source height margins are
H0+5, H0+4 and H0+3; all original shifts are less than 1 in absolute value
eventually. On the line, the source Proposition 2.2 places every relevant zero
of L(s,ψ) on Re(s)=1/2. Thus `dist(s,ρ)≥θα` for the nearby zeros. For a zero
outside the original Ω, either its imaginary distance from this segment is at
least 2 or its real distance is at least `1/2-α/2`; both exceed α/2 eventually.
Lemma 5.9 applies with a
fixed separation constant, uniformly over the whole segment:

    |L(s+β1,ψ)/L(s,ψ)|≪L^9.                             (6.1)

There is no analogous assertion made on J0 at its zeros.

The genuine Lemma 4.3 gives `|F'/F|≤140800 L` on Ω2. Integrating its real
part on horizontal paths of length at most α, and using conjugation on J0,
gives

    |Fd/F| + |F/Fd| ≪1,
    |G/Gd| + |Gd/G| ≪1                                 (6.2)

on Jθ. The second follows from the first and `|δ|,|δd|<1/2`. In particular
the factors are bounded by fixed constants once `αL=πL^-8` is small enough;
there is no `L^158` pointwise ratio loss.

The exact gamma formulas give, uniformly on this fixed thin line,

    |Zp|^±1, |Zχ|^±1, |Bβ|^±1 ≪1.                     (6.3)

Indeed the modulus powers are `(pt/(2π))^(1/2-σ)` and
`(Dpt/(2π))^(1/2-σ)`, and `α log(Dpt)=O(1)`. No D or t0 power is suppressed.

By (5.1), the AFE, and (6.2)-(6.3),

    |L(s,ψ)L(s,χψ)G(s)|
      = |(1+δ)(1+Z Fd/F)+eG| ≪1.

Consequently, by factoring Q using L(s,ψ) on this separated line,

    |QG| = |L(s,ψ)L(s,χψ)G|
            ·|L(s+β1,ψ)/L(s,ψ)|
            ·|L(s+β2,ψ)L(s+β3,ψ)|
          ≪ L^9 |L(s+β2,ψ)L(s+β3,ψ)|.                (6.4)

Finally (4.1), (6.2) and (6.3) give the crucial exact-weight majorant

    |Qd Gd| ≪ L^9 |L(s+β2,ψ)L(s+β3,ψ)|.              (6.5)

Only the two genuine L-functions of conductor p occur on the right. In
particular this argument does not import an unproved uniform moment for a
conductor-Dp L-function or for a degree-four product.

## 7. Available moments, weighted bounds, and the -105/-42 budgets

The actual theorem `lemma81_uniform_actual_L_fourth_moment` in
`ZhangLS/Spec/Lemma81ActualLFunctionMoments.lean:23` states uniformly

    Σ_{ψ∈Ψ}|L(s,ψ)|⁴ ≪ P² L^36

for `|Re(s)-1/2|≤α` and `|Im(s)-T0|≤H0+1`. Its proof uses the genuine Lemma
6.1 approximation and its actual E1 error; it is not a moment hypothesis.
Both `s+β2` and `s+β3`, for s∈Jθ, lie in this exact domain eventually, since
the shifts are pure and `4α<1`. The two uses therefore carry no hidden D or
t0 powers. There is no need to generalize that theorem to χψ.

The actual finite-polynomial fourth moments give

    ΣΨ |A|⁴, ΣΨ |B|⁴, ΣΨ |Jd|⁴ ≪_C P²L^36.          (7.1)

The inverse-character version follows by conjugating the coefficient sequence
and reflecting s; the same thin-strip bound applies. Cubing the bounded
polynomials gives the accepted sixth moments

    ΣΨ |A|⁶, ΣΨ |B|⁶, ΣΨ |Jd|⁶ ≪_C P²L^81,          (7.2)

because their cube lengths are at most P^1.512<P² and their coefficients are
bounded by a fixed multiple of τ3, with `τ3²≤τ9`.

The extra short inverse has a better sixth-moment logarithm:

    ΣΨ |G(s)|⁶ ≪ P²L^36.                               (7.3)

To prove (7.3), cube its actual polynomial. The resulting support is at most
D^12<P² eventually; `|υ|≤τ2` gives cube coefficients at most τ6, including
the truncation constraints. Their harmonic square sum is at most

    Σ_{n≤D^12} τ6(n)²/n ≤ (1+log(D^12))^36 ≪ L^36.

Apply the actual second large sieve with its common height twist. The
thin-strip exponential weight is uniformly bounded, since the support is below
P². This proves (7.3) without applying a bounded-coefficient polynomial theorem
to υ, and without pretending that G has coefficients bounded by a constant.

Let V mean B or Jd. Combining (6.5) with four fourth moments gives

    Σ_{Ψ1}|Qd Gd A V|
       ≪_C L^9 (P²L^36)^(1/4+1/4+1/4+1/4)
       = O_C(P²L^45).                                  (7.4)

For the extra G in the raw AFE error use Hölder exponents `4,4,6,6,6` for
`L(s+β2), L(s+β3), G, A, V`. Their reciprocals add to one. Thus

    Σ_{Ψ1}|Qd Gd G A V|
       ≪_C P² L^[9+36/4+36/4+36/6+81/6+81/6]
       = O_C(P²L^60).                                  (7.5)

The estimates (6.2) and `|1+δ|≥1/2` now turn the two parts of R in (5.2) into

    Σ_{Ψ1}|Qd A V R|
       ≪_C P²(L^[-227+45]+L^[-179+60])
       = O_C(P²(L^-182+L^-119)).                       (7.6)

The exact multipliers in (4.2) are bounded on Jθ, and the normalized Gaussian
mass there is at most `exp((θα)²/(4W²))`, hence uniformly bounded. Division by
aM, using the genuine prime-mass lower bound, gives

    O_C(a^-1 L^[-227+45+77]) = O_C(a^-1 L^-105),
    O_C(a^-1 L^[-179+60+77]) = O_C(a^-1 L^-42).         (7.7)

To apply this to the original central error, move **the analytic error
integrand** from J0 to Jθ. In (5.2), `1+δ=FG` is nonzero on the closed strip;
all other factors are holomorphic there. No L reciprocal is being moved.
The quotient L(s+β1)/L(s) appears only in the bound (6.4) on the separated
line. Horizontal endpoint terms are exponentially small by the same source
Gaussian and `exp(O(L^9))` envelope as in Section 3. This proves the signed
integral error bound (R-E); it does **not** assert that the absolute central
integral obeys (7.4) or (7.5).

Together Sections 2-7 prove (R-T) and (R-C) at source level from the accepted
attachments and the genuine repository inputs. The newly closed weighted
step is substantially more precise than the inherited completion error.

## 8. What an exact finite Mellin transformation retains

For an actual interval mask `I=[L_I,U_I)` define the explicit Perron kernel

    W_I(z)=(U_I^z-L_I^z)/z,

with its removable value at z=0. For `Re(s)+c>1`, the exact endpoint convention
is

    Kshort_I(s)=lim_{Y→∞}(2πi)^-1∫_{c-iY}^{c+iY}
         W_I(z)G(s+z)Q(s+z) dz + E_I(s),               (8.1)

where `E_I(s)` is `+½κshort(L_I)ψ(L_I)L_I^-s` when L_I is an integer,
minus the corresponding upper-endpoint term when U_I is an integer. These
terms convert Perron's half endpoints to the inherited inclusive-lower,
exclusive-upper convention. For a smooth finite mask, its ordinary Mellin
transform replaces W_I. A truncated integral has a genuine Perron remainder;
it cannot be discarded without a bound. A Gaussian regularization is another
valid exact limiting procedure, but its limit and endpoints must be justified.

Inside (8.1), the functional equation is at `s+z`, not s:

    Q(s+z)=Γ4(s+z)Qd(s+z),
    Γ4(v)=Zχ(v)Π_j Z(v+βj,ψ)
         =Zχ(v)Zp(v)^3 Bβ(v,p)^-2.                   (8.2)

Here `Qd(s+z)` means exactly `Qdualβ(1-s-z)` under the convention of Section
1. Globally on a Mellin contour use the first definition of Γ4 in (8.2).
Its second expression denotes the canonical meromorphic gamma quotient and
agrees with the inherited Bβ branch wherever that branch is defined; no
global square-root branch is being asserted. The external T multiplier
remains `-i rψ Bβ(s,p)/Zp(s)`, and the C
multiplier remains `-i rψ Bβ(s,p)/(Zp(s)Zχ(s))`. It cannot be replaced by its
value at s+z. After reflecting z to -z, the right coefficient has
`W_I(-z)Γ4(s-z)G(s-z)`, while the left coefficient has its own interval kernel
and `Gdual(1-s+z)`. The q intervals on the two sides are generally different.
Moving their z contours to a common line requires the exact limiting,
horizontal, and endpoint contributions. Gamma poles that are removable in
the entire product `Γ4(v)Qdualβ(1-v)=Q(v)` must be kept canceled, rather than
counted as spurious independent residues.

This formula provides an explicitly specified transform, with all shifts and
gamma factors. It supplies no main term until an actual contour deformation
or arithmetic evaluation identifies a surviving term and bounds the rest.
Restoring the full series as in Section 3 bypasses these finite-mask Mellin
bookkeeping obligations and leads exactly to H, then (R-T)/(R-C); it does not
compute their signed averages.

## 9. Exact completion, including the χ factor

The four-factor arithmetic region is still

    q=d r0 r1 r2 r3, d≤D⁴,
    weight=υ(d)χ(r0)Π_j rj^-βj,
    q∈I_side, p∤qmn.

The side intervals are unchanged:

    C+: [.995,.9995), C-: [1.0005,1.005),
    T+: [.995,1.005), T-: [.997,1.005)

in log_P q. The r0=1 regime is present. No condition of coprimality to D is
introduced for d or r1,r2,r3.

For a pure-power variable r=rj, fix all other variables and put
`R=Π_{k≠j}rk`, with r0 included. The target trace functions in r are

    F+(r)=e_p(A/r),    A=χ(-1)n/(D d R m),
    F-(r)=Kl3(B r;p), B=χ(-1)d R n/(D m),

where these fractions are modular units. Their real analytic weights include
respectively

    r^-βj ·1_I(dRr)·U+_p(dRrm/n),
    r^(βj-1)·1_I(dRr)·U-_p(m/(dRrn)),

as well as the unaltered outside factors. These are different weights and
different masks. With `Fhat(h)=Σ_{u≠0}F(u)e_p(hu)`, exact finite completion is

    Σ_{r≥1,p∤r}w(r)F(r)
      = p^-1 Σ_{h mod p} Fhat(h) Σ_{r≥1}w(r)e_p(-hr).  (9.1)

For h≠0,

    Fhat+(h)=sqrt(p) Kl2(Ah;p),
    Fhat-(h)=sqrt(p) Kl2(-B/h;p)-1/p;

at h=0 their values are -1 and -1/p. Thus completion produces a common Kl2
family, but neither the arguments nor the analytic weights agree. The zero
frequency and every `-1/p` correction are actual parts of (9.1).

There is also a useful exact CRT formula if one completes the χ-weighted
factor itself. Extend F by zero at residue 0 modulo p. For every integer h,

    Σ_{u mod Dp} χ(u)F(u mod p)e_(Dp)(hu)
      = τ(χ)χ(p)χ(h) Fhat_p(h·D^-1 mod p).             (9.2)

To prove it write `u=a p·p^-1_(D)+b D·D^-1_(p)` by CRT. The D sum is the
primitive χ Gauss sum `τ(χ)χ(h)χ(p)`; the p sum is the displayed Fhat. The
formula includes h divisible by p, and vanishes when h is not a unit modulo D.
It covers even and ramified conductors with the actual primitive character.
The factor τ(χ), its parity phase, and χ(p) are indispensable. Formula (9.2)
is the finite arithmetic counterpart of retaining the conductor-Dp gamma in
(8.2); its presence prevents an automatic pure-power cancellation argument.

Equations (9.1)-(9.2) are computable finite transforms. To turn them into a
main-term estimate one must control the aggregate nonzero frequencies, all
product-length regimes, and the exact q-mask boundaries. A partition by the
largest factor, with fixed tie breaking, covers all regimes; at least one
factor has size ≥P^.24875/D, but that factor need not be r0 and may still be
too short for completion alone to save the required amount. Algebraic
completion has not proved cancellation at the aM scale.

## 10. Why the existing mean-value theorems do not evaluate this main term

The existing theorems genuinely do the following:

* Lemma 8.1 attaches a zero mean of two bounded, p-independent polynomial
  sequences to the original cβ contour and its reflected conjugate. The
  added factor rψ cannot be encoded by one common coefficient sequence.
* Proposition 7.1 evaluates the original one-reciprocal-gamma κ contour.
  Its Gauss average produces a **direct** additive phase of the form
  `e_p(l/k)`, followed by the source residue calculation for κ. It is not the
  inverse-additive `e_p(χ(-1)n/(Dqm))` mean above.
* Proposition 14.1 handles one `Z(s,χψ)^-1` factor and arbitrary τ5-bounded
  κ* with its original bounded short second sequence. Its direct additive
  phase, χ-induced component and conductor reduction are concrete. The
  new pair has the incompatible positive Zp/three-Gauss structure. Moreover
  κshort itself has only the τ6 pointwise envelope, so it cannot simply be
  substituted into the τ5 interface.
* The actual single-L fourth moments, finite polynomial moments, and Lemma
  5.9 provide upper bounds. They suffice for (R-E); they do not determine a
  phase or a lower bound for a signed target correlation.

Multiplying the candidate coefficient by a root number would violate the
common-coefficient quantifier in P7/P14. Applying (4.1) to move gamma factors
merely returns the same paired expression. Replacing the four actual factors
by an unspecified transformed kernel, throwing away the 𝒜 term, or declaring
the transformed trace sums orthogonal would be a new unsupported estimate.

These are scope mismatches of the current inputs, not a theorem that a stronger
structured moment or an appropriately proved extension of their methods cannot
work. The -105/-42 result demonstrates that some of the requested attachment
obligations are already dischargeable; the signed arithmetic evaluation is the
remaining genuinely new one.

## 11. Smallest new signed estimate and R5/R6

Use the accepted actual matrix notation with

    X=A, Y=Zχ bar(B), U=rψ A,
    E=[[H(A,A),C0[A,B]],[bar(C0[A,B]),H(B,B)]],
    b=(H(A,J),bar(C0[J,B]))ᵀ,
    t=T1[A,A], u=C1[A,B], q=T1[A,J], k=(bar(t),bar(u))ᵀ.

If the actual old block E is positive definite, let `x=E^-1b`. Then

    s=H(A,A)-k*E^-1k,
    τ=q-(t,u)x,
    Rres=H(J,J)-b*E^-1b.                               (11.1)

For bounded x, a **single** signed mixed-mean theorem sufficient to evaluate
the new Schur target residual is

    𝒮_D(A,Vx) = μ_D + error_D,                         (11.2)

where

    Vx(s)=Jd(s)-x1 Ad(s)-x2 Zχ(s)^-1 B(s),
    𝒮_D(A,V)=(aM)^-1 Σ_{Ψ1}∫_{J0}
        -i rψ Bβ^-1 Zp Qd A V Gd(𝒜-2) ω ds/(2πi).

All functions in (11.2) are explicitly specified actual functions. Sections
2-7 imply `τ=𝒮_D(A,Vx)+O_C((1+|x1|+|x2|)a^-1L^-14)`.
An independently bounded approximation xhat can be used instead, provided the
old-block/old-target error and its propagation are included. This avoids
asking for unrelated generic trace-function theorems: (11.2) concerns the
precise target residual of this finite trial.

For the fixed zero-moment smooth-profile test in the prior report, the **old
model** has b0=0. Only after its actual attachment is proved at sufficient
precision may one replace Vx by Jd at leading order. At that point the
smallest first new scalar target is the explicit (R-T) integral for that fixed
f and the original tent J. A nonzero computable μ_D is still needed; the
current formulas do not exhibit one. If its leading term is zero, a quantified
next-order signed calculation is required for any log-scale improvement.

R5 remains the actual norm obligation

    s_D≥s_*>0,

or a proved asymptotic `s_D∼s_* L^-γ` with `s_*>0`, together with the actual
old-block invertibility and target norm. For the special diagonal old model,
the candidate formula is

    s0=A0-|t0|²/A0-|u0|²/B0.

It is not positive merely because A0 and B0 are positive. Ordinary harmonic
coefficient norms, fixed profile widths, the φ(D)/D density, and an M1 scalar
bound of order L^-13 do not imply this actual Schur norm lower bound.

R6 remains a joint error certificate. If K is the actual augmented Gram/target
matrix, Khat a proposed explicit main matrix, and each entry error is ≤ε_D,
then every specified coefficient vector z satisfies

    |z*(K-Khat)z|≤ε_D ||z||_1².                         (11.3)

Every old and new entry must be covered. At a residual norm `s_D≈L^-γ`,
bounded old projection coefficients give normalized error of order
`ε_D/s_D`. To certify a margin `η_D≈L^-δ`, a sufficient requirement is

    ε_D=o(s_D η_D)=o(L^[-γ-δ]).                         (11.4)

For example, retaining an L^-8 margin while normalizing a residual with squared
norm L^-8 requires `o(L^-16)` entry precision. The inherited L^-14 error does
not meet it, even though the new L^-42 weighted substitution does. Relaxing
fixed numerical coefficients does not remove (11.3)-(11.4) and does not change
the original exponents -2022/-2024 or their uniform quantifiers.

## 12. Scoped stopping condition

The attachment route has a concrete new source-level success: one may replace
the exact paired defect by the actual `Gdual(𝒜-2)` in the completed means, with
an additional normalized `O(a^-1L^-42)` error. No unknown higher L moment or
uncontrolled bad-family use remains in that substitution.

Stop before any strict-gain or completed-main-matrix claim until (i) the signed
quantity (11.2), or its equivalent explicit finite inverse-additive-minus-Kl3
sum, has an evaluated surviving term and a quantified remainder, (ii) the
actual residual norm R5 is proved, and (iii) the full matrix meets R6. A
zero-main-term result with an actual norm bound would also be informative, but
it would rule out only the corresponding leading gain in this specified trial.
The present stopping point makes no global impossibility assertion about root
phases, different trials, a new structured moment, or a finer-scale repair.

## 13. Sources and reproducibility

Frozen inputs (SHA256):

* Independent review: `1bd6033619e906f81dcd6fd31be5f18f8312c0b2e1c64787bdb76f62c7644cce`
* Short-υ bridge: `b5584906c40bc2447e45fc300d502eee23fe8a816b89987c3bae54a1e935266b`
* Phase main matrix: `ef06b73b6ef3a6cd848996e2c7ee701234229eb662b45e01e89ebb7e9cbc21cd`
* Annular report: `1839df7636ee4adcdacae99228c5ecf4b089556815fcc6c17d5b0888e3a91ea2`
* Fixed-window addendum: `c457ac0dfb91b14a9bd45dee4615fa489cb98c2a90c0569d00a8ca3e0873c52e`

Inspected genuine repository interfaces, under `ZhangLS/Spec/`:

* `Lemma23ProductApproximation.lean`: FG error throughout Ω1
* `Lemma23SectionFourLogDerivative.lean:204`: actual Ω2 `|F'/F|≤140800L`
* `Lemma44ApproximateFunctionalEquation.lean`: raw actual error L^-179
* `Lemma45Normalization.lean`: actual 𝒜 and reflection identities
* `Lemma59.lean`, theorem `lemma59_proved`: original all-zero-separated first-shift quotient
* `Lemma81ActualLFunctionMoments.lean:23`: actual L fourth moment, including precise height domain
* `Lemma81PolynomialFourthMoment.lean:109`, `Lemma81ActualPolynomialMoments.lean`: actual polynomial moments and inverse-character versions
* `Lemma33.lean`, `Lemma34TauProduct.lean`: actual sieve and harmonic divisor moments
* `Proposition21.lean:19`: actual Ψ2 cardinality relative to M
* `Lemma81PrimeMassLower.lean`: original prime-mass lower bound
* `Proposition71OriginalFamilyExtension.lean`, `Proposition71FinalAssembly.lean`, `Proposition141.lean`: actual old mean interfaces

Primary mathematical text: [arXiv:2211.02515v1 source](https://arxiv.org/abs/2211.02515v1), especially
Sections 2-8 and 14. The arithmetic obstruction statements above are checked
against its actual integral kernels, not just theorem names.

`check_budgets_and_transforms.py` checks rational exponent budgets, the exact
algebraic defect identity, support/height asymptotics, and the CRT χ-completion
formula for odd/even/ramified example conductors. These finite tests supplement
the uniform arguments; they do not test assumption (A), evaluate any large-D
main term, prove R5, or provide a Lean verification. No compilation was run.
