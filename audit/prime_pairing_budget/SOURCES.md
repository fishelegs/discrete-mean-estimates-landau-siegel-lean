# Primary-source audit

All links were opened on 2026-10-03. These are the sources actually named by the candidate, not an assertion that this is a survey of every result available by that date. Formulas below are mathematical statements of the sources; conductor and full-budget deductions are independently derived in INDEPENDENT_REVIEW.md.

## Montgomery–Vaughan, additive primes

[Author-hosted Multiplicative Number Theory II draft](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf), Theorem 17.1, printed p.65, PDF p.77. For `(a,q)=1`, `|alpha-a/q|<=q^-2`, the prefix von Mangoldt sum is bounded by

    (N q^-1/2+N^4/5+N^1/2 q^1/2)(log N)^5/2.

The candidate reproduces the powers and hypotheses correctly. Uniform prefix endpoints suffice for moving intervals. Partial summation and prime-power removal give the stated unweighted-prime bound. Substituting q=Dp after the exact quadratic Gauss expansion incurs the declared conductor cost. This theorem does not grant cancellation at arbitrary extra Fourier frequencies with the original denominator p.

## Fouvry–Kowalski–Michel, trace weights

[Author-hosted Algebraic trace functions over the primes](https://people.math.ethz.ch/~kowalski/weights-over-primes.pdf), Theorem 1.5 and Remark 1.6, printed pp.3–4. The sharp prefix bound is `X(1+p/X)^(1/12)p^(-eta/2)`, eta<1/24; the smooth version is `H X(1+p/X)^(1/6)p^-eta` with the specified derivative parameter H. The sheaf must be isotypic and nonexceptional; constants depend polynomially on its conductor.

The excluded class includes multiplicative-character times additive-character weights. Pure linear additive phases are excluded. The reciprocal and reciprocal-plus-linear rank-one phases with nonzero reciprocal coefficient have bounded conductor and are nonexceptional. This is a prime-modulus theorem. The candidate correctly declines to treat a varying chi_D factor as a trace function modulo p or to replace p by composite Dp.

## Baker, short reciprocal primes

[Published Kloosterman sums with prime variable](https://www.impan.pl/shop/en/publication/transaction/download/product/82065), Acta Arith. 156.4 (2012), Theorem 1, printed p.352. Write `q=uv`, `(u,v)=1`, u squarefree and v squarefull. For `0<delta<=1/24`, `v<=x^1/4` and `v q^(1/2+delta)<=x<=q^(3/4+delta)`, the prime sum saves `x^(delta^4/2000)` relative to x.

Theorem 1 is presented for `(x,2x]`. Its proof, printed pp.361–362 (PDF pp.11–12), explicitly chooses `(x,x']` with `x'<=2x` and proves the same uniform bound. Thus moving upper endpoints are justified by the proof, not by an unsupported conversion of a dyadic statement. For q=Dp the squarefull part divides D. Fixed margins and D=P^o(1) justify the candidate's use.

## Fouvry–Shparlinski, intermediate and long reciprocal primes

[Author-hosted On a ternary quadratic form over primes](https://www.imo.universite-paris-saclay.fr/~etienne.fouvry/Fou-Shpar-Ternary-form.pdf), Theorems 3–4, printed pp.11–12. The intermediate bound is `(x^(15/16)+q^(1/4)x^(2/3))q^epsilon` for `q^(3/4)<=x<=q^(4/3)`; the long bound is `tau(q)^(1/2)q^-1/2 x(log x)^2+tau(q)q^(1/4)x^(4/5)(log x)^(3/2)`. Both allow integer composite q and unit numerator.

Section 3.1, printed p.10, explicitly permits replacing the dyadic prime range by a prefix with the same bound up to a constant. The proofs also use prefix von Mangoldt sums. Endpoint differences therefore provide the uniform interval control needed here. The candidate's power exponents, overlap and long saving .352 at theta=3.01 are correct.

## Bourgain–Garaev, residue-ring bilinear sums

[Published Kloosterman sums in residue rings](https://www.impan.pl/shop/publication/transaction/download/product/83636), Acta Arith. 164.1 (2014), Theorem 3, printed p.44, and Corollary 3, printed p.52. The theorem has full prefactor N1*N2 and factor

    [F_k1(N1;q)F_k2(N2;q)]^(1/(2k1k2)),
    F_k(N;q)=N^(k-1)q^-1/2+q^1/2 N^-k.

The candidate's fixed-k constants and logarithmic powers match the source. Separate coefficients may be arbitrary complex numbers of modulus at most one. Zero-extension permits dyadic support, gcd conditions and other individual subsets; separate Fourier/Mellin phases are therefore legal. The prime-variable corollary improves constants/logarithms and still permits separate coefficients. It does not allow a general jointly dependent mask. Nonunits are omitted and the numerator must be a unit.

## Bourgain–Garaev, prime-field inverse powers

[Sumsets of reciprocals in prime fields and multilinear Kloosterman sums](https://arxiv.org/pdf/1211.4184), arXiv:1211.4184v1, Corollaries 5–6, printed p.64, and Theorem 9, printed p.7. Corollary 5 permits fixed positive inverse powers, arbitrary interval positions and separate bounded coefficients, under `Ni<p^((ki+1)/(2ki))`; the candidate's exponents and `(N1N2)^o(1)` loss match. Corollary 6 is a prefix prime sum for `p^(1/2+epsilon)<N<p` with an unspecified positive saving depending on epsilon and the inverse power. The first-power Theorem 9 formula in the candidate matches its displayed source statement; its use requires actual prime-field intervals, so repeated integer ranges need separate handling.

None of these assertions supplies a composite-modulus inverse-power prime theorem or a chi_D-twisted version. In particular quadraticity cannot convert chi_D(n) into chi_D(n^-2). The candidate does not apply such an unsupported extension.
