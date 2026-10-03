# Prime phase estimates and absolute budgets

Verified primary sources, 2026-10-03. Write `e_q(t)=exp(2πit/q)`. Throughout `p~P` is prime, `p∤D`, `χ_D` is a primitive quadratic character of conductor `D=P^{o(1)}`, and nonzero phase numerators are units modulo the stated modulus. `Q=P^θ` denotes the scale of a dyadic interval `(Q,2Q]`, not an arbitrary translated interval of length Q. All inverse sums omit nonunits. Bounds are uniform in the unit numerator. Factors `P^{o(1)}` below include fixed powers of D, logarithms, and an arbitrarily small fixed power when explicitly stated.

## 1. Exact split-prime and conductor reductions (derivation)

For primes `ℓ∤D`, the split indicator is `(1+χ_D(ℓ))/2`. The omitted primes dividing D contribute at most `ω(D)` to an unweighted sum. One must also omit `ℓ=p` in reciprocal sums.

The primitive Gauss identity is

`χ_D(n) = τ(χ_D)^{-1} Σ_{b mod D} χ_D(b)e_D(bn)`, with `|τ(χ_D)|=√D`.

For `(n,D)=1`, quadraticity also gives `χ_D(n)=χ_D(n^{-1})`. Consequently BOTH pure phases have an exact composite-modulus reduction:

`χ_D(n)e_p(an) = τ(χ_D)^{-1} Σ_b χ_D(b)e_{Dp}((aD+bp)n)`;

`χ_D(n)e_p(a n^{-1}) = τ(χ_D)^{-1} Σ_b χ_D(b)e_{Dp}((aD+bp)n^{-1})`.

Here the inverse in the last expression is modulo Dp. Every nonzero Gauss coefficient has `(b,D)=1`, so `aD+bp` is a unit modulo Dp. The coefficient ℓ¹ norm is `φ(D)/√D≤√D`. Thus a uniform pure-phase prime estimate `B(q,Q)` gives the split estimate

`B_split(p,D,Q) ≤ (B(p,Q)+√D B(Dp,Q))/2 + O(ω(D)+1)`.

This avoids treating `χ_D(n)K(n mod p)` as a trace function modulo p, which it generally is not. If D is a discriminant but not the primitive conductor, first replace it by the true conductor and account for primes in the inducing modulus. No assertion here covers `p|D`.

## 2. Additive prime phase: Vaughan

[Montgomery–Vaughan, author-hosted draft, Theorem 17.1, printed p.65](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf): for `(a,q)=1` and `|α-a/q|≤q^{-2}`,

`|Σ_{n≤X} Λ(n)e(αn)| ≪ (Xq^{-1/2}+X^{4/5}+X^{1/2}q^{1/2})(log X)^{5/2}`.

For exact `α=a/p`, the pure prime bound has the same three power terms. Passing to dyadic unweighted primes uses partial summation and removal of prime powers; one safe version is the displayed RHS divided by `log Q`, plus `O(√Q log Q)`.

Combining with §1 (own calculation), the χ_D-twisted Λ sum has upper bound

`[Q/√p + √D Q^{4/5} + D√(pQ)](log Q)^C`.

The same power budget therefore holds for split primes. Taking the minimum with the trivial bound gives

`B_add(P,Q) ≤ P^{min(θ, max(θ-1/2,4θ/5,(θ+1)/2))+o(1)}`.

For `θ>1` the relative saving exponent is

`s_add(θ)=min(1/2, θ/5, (θ-1)/2)`.

There is no uniform power saving from this estimate for `θ≤1`; indeed for `a=1` and `Q=o(p)` the additive phase barely moves, so a uniform cancellation assertion would be false.

## 3. General trace functions: exclusion matters

[Fouvry–Kowalski–Michel, Theorem 1.5 and Remark 1.6](https://people.math.ethz.ch/~kowalski/weights-over-primes.pdf) give, for a nonexceptional isotypic trace function K of bounded conductor and every `X≥2`,

`|Σ_{ℓ≤X, prime} K(ℓ)| ≪ X(1+p/X)^{1/12}p^{-1/48+ε}`.

For a fixed smooth weight the stronger bound is `X(1+p/X)^{1/6}p^{-1/24+ε}`; a derivative parameter H costs H. The excluded sheaves have trace proportional to `χ(n)ψ(n)`, with χ multiplicative and ψ additive modulo p. Thus `e_p(an)` is excluded; `e_p(a/n)` and `e_p(a/n+bn)` with `a≠0` are permitted. Below p, cancellation begins at `X>p^{3/4+ε}`. The sharp-cutoff absolute exponent is `11θ/12+1/16+ε` for `θ≤1`, and `θ-1/48+ε` for `θ≥1`. This prime-modulus theorem alone does not justify the χ_D twist or substitution `p→Dp`.

## 4. Reciprocal primes below and above p

[Baker, *Kloosterman sums with prime variable*, Theorem 1](https://www.impan.pl/shop/en/publication/transaction/download/product/82065): write `q=uv`, `(u,v)=1`, u squarefree and v squarefull. For `0<δ≤1/24`, `v≤Q^{1/4}`, and

`v q^{1/2+δ}≤Q≤q^{3/4+δ}`,

`|Σ_{Q<ℓ≤2Q} e_q(a/ℓ)| ≪_δ Q^{1-δ^4/2000}`.

At `q=Dp`, `v≤D=P^{o(1)}`. After §1, this gives `B_split≤P^{θ(1-δ^4/2000)+o(1)}` whenever the displayed inequalities hold with a fixed power margin. In particular there is a nonzero saving at every fixed `θ>1/2` in this short range; the saving can be extremely small.

[Fouvry–Shparlinski, author preprint, Theorems 3 and 4](https://www.imo.universite-paris-saclay.fr/~etienne.fouvry/Fou-Shpar-Ternary-form.pdf) give pure reciprocal dyadic-prime estimates for arbitrary integer modulus q:

`B(q,Q) ≪_ε (Q^{15/16}+q^{1/4}Q^{2/3})q^ε`, for `q^{3/4}≤Q≤q^{4/3}`;

`B(q,Q) ≪ τ(q)^{1/2}q^{-1/2}Q(log Q)^2 + τ(q)q^{1/4}Q^{4/5}(log Q)^{3/2}`, for all `Q≥2`.

After §1, the corresponding absolute P-exponents are

`b_mid(θ)=max(15θ/16,1/4+2θ/3)`;

`b_long(θ)=max(θ-1/2,1/4+4θ/5)`.

The long bound saves precisely when `θ>5/4`, with relative exponent `min(1/2,θ/5-1/4)`. The ranges overlap. Together with Baker, they cover all fixed `θ>1/2`, including `θ≤3.01`, with some power saving. At `θ=3.01`, the displayed long bound is `P^{2.658+o(1)}`. These are usable explicit budgets, not a claim of optimality.

## 5. Bilinear reciprocal products: arbitrary bounded coefficients

[Bourgain–Garaev, *Kloosterman sums in residue rings*, Theorem 3 and Corollary 3](https://www.impan.pl/shop/publication/transaction/download/product/83636) apply to arbitrary integer modulus q. For fixed positive integers k₁,k₂, `|α_m|,|β_n|≤1`, and `(a,q)=1`, put

`F_k(T;q)=T^{k-1}q^{-1/2}+q^{1/2}T^{-k}`.

Then

`|Σ_{m≤A,n≤B} α_m β_n e_q(a/(mn))| ≤ C(k₁,k₂)(log q)^{2(k₁/k₂+k₂/k₁)} AB [F_{k₁}(A;q)F_{k₂}(B;q)]^{1/(2k₁k₂)}`,

where `C=(2k₁)^{45k₁²/k₂}(2k₂)^{45k₂²/k₁}`. The sums omit nonunits. If both variables are restricted to primes, Corollary 3 removes the logarithmic factor and replaces C by `(2k₁)^{1/k₂}(2k₂)^{1/k₁}`. Arbitrary prime-subset indicators and χ_D factors can be included in the separate coefficients. No assertion permits arbitrary jointly dependent coefficients.

For `A=P^α`, `B=P^β`, `q=P^{1+o(1)}`, the full saving is (own algebra)

`δ_BG = -[max((k₁-1)α-1/2,1/2-k₁α)+max((k₂-1)β-1/2,1/2-k₂β)]/(2k₁k₂)`.

Use this only when `δ_BG>0`, retaining the overall size `AB`. A sufficient condition is `1/(2k₁)<α<1/(2(k₁-1))` and its β analogue, where the upper endpoint is infinite for k=1. This is sufficient, not necessary: one factor's negative contribution can outweigh the other's positive contribution. The inequality can be used with dyadic support by setting coefficients to zero outside that support. k₁,k₂ must remain fixed when their constants are hidden in `P^{o(1)}`.

The bound applies directly with `q=Dp`, or with q=p and χ_D absorbed into weights. The diagonal m=n is included. If the numerator vanishes modulo p, no cancellation is available; if it is nonzero but nonunit modulo a composite q, one must reduce to the true additive conductor and check the changed unit condition. Those reductions are not automatic.

## 6. Inverse squares and other fixed powers

[Bourgain–Garaev, *Sumsets of reciprocals in prime fields*, Corollary 5](https://arxiv.org/pdf/1211.4184) allows fixed positive powers r₁,r₂, arbitrary bounded separate coefficients, and arbitrary interval positions:

`Σ_{m∈I₁,n∈I₂} α_mβ_n e_p(a m^{-r₁}n^{-r₂}) ≪ AB p^{1/(2k₁k₂)} A^{-1/[k₂(k₁+1)]}B^{-1/[k₁(k₂+1)]}(AB)^{o(1)}`,

provided `A<p^{(k₁+1)/(2k₁)}`, `B<p^{(k₂+1)/(2k₂)}`. Thus the power saving is

`δ_pow=α/[k₂(k₁+1)]+β/[k₁(k₂+1)]-1/(2k₁k₂)`.

Theorem 9 additionally supplies, for inverse first powers,

`p^{1/8}(AB)^{3/4}(1+A³/p)^{1/16}(1+B³/p)^{1/16}`.

These are prime-field results; a composite-modulus inverse-power extension has not been verified here. Corollary 6 gives prime sums `≪Q^{1-δ(ε,r)}` when `p^{1/2+ε}<Q<p`. Powers at nonzero residues are allowed; poles remain excluded.

## 7. Insert the complete outer budget before claiming success

Let `KU=P^λ`. For the stated completed expressions, the additive scalar contribution is `P^{λ-1}B_add/Q` and the reciprocal scalar contribution is `P^λ B_rec/Q`, up to logarithms. Therefore their P-exponents are respectively

`λ-1-s_add(θ)` and `λ-s_rec(θ)`.

A relative prime saving is useful for an `o(1)` target only if `s_add>λ-1` or `s_rec>λ`, respectively. For a target `P^{-η}`, replace the right sides by `λ-1+η` and `λ+η`. The reciprocal long estimate offers only `s_rec=min(1/2,θ/5-1/4)`; at θ=3.01 this is 0.352. A bilinear argument changes both the relative saving and its prefactor; insert `AB·P^{-δ_BG}` into the actual complete expression before comparing exponents. Splitting an expression into prime factors does not itself pay a multiplicity, normalization, or remaining outer-sum cost.
