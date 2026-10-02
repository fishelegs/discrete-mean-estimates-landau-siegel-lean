# Lemma 15.1: actual arithmetic and local-residue audit

## Status

This is a bounded genuine arithmetic/local-residue bridge, **not a proof of Lemma 15.1**.
No final quadratic-form estimate, no desired arithmetic asymptotic, no assumption
`eventually ¬(A)`, and no unproved Lemma 5.6 is used. In particular the coefficient
of the full arithmetic sum has not yet been proved to be the residue-model coefficient.
The original target is retained separately with α₁ an unspecified explicit parameter.
No definition of α₁ is guessed.

## Source checks and the target before any repair

Official local source: `/tmp/zhang-2211.02515-source.tex`; official PDF:
`/tmp/zhang-2211.02515.pdf`. SHA256 hashes are in `integration_manifest.json`.
The source macros are `\sp=(s,\psi)` and `\pc=\chi\psi` (TeX lines 42,45).

* (2.13): β₁=iα(1−5c′αL), β₂=2iα(1+c′αL), β₃=3iα(1−c′αL).
  The code reuses all three actual shifts through `lemma83PaperBeta D c j`;
  `c` is fixed independently of D, rather than reset to zero.
* (2.21),(2.22),(2.26): P₁=P^.504, P₂=P^.5 T^−10, P₃=P^.498,
  β₆=3iα/2, β₇=5iα/2 and all three original exact decimal iotas are retained.
* (12.1),(12.2), TeX 3363–3372: H₁₄ is cut **strictly below** P^(1/2),
  and B=(H₁₄+iota₂H₁₂)H₂. Thus the complementary tail includes equality
  n=P^(1/2); an endpoint error must be justified if this is replaced by `>`.
* (15.1), TeX 3981 and visually inspected PDF page 79, writes
  B=Σ b(n)χψ(n)/n^s. Define U,V as the two original coefficient kernels.
  Its natural χψ-coefficient is b₀(n)=Σ_ab=n U(a)V(b). At χ(n)=0 this
  display alone does not determine b; the natural convolution extension is
  explicitly used in `lemma151BChiPsi`, not claimed to follow by uniqueness.
* Immediately before (15.5), TeX 4070, the source instead writes the
  **ψ** coefficient of (L(s+β₁,ψ)L(s+β₂,ψ)/L(s,ψ))B as κ₁*b.
  The actual ψ coefficient of B is bψ(n)=χ(n)b₀(n), so the correct convolution
  in that basis is κ₁*bψ. This conflicts with taking the same b literally
  from (15.1). PDF page 81 was rendered and visually inspected at the same formula.
* Lemma 15.1, TeX 4273–4296 / PDF page 86, has the external χ(n), the
  original strict n₁<T and n₁∈N(Q), Q=∏_{prime q<D⁴}q. Appendix B treats
  single-kernel sums without that external χ. This is compatible with bψ,
  because bψ(n₁n)χ(n)=χ(n₁)b₀(n₁n) on the rough domain, and is not an
  identity for b₀. The basis repair is logically prior to a tail-phase repair.

Both b conventions and the literal original numerical target are kept separately
in `Lemma151Definitions.lean`. No coefficient is selected to improve a final number.

## B.3 double-source check

TeX line 5317 literally contains `\sum_{l>P^{12}/l_1}`. An `od -tc` byte
inspection confirms `{1 2}`, without a slash or nested fraction. The official
PDF page 108 was rendered and visually inspected; it also prints P^12.
`p108.png` and `p107-108.txt` preserve that check. This is a source/typesetting
fact. The support-driven replacement by P^(1/2), including its ≥ endpoint,
is a separately labeled correction from (12.1), not an alternate reading of
those bytes. `lemma151_literal_B3_support_zero` verifies that the literal P^12
cutoff already lies beyond the support of κ₁ for P≥1.

## Exact actual-zeta residue and the coefficient it permits

Put L=log P, γ=β₆ and

A(s)=exp(Lγ(.504−z)+Lzs)−exp(.004Lγ+.5Ls).

The actual Appendix B integrand is

F(s)=A(s) ζ(1+s)/ζ(1+s−β) · ω₁(s−γ) · exp(−s log l₁)/(s−γ),

with ω₁(s)=exp(s²/(4(log D)^30)). The checked local theorem establishes

lim_{s→0,s≠0} sF(s)=−A(0)ω₁(−γ)/(γ ζ(1−β)).

It uses the actual `riemannZeta` and actual pole-removed zeta, not a rational
stand-in. For β purely imaginary, zeta nonvanishing follows from the existing
closed-half-plane nonvanishing theorem; it is not an extra desired estimate.
The numerator cancels exactly at s=γ. Hence that apparent simple pole does
not supply a second main residue, provided the other factors are regular there.

Let R=zetaPoleRemoved(1−β). The exact coefficient is

(β/γ) A(0) · ω₁(−γ)/R.

When ‖R−1‖<1, the code proves the explicit quantitative bound

|exact residue−(β/γ)A(0)|
 ≤ |β/γ||A(0)| (|ω₁(−γ)−1|+|R−1|)/(1−|R−1|).

This exposes the two true local analytic errors instead of pretending that
1/ζ(1−β)=−β at finite D. The limit β_j/β₆→2j/3 and exact β₆ logP=3πi/2
then select the final Appendix B small-phase expression, if the contour and
arithmetic-to-integral passages are justified:

(j/.756)∫_.5^.504 [exp((3/2)πi(.504−z))−exp(.006πi)] dz.

An independently checked change of variable/integration by parts gives

this expression = −iπj b*,
  b*=(1/.504)∫_0^.004 t exp((3/2)πit) dt.

The printed e1j'' instead is

(j/.756)∫_0^.004 [exp((3/2)πi(.504−z))−exp(.75πi)] dz.

These are retained as distinct definitions. The printed expression does not
follow by change of variable from Appendix B's terminal residue. This identifies
a local discrepancy; it does not by itself establish the repaired full lemma.

## Genuine arithmetic results and explicit repair error

`Lemma151Arithmetic.lean` proves the exact identity

ρ* = ρ * (n↦n^β ν(n)),   ν=ζ*χ,  μ*ν=χ,

and, for Re β=0,

|ρ*(n)−ρ(n)| ≤ Σ_ab=n,b≠1 τ₂(a)|ν(b)|.

`Lemma151WeightedError.lean` proves for every finite S and actual weight w:

|Σ_{n∈S} w(n)ρ*(n)/n − Σ_{n∈S} w(n)ρ(n)/n|
 ≤ Σ_{n∈S} |w(n)|/n Σ_ab=n,b≠1 τ₂(a)|ν(b)|.

Its rough specialization retains n₁, n<X strictly, n>0 and (n,Q)=1, and takes
w(n)=b(n₁n)χ(n), using the actual source β_j. This explicit, finite ν-weighted
error is a genuine partial repair interface. It is not yet a proved scalar
uniform rate in D, and it is not defined as the error being estimated.

`Lemma151Basis.lean` proves the actual ψ-coefficient expansion, that the original
Q excludes every ramified prime (without requiring D squarefree), and the exact
χ cancellation above. Regressions expose a negative-character prime at which
ρ*=ρ but χρ*=−ρ, so omitting the basis conversion is detectably invalid.

## Minimal remaining interfaces for a full, genuinely arithmetic lemma

1. Resolve the b convention globally: preserve (15.1)'s literal target and add
   a clearly labeled ψ-basis repair, propagating it into (15.5), (15.7), (15.19),
   (15.20), (15.22) and Section 16. Do not silently rename b halfway through.
2. Split every divisor of n₁n into its Q-smooth and Q-rough components, retaining
   n₁∈N(Q), n₁<T, ramified χ(n₁)=0 behavior and all U,V strict supports.
3. Factor the rough convolution into one-kernel sums. ρ(n) is multiplicative
   only across coprime factors: collisions where a rough prime divides both
   convolution arguments need an explicit uniform error, not a product identity.
4. Apply genuine Lemma 3.2 to the **weighted** B.1 majorant above, including the
   original b/tau weights and the n₁ divisor sums; derive the numerical log powers.
5. Prove B.2 with the original q<D⁴ exclusion and transport all kernel weights.
6. Establish Mellin inversion and justified sum/integral interchange for the
   actual ζ-ratio (including the truncated κ₁ and its ≥ boundary term).
7. Complete the contour shift, zeta reciprocal/zero-region bounds, Gaussian
   truncation and smoothing errors, uniformly in l₁|n₁, n₁<T.
8. Bound the local actual-zeta error displayed above and β_j, P₂, l₁ phase shifts
   using the original fixed c′ and log T/log P, then derive an explicit scalar
   rate for a repaired theorem. α₁'s undefined original symbol remains separate.
9. Only after 1–8 may −iπj b* be promoted from its exact local/model identity to
   the coefficient of the actual arithmetic sum. Nothing here asserts the final
   Section 18 bound or refutes the main theorem.

## Validation scope

Everything is in `/tmp/lemma151`; no live repository, progress or GitHub writes.
The requested base is 58bfdd81529397bc945710d80a4fd83006fadf01. The parent checkout
advanced while work ran; all 225 transitively imported ZhangLS sources were
compared against that requested base, with **no changed imports**. The validated
checkout head and complete import closure are recorded in `import_closure.json`.
The pinned Lean 4.30 binary is invoked directly with existing LEAN_PATH entries;
no lake update, cache fetch or shared build writes occur. `build.sh` compiles
private outputs, and `Axioms.lean` checks every public declaration in the package.

## Central integration qualification

Six production modules are installed in ZhangLS/Spec with import-only relocation. Seven named semantic regressions are in the standalone CloudLemma151ArithmeticRegression.lean, followed by all69 public axiom checks. The actual local residue limit is proved under its explicitly displayed nonzero/pure-imaginary shift conditions. The local error theorem retains the actual Gaussian and pole-removed-zeta deviations and a closeness side condition; it is not a global asymptotic with that side condition silently discharged. The finite arithmetic error still contains the actual nu-weighted convolution sum; its smallness, collision estimates and uniform n1 asymptotic remain open. Central3859-job dependency and5221-job project builds PASS.
