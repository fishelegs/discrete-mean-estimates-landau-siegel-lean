# Section 8 upstream kernel and normalization audit

## Result

**The printed function tables (8.13)–(8.18) follow faithfully from the original β shifts and the actual Lemma 8.2 / Lemma 8.4 kernels. No uniquely justified correction to these tables, the π normalization, the support limits, or the conjugation orientation was found.** The previously certified literal value `c1 > 7` is therefore not explained by a mistranscription in that upstream chain. The off-diagonal *numerical evaluation* printed after the integral definitions remains the identified discrepancy.

This audit concerns the kernels, finite parameter changes, and the numerical model. It does **not** prove the full character-sum-to-integral bridge (8.11), all endpoint estimates, or (8.23). In particular it does not convert the paper's “simple approximation” into a finite-D equality.

## Source identity and exact locators

Source: arXiv:2211.02515v1, https://arxiv.org/abs/2211.02515v1 and https://arxiv.org/pdf/2211.02515v1

- TeX `/tmp/zhang-2211.02515-source.tex`, SHA256 `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`
- PDF `/tmp/zhang-2211.02515.pdf`, SHA256 `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`
- `P=exp(L^9)`: (2.6), TeX 364; `α=π/log P`: (2.10), TeX 401, PDF p.6
- Original β1,β2,β3: (2.13), TeX 469, PDF p.7
- `P1=P^.504`, `P2=P^.5 T^-10`: (2.21), TeX 576, PDF p.10
- β6,β7: (2.22), TeX 579; iota2: (2.26), TeX 593, PDF p.10
- `T=exp(L^1.1)`: TeX 1689, Section 6
- Cyclic β4=β1, β5=β2: TeX 2331–2335, PDF p.45
- F kernel: Lemma 8.2, TeX 2339–2345; its contour calculation at 2364–2365, PDF p.45
- G kernel: Lemma 8.4, TeX 2392–2398; its contour calculation at 2403–2415, PDF pp.46–47
- Mollifier sum denominators: TeX 2422–2434; integral (8.11): 2468–2470, PDF p.48
- Cross substitutions (8.12): TeX 2474–2477, PDF p.48
- Function tables (8.13)–(8.18): TeX 2488–2504, PDF p.49
- Normalized integrals (8.19)–(8.22): TeX 2529–2543, PDF pp.49–50
- c symmetrization: TeX 2555–2568; printed c12 numerical value: 2579; claimed (8.24): 2583, PDF p.50

I also rendered and visually inspected PDF pp.45–46. They agree with the TeX on both kernel formulas, cyclic companions, all signs and denominators. The preceding independent review inspected PDF pp.10,49,50.

## 1. Keep the original fixed c′ exactly

Put ε=c′αL. The exact original shifts are

- β1=iα t1, t1=1−5ε
- β2=iα t2, t2=2+2ε
- β3=iα t3, t3=3−3ε
- βμ=iα r, r=3/2 for μ=6 and r=5/2 for μ=7

The exact sum is `β1+β2+β3=2β3=6iα(1−ε)`, not `6iα` at finite D. The live source already proves this as `lemma52_beta_sum` in `ZhangLS/Spec/Lemma52Product.lean:20`.

For every fixed c′, `ε=c′π/L^8 → 0` as D→∞. No step here sets c′ to zero in the original problem, treats it as a tunable free constant, or lets it grow with D. The zero-ε expressions below are the limiting normal forms; the new Lean `eps_tendsto` proves the genuine limit for arbitrary fixed c′.

## 2. The residues force the signs in F and G

For ℓ=log x, the double pole at s=βμ in

`(s−βj) exp(sℓ)/(s−βμ)^2`

has residue `(1+(βμ−βj)ℓ) exp(βμℓ)`. This is exactly Lemma 8.2's F.

For a=β(j+1), b=β(j+2), m=βμ, the rational factor in Lemma 8.4 is exactly

`(s+a)(s+b)/(s(s+m)^2)`
`= (ab/m²)/s + (1−ab/m²)/(s+m) − ((a−m)(b−m)/m)/(s+m)^2`.

Thus its poles at 0 and −m give exactly

`G=ab/m² + (1−ab/m²−(a−m)(b−m)ℓ/m) exp(−mℓ)`.

The live `lemma84_partial_fractions` and `lemma84_model_circle_integral` in `Lemma84Residue.lean` prove those identities. `lemma84_paper_model_circle_integral` in `Lemma84PaperResidue.lean` specializes this to the actual original shifts and `lemma84MainTerm`. In particular, changing the sign of G's log term, replacing its companions by conjugates, or replacing βμ² by |βμ|² is not consistent with this residue calculation.

## 3. Exact finite-ε normalized formulas, then all six limits

Set x=P^z. Since α log P=π exactly, put q=πi and let a,b be the two cyclic t companions of tj. For every finite D with L>0:

`Fjμ(P^z) = (1+q(r−tj)z) exp(qrz)`

`Gjμ(P^z) = A+(1−A+qBz) exp(−qrz)`

where `A=ab/r²` and `B=−(a−r)(b−r)/r`.

Here are all finite-ε coefficients; these are polynomial identities, not fitted numerical parameters:

| jμ | r−tj | A | B |
|---|---|---|---|
| 16 | 1/2+5ε | 8/3−8ε²/3 | −1/2−ε+4ε² |
| 26 | −1/2−2ε | 4/3−8ε+20ε²/3 | 1/2+4ε−10ε² |
| 36 | −3/2+3ε | 8/9−32ε/9−40ε²/9 | 1/6+7ε/3+20ε²/3 |
| 17 | 3/2+5ε | 24/25−24ε²/25 | 1/10−ε+12ε²/5 |
| 27 | 1/2−2ε | 12/25−72ε/25+12ε²/5 | 3/10−4ε/5−6ε² |
| 37 | −1/2+3ε | 8/25−32ε/25−8ε²/5 | −3/10+ε/5+4ε² |

At ε=0 these give precisely all twelve printed f/g functions, including the potentially suspicious `+πiz/6` in g36 and `−3πiz/10` in g37. Both are required by the upstream residue formula.

The approximation is uniform for z∈[0,1]: since |exp(±qrz)|=1,

- `|Fε−F0| ≤ 5π|ε|`
- `|Gε−G0| ≤ (16+4π)|ε| + (40/3+10π)ε²`

Thus, for fixed c′, the displayed `O(L^-8)` table approximation is consistent. These explicit uniform error bounds are elementary consequences of the coefficient table (not separately Lean-certified in this package). The package does formally certify all exact finite-D kernel identities, table identifications, and pointwise D→∞ limits.

## 4. Supports, denominators, and argument shifts

Put `δ=10 log T/log P = 10/L^(79/10)` exactly, so δ→0 and α log T=πδ/10→0. Then the *finite-D* geometric parameters are

- `a=log P1/log P=63/125=.504`
- `b=log P2/log P=1/2−δ`
- `d=log(P1/P2)/log P=1/250+δ`
- `a=b+d`

After x=P^z, `dx/x=(log P)dz`. For example, the finite-D cross term normalized by 1/α is

`1/(a b π) ∫[0,b] Fε,j7(z) Gε,j6(z+d) dz`.

The other cross term is

`1/(a b π) ∫[0,b] Fε,j6(z+d) Gε,j7(z) dz`.

The diagonal terms have denominators `a²π`, `b²π` and endpoints a,b, respectively. Consequently the limiting endpoints, denominators and shifts are *exactly* the printed .504, .5, and +.004, respectively. The + sign is forced by P1/P2>1.

The factor π comes from `1/(α log P)=1/π`, not `1/(2π)` or `2/π`. The weights `(1/2,2,3/2)` come from Proposition 7.1 / the residue computations at TeX 2170–2176. The separate doubling occurs only when (8.7) takes `2 Re Theta1`.

On compact z ranges the finite-ε kernel family and its z derivatives stay bounded for ε small. The denominator b stays away from zero. Hence replacing b,d by .5,.004 changes these normalized integrals by O(δ), and the kernel replacement contributes O_c′(L^-8). Before multiplying by 1/α this is o(α), as claimed. Note that δ=O(L^-7.9), not O(L^-8); no stronger T-error rate is being silently asserted.

This argument only concerns the already-defined integral kernels. Applying Lemmas 8.2/8.4 to the actual sums is restricted to dr<Pμ/T, and the strips Pμ/T≤dr<Pμ cannot be replaced pointwise by those asymptotic formulas. The live `Lemma84Section8Objects.lean` correctly retains this exact boundary residual. An independent boundary analysis is still necessary in the full proof; it cannot justify changing a leading constant by an arbitrary fixed amount.

## 5. Cross terms and conjugation are forced

For the two mollifiers, the exact product is

`(F6+iota2 F7)(G6+conj(iota2)G7)`
`=F6 G6+iota2 F7 G6+conj(iota2)F6 G7+|iota2|² F7 G7`.

Therefore the coefficient before symmetrization is

`v=b11+iota2 b21+conj(iota2)b12+|iota2|² b22`.

Then `v+conj(v)` forces

- c11=b11+conj(b11)
- c22=b22+conj(b22)
- c12=b12+conj(b21)
- c21=b21+conj(b12)=conj(c12)
- c1=c11+iota2 c21+conj(iota2)c12+|iota2|²c22

This matches both the paper and `Section8NumericalObjects.lean`. Swapping b12/b21, swapping c12/c21 without the matching coefficients, conjugating iota2, or dropping the shift in one cross factor would change the requested source problem.

## 6. What the audit does and does not correct

The certified literal obstruction gives `c1>7`. Independent prior quadrature gives c11≈3.6122616014, c22≈1.3221492640, and

`c12≈−0.457471578721370236−0.201383435433634884 i`,

hence `c1≈7.050104669792050420`. The printed off-diagonal approximation instead reads `−0.45757−0.18179i`. Both its real and imaginary parts lie outside the claimed error; the imaginary discrepancy is the dominant one. The two printed diagonal values agree with direct evaluation.

The justified correction is to the reported numerical evaluation, not a uniquely reconstructible alternate kernel or parameter. Neither fixed-c′ perturbations nor the T^-10 cutoff correction alter the limiting c1. No original-formula correction to rescue a downstream Q has been established by this audit; any alternate parameter choice would be a new analytic argument requiring separate authorization and verification.

Several clear prose/cross-reference typos are harmless here: TeX 2428 says Lemma 8.3 where 8.4 is used; TeX 2522 says “inserting these into (8.13)” where the integral relation (8.12) is intended. Such citation corrections do not alter any f/g coefficient or integral.

## 7. New bounded Lean package and scope

All new files are in `/tmp/section8-upstream-audit`. No live repository, P14/P71 file, shared cache, or GitHub state was edited.

- `Upstream.lean`: exact scaled original shifts, exact finite-D F/G normalization, G scaling, all twelve table identities
- `Limits.lean`: ε→0 for fixed arbitrary c′, continuity of the kernel normal forms, actual finite-D kernels tending to those normal forms
- `Geometry.lean`: δ→0 and α log T→0, exact log P1/P, log P2/P and log(P1/P2)/P identities, π normalization, cross expansion/symmetrization
- `check.sh`: direct Lean 4.30.0 invocation; all .olean outputs are local to this new directory, imported live dependency artifacts are read-only
- `derive_coefficients.py`, `coefficients.txt`: independent exact SymPy polynomial table, diagnostic only

The checks import genuine `lemma82MainTerm`, `lemma84MainTerm`, original β definitions, original P/T/P1/P2 definitions and the existing literal numerical tables. They do not introduce replacement character sums or change any upstream object. The source permits all c∈R in the algebraic identities and limit statements, which is stronger than the required fixed positive c′. Only μ=6,7 are interpreted as source rows.

No `sorry`, custom axiom, result-shaped assumption, `notA` theorem, unsafe evaluator, or numerical oracle is used. The final audit checks all 30 new lemma declarations and the existing exact paper contour theorem. Their axiom lists are standard `[propext, Classical.choice, Quot.sound]` only. This is a focused replay against the existing compiled dependencies, not a fresh rebuild of the entire imported project.

## Central repository integration

The three production modules are installed as Section8UpstreamKernels, Section8UpstreamLimits and Section8UpstreamGeometry in ZhangLS/Spec. Only local import paths changed. All36 public definitions/lemmas and the existing actual contour theorem were centrally axiom-checked;4 extra regressions and5215-job whole-project build pass. Pointwise limits and exact finite-D identities are Lean-certified. Uniform integral convergence and the complete character-sum-to-model passage remain separate obligations; the elementary uniform estimates discussed above are not silently upgraded to kernel-certified statements. The actual second-factor boundary replacement is now separately verified in CLOUD_LEMMA84_BOUNDARY_STATUS.md, but first-factor/8.10/8.11 obligations still remain.
