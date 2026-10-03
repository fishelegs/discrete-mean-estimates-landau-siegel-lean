# Independent source-semantic review of original Proposition 2.6

Verdict: **ACCEPT** for the original target and the same-compatible-c actual BV/J-defect package. This review checked the original TeX, all final proof sources and frozen verification records; the separate central verification subsequently rebuilt every new module and the full repository. The review does not certify a strict gain or the original main theorem.

Original complete review SHA256: `069b7437565ebd45f09cf20381e81d1da2cfa00a87e78269f4d9a0e0f76eaa8f`. Original frozen proof manifest: `7f24e67e7c83223e909a2357b6f84cfcd44783b4bc93846e9762a3f4f9d8799d`. Original public-candidate manifest: `3869201631e745c8777c3c5c0cb77be1700d8e4cf69c280569d078cabfc12969`.

The independently checked inventory is 32 production modules/422 actual owned declarations plus one expanded-regression module/15 declarations; all 437 use only the three standard axioms. The 294 source-declared public declarations match this inventory. The regression module is now named `ZhangLS.Spec.Proposition26Regressions`; declaration names and proof body are unchanged.

## 原文及 notation 边界

原始研究源为 arXiv:2211.02515v1。直接读取本地原 TeX，SHA-256 为 `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`。本报告没有拷贝或发布全文。候选作者记录的 PDF SHA 为 `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`；本审查没有重新读取该 PDF，因此不把其 hash 当作本次独立 PDF 验证。

独立 TeX 检查确认：

- 原 (2.20) 的对象是 `Σψ∈Ψ1 Σρ∈Z(ψ) C*(ρ,ψ) |J1−Z(ρ,χψ) conj J2| |H2| ω(ρ)`
- (2.21)–(2.30) 指定实际 P₂/P₃、β₆/β₇、iota 常数、tent 和 J₂ 的平移
- Section 8 的最后编号为 (8.24)，原 TeX 无 `eqno(8.25)` 或 `eqno(8.26)`，Section 11/12 却引用两者。这是缺失交叉引用，不足以单独断言所需不等式为假
- 单变量 `tilde Z(ψ)` 零集合未定义；本实现沿用既有澄清，读作原 (2.14) 的 `Z(ψ)`。这不应与原 Section 4 的双变量 `tilde Z(s,ψ)=Z(s,ψ)Z(s,χψ)` 混同。此处使用的是原 χψ functional-equation factor

## Literal 对象对照

主要定义在 `Proposition26OriginalObjects.lean`，原零窗口在 `Lemma81FiniteZerosReflection.lean`，actual coefficient/weight 桥在 `Proposition26EnergyObjects.lean`。

- `lemma81GoodFamily χ` 是原 Ψ₁；`lemma81ZeroFinset D ψ` 是实际 `L(s,ψ)=0` 与 strict 窗口 `|Re ρ−1/2|<1/2`、`|Im ρ−center|<L^405` 的有限集合，不是 product zeros 或模型 zeros
- `proposition26Weight` 定义为实际 C* 的实部乘 critical-line Gaussian。`proposition26_actual_weight_data` 用原 Proposition 2.2 和 compatible L2.3 数据，在同一充分大 D 阈值下证明 ρ 位于 critical line、weight 非负、实际复数 `C*ω` 恰等于其嵌入
- `proposition26_original_Xi3_complex_identity` 把实数 Xi3 定义逐项接回 literal 复数原和。因此没有把 `Re C*` 当作未经证明的代理权重
- H₂ 精确保留 `conj(iota3) H13 + conj(iota4) H12`；iota3 = −1.00635−0.22789i，iota4 = −0.68738+1.60688i。P₃=P^0.498、P₂=P^0.5 T⁻¹⁰。两个 H-component 分别调用 β₆=3iα/2、β₇=5iα/2，且保留 `(X/n)^β` 和 strict `n<X`
- J₁/J₂ 使用真实 `χ(n)ψ(n)`、正指标 LSeries convention 和原 tent。J₂ 平移是 `1/250−log(D t₀)/log P`，不是仅保留 0.004 或改成近似平移
- `proposition26_original_tent_two_coordinate` 与 `lemma111_tent_error_two_original_coordinate` 精确证明 `log(n/(D L^519))/logP+1/250` 与上述 J₂ 原坐标相同
- 原 J-defect 的 `Z` 属于 `χψ`（modulus `D*p`），不是 ψ。real profile conjugation 给出 `J₂(1−ρ,ψ⁻¹)=conj(J₂(ρ,ψ))`；actual twisted Z 在 critical line 的模等于一由真实 primitive character 数据推出
- target 中的 `a` 为 `(6/π²)L'(1,χ)² ∏q|D q/(q+1)`，`M` 为实际 strict interval `P<p<P(1+L⁻⁶⁸)` 中 primes 的和。原 χ、Normalized (A)、所有 genuine square-root branches 均保留

## 实际范数依赖链

### 1. χ cancellation 与 finite Abel

`Proposition26ChiHarmonic.lean` 的 uniform χ harmonic theorem 没有 (A) 或任何 mean 假设。对 `Re s=1`、`‖s‖≤D`，`x≤D²` 时直接用 harmonic majorant；`x>D²` 时使用真实 continued L-function 的 `O(log D)` 上界与 periodic-character truncation error，其尾部 `x⁻¹ D(‖s‖+1)≤2`。系数为实际 χ，因而上界 `H=(14 exp16+2)L` 同时覆盖所有 finite cutoffs。

complex Abel 公式的成本恰是末端绝对值加 successive variation。`Proposition26VariationBound` 要求所有正数 multiplicative samples `q(n+1)`，而非仅 q=1。`ProfileBV` 提取 χ(q) 和纯相位，再调用原 χ harmonic theorem。`ArithmeticInner` 通过严格支持把原 indices 精确扩张到 `Icc 1 floor(P)`，遗漏项由 a(qn)=0 消失。

first inner sum 的参数是 `1−β_j+i v`；second inner sum 对 conjugate sequence 使用 `−v`、`conj(w)`，参数 `1−i v`。`ParameterBudget` 证明 `L²⁰+4≤D` eventually，并用原 small-shift bound 控制 β；不存在把增长的 frequency uniformity 作为未证明前提的步骤。

### 2. 真正 finite-β μ*ξ，含 ramified p=2

`lemma83XiMoebius := μ * lemma83XiArithmetic`，并用 arithmetic-function Möbius inversion 得到实际 ξ=1*b。`ConvolutionBV` 在取绝对值前完成正数 divisor-antidiagonal 的 finite reindex，得到 second inner bound `H V Σk≤floorP |b(k)|/k`，χ(dr) 仍在外侧。

冻结 ξ 输入实际证明三个 zero-shift local cases：p|r 时 ξ(p^k)=k+1；p|d 且 p∤r 时 `1−k/(p−1)`；p∤dr 时 1。由此 μ*ξ 的 local harmonic factors 分别为 `p/(p−1)`、`1+1/(p−1)²`、1。p=2 没有排除；尤其 d-only 情况 ξ(2)=0，并不做任何除以这个可能为零的 numerator 的相对估计。

非零 β 使用 additive prime-power perturbations，`Σi |p^(−β_i)−1|≤3 b log p`。有限 Euler product 仅在 p≤N 上进行；all powers of these finitely many primes 的绝对可和已独立证明。没有主张非零 β 在所有 primes 上的 Re=1 绝对收敛。原 `b≤3α`、`α logP=π` 给出固定常数：

`Σn≤N |μ*ξ(n)|/n ≤ exp(8+842400000 π log4) r/φ(r)`，`N≤P`

该 pointwise theorem 不限制 dr；这点对实际 double box 很重要。Lambda 的另一条接口本来仅覆盖 m≤P，但汇合没有误用它：`proposition26_actual_lambda_uniform` 单独用 general finite-shift Lambda bound 和 `log(dr)≤2 logP`，所以覆盖实际 d,r<P 的 dr<P² box。

### 3. r/φ 与两个原 inner sums

原 S_j 在 `Proposition71Objects.lean` 包含 `|μ(r)| Λ(dr,1−β_j)/(dr φ(r))`、真实 first/second inner sums 和实际 ξ。`ArithmeticBV` 先保留两边 χ(dr)，再显式用 `‖χ(dr)‖≤1`；`|μ(r)|≤1` 也显式证明。这里是合理的 coarse 上界，不是假装得到 φ(D)/D 的主项。

外层乘积精确成为：

`[K/(d r φ(r))] · HV · [HV · Q r/φ(r)] = KQ(HV)²/[d φ(r)²]`

`OuterWeight` 证明 `Σ φ(r)⁻²` 真正收敛，经过 `φ(r)⁻¹≤τ₂(r)/r`、`τ₂²≤τ₄` 以及 τ₄ 的真实 s=2 Dirichlet series。d-sum 只损失 `1+log floorP≤2L⁹`。因此三项 S_j 均为 `O(V² L¹¹)`。

### 4. 原 P7.1 + L8.1，实际 prime mass

`proposition26_polynomial_energy_arithmetic` 从 `lemma81_proved` 取 compatible c，并在同 c 上使用 `proposition71_at_every_positive_constant`。实际 energy 等于原 discrete mean 的实部。得到：

`Energy(a) ≤ M [(4/α+C L²) Σj |S_j(a,conj a)| + ε]`

C 在 ε 和 a 之前固定；D₀ 在 χ、a、branch 之前固定。UniformEnergy 对固定 V 取 ε=1 后应用三项 S_j bound，由 `α⁻¹=L⁹/π` 得到 `Energy≤K M L²⁰`。

没有在这条链上使用原 fourth-moment `P² L³⁶` 再把 P² 当 M；所有能量从原 P7.1/L8.1 outset 就乘 actual M，因此不存在漏付 L⁷⁷。Lemma5.9 的 quotient estimate 也没有被误称为 `C*≤α²|F|²`。

## smoothing、H₂ 和最终指数

1. `Lemma111PrimitiveVariation` 把真实 primitive error 分成 monotone / antitone pieces，得 BV≤8/L²⁴；真实 tent 是其二阶差分，因此两种实际 error 的 BV≤16000/L²⁴
2. strict cutoff 会把最后端点替换为 terminal jump，保持所用的 last-endpoint BV 常数。`Proposition26GaussianProfiles` 定义 `L²⁴ * error * 1_(n<P^.505)`，故 V=16000 为固定数，不依赖 D
3. 支持 `P^.505≤PT⁻²` 已证明。`GaussianPolynomialBridge` 给出精确 `Jμ−Jtildeμ = L⁻²⁴ A(normalizedProfileμ) + actualTailμ`
4. tail 是 finite Gaussian sum minus full actual Jtilde，不是以一个任意 tail-bound premise 代替无限级数。其界 `2(Σn n⁻²)exp(−L¹⁰)` 由真正 summability 和 pointwise Gaussian tail 导出；constant-one χ-twisted polynomial 的 energy 从同一个 BV norm 控制
5. 先把固定 normalized profile 代入 mean theorem，再用 energy 二次齐次性还原 `L⁻⁴⁸`。得到每一 unsmoothing energy `O(M L^(20−48))=O(M L⁻²⁸)`。因此没有未归一化 mean 的 arbitrary o(M) 残项问题
6. 原 E₂ 是 `L⁻⁶⁸ ∫ |actualShortPolynomial(s+iv)| exp(−v²/(4L³⁰))dv`。exact full Gaussian mass 为 `2√π L¹⁵`。weighted integral Cauchy 将平方变成 `2√π L⁻¹²¹ ∫ |short|² gaussian`，再积分 actual `O(M L²⁰)` 界再付一次 L¹⁵，所以 smoothed energy `O(M L⁻⁸⁶)`
7. H-component 的 `(X/n)^β` 精确分成 unit scalar `X^β` 及 frequency `Im β`。余下 linear log ramp 非负递减，multiplicative sample BV≤1；P₂/P₃ 与 iota 保留。得到 H₂ energy `O(M L²⁰)`
8. critical-line conjugation 和 actual χψ Z 的 unit norm 给实际三缺陷分解。总 J-defect energy `O(M L⁻²⁸)`。原 weighted Cauchy 得 `Xi3²≤O(M² L⁻⁸)`，所以 `Xi3=O(M L⁻⁴)`
9. `lemma171_actual_main_gt_half` 用真正非负 harmonic source sum 的 n=1 项和已证明 Lemma17.1 得 a>1/2。它的 project import closure 没有 P2.6，故无此处的依赖环。最终把 `K L⁻⁴≤ε/2` 的阈值统一提前，得到原 `Xi3=o(a M)`

## 量词和非空性

- 总存在的 c 在所有 V、ε、χ、profile、branches 前；norm 的 K/N 可依赖固定 V；原 target 的 N 仅依赖 ε 和先前固定常量
- original target 保留 NormalizedAssumptionA χ，不把 A 从全局 contradiction 消除。未要求证明存在满足 A 的 χ，也没有用不存在这样的 χ 来清空 theorem
- compatible branch 是真实 square-root branch，forall genuine branch 范围保留。positivity 来自已完成 L2.3 compatibility
- real target 通过 literal complex sum identity 与原 (2.20) 相连，不依赖把 weight positivity/critical line 当最终 theorem 的额外前提

