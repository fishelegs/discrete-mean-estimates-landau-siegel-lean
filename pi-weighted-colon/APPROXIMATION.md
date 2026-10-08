# √2 基准与可复用的近似对判据

这一步是为 π 研究准备经过 Lean 检查的工具与正面基准。它证明 √2 的明确
二次逼近下界，并实现一个足够推出坏逼近性的全尺度近似对接口。
**没有构造 π 的该接口，也没有证明 π 坏逼近。** 原有 A7 六个归属明确的
超越性源文件、π 点态非零证明、依赖版本及独立 W2 回执保持不变。

## 精确声明

所有声明位于 `PiWeightedColon`。`ApproximationLowerBound α κ` 定义为

```lean
∀ p q : ℤ, 0 < q → κ / (q : ℝ)^2 ≤ |α - (p : ℝ) / (q : ℝ)|
```

分子允许负数；分母是正整数；不要求分子分母互素。

- `sqrt_two_integer_rational_bound`：对上述所有 `p,q`，
  `1 / (4 * (q : ℝ)^2) ≤ |Real.sqrt 2 - (p : ℝ)/(q : ℝ)|`。
- `approximation_pairs_positive_lower_bound`：当 `C>0`、`0≤η<1` 且
  `HasApproximationPairs α C η` 时，证明 `(1-η)/C>0` 和以该常数为 `κ`
  的 `ApproximationLowerBound`。
- `sqrt_two_has_approximation_pairs`：实际构造
  `HasApproximationPairs (Real.sqrt 2) 9 (1/2)`。
- `sqrt_two_pair_lower_bound`：通过通用判据导出
  `ApproximationLowerBound (Real.sqrt 2) (1/18)`。
  此下界弱于直接的 `1/4`，用途是检验构造与判据的整条接口。

`HasApproximationPairs α C η` 的量词是**每个正整数尺度** `Q`，在该尺度
存在整数 `a,b,c,d`，满足

```text
1 ≤ b,d ≤ C Q
ad-bc ≠ 0
|bα-a| ≤ η/Q,  |dα-c| ≤ η/Q.
```

它不是只给某个尺度的近似，也不是只要求两个有理数不相等而遗漏整数行列式。

## 判据证明与常数核对

固定目标 `p/q` 后，选尺度 `Q=q`。若 `bp-aq` 与 `dp-cq` 都是零，则
`q(ad-bc)=b(dp-cq)-d(bp-aq)=0`，与 `q>0`、`ad-bc≠0` 矛盾。因此至少一个
交叉差是非零整数，绝对值至少为一。以第一个为例，三角不等式给出

```text
1 ≤ |bp-aq|
  ≤ q|bα-a| + b|qα-p|
  ≤ η + C q² |α-p/q|.
```

除以正数 `Cq²` 得到常数 `(1-η)/C`。严格的 `η<1` 保证常数为正。
单个近似的代数不等式本身不需要 `η≥0` 或 `η<1`；完整判据保留题设
`0≤η<1`，另行证明正性，没有将未使用的参数当作额外证明。

√2 的直接证明利用非零整数 `p²-2q²` 的绝对值至少为一。
非零性来自固定 Mathlib 中已经证明的 `irrational_sqrt_two`。
若逼近误差至少 `1/4`，则由 `q≥1` 得结论；否则
`|p/q+√2|≤4`，结合二次范数的因式分解即可得 `1/(4q²)`。
这没有使用新的超越性假设、定制公理或未证明的 π 性质。

## Pell 构造的全尺度性

`sqrtTwoPellPair` 定义 `(P₀,Q₀)=(1,1)`，
`(Pₙ₊₁,Qₙ₊₁)=(Pₙ+2Qₙ,Pₙ+Qₙ)`。Lean 证明：

```text
1 ≤ Qₙ ≤ Pₙ ≤ 2Qₙ,  n+1 ≤ Qₙ,
Qₙ < Qₙ₊₁ ≤ 3Qₙ,
Pₙ²-2Qₙ² = (-1)^(n+1),
PₙQₙ₊₁-QₙPₙ₊₁ ≠ 0,
|Qₙ√2-Pₙ| ≤ 1/(2Qₙ).
```

给定正整数尺度 `M`，取第一个 `Qₙ≥M`。若 `n=0`，则 `M=1`；否则
`Qₙ₋₁<M`，所以 `Qₙ≤3M`、`Qₙ₊₁≤9M`。
两项分母均至少为 `M`，两项误差均不超过 `1/(2M)`。
相邻项独立性由 Pell 范数保证。这一最小指标选择在 Lean 中通过 `Nat.find`
实现，并明确把正整数 `Q : ℤ` 转为自然数尺度后转回。

## 回归、公理与重放

`ApproximationPairsRegression.lean` 包含精确全称类型检查、非互素及负分子
实例、Pell 前四项 `(1,1),(3,2),(7,5),(17,12)`、首个行列式 `-1`，以及
必要性反例：`α=0,C=1,η=0` 对每个正整数尺度可选两次 `0/1`，满足除独立性
之外的全部条件，但 `α=0` 不可能有任何正的 `ApproximationLowerBound`。
这在 Lean 中证明了删去独立性会使判据为假。

五个预期失败文件分别检查：删去独立性、`q=0`、`η=1` 却声称常数为正、
用误差条件代替分母增长条件、只提供尺度 `Q=1` 的近似对。
其中后两项是接口类型回归，未声称是数学反例。

`ApproximationPairsAudit.lean` 对新增的全部 **43** 个具名定义和定理输出
精确类型及递归公理集。累计重放检查 **535** 个具名声明和 **81** 项编译：
23 个本地证明模块、6 个原始 A7 模块、12 个回归模块、13 个审计模块和
27 个预期失败。所有预期失败须只有目标错误且没有生成 `.olean`。
仅允许 `propext`、`Classical.choice`、`Quot.sound`；禁止 `sorry`、`admit`、
`native_decide`、自定义公理及 `unsafe`，并把警告作为错误。

从仓库根目录重放：

```sh
python3 pi-weighted-colon/scripts/replay.py \
  --lean /Users/keyishen/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean \
  --existing-mathlib-project /Users/keyishen/Documents/Codex/2026-10-08/task/pi-a7-mathlib-project \
  --out /tmp/pi-sqrt-two-replay
```

使用原有 Lean 4.30.0、Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`
及原有九个包版本，不增加外部依赖。完整命令、源码和日志哈希、公理集合在
`verification/replay-receipt.json`；新增审计输出在
`verification/ApproximationPairsAudit.log`。此前 A7 的原始累计回执另存为
`verification/a7-replay-receipt.json`，SHA-256 为
`c37045a98ce1bd9efc3389ff548a7d5f75824f77262e4bd2e03eb5353f474dce`。

π 仍然只有已经证明的代数点态非零结果；独立 W2 的无理性指数结论并不
自动给出二次逼近的统一正下界。本次没有形式化 e 的负面基准，没有修改
W2，也没有声称整个包含仓库的默认 Lake 构建通过。
