# 全阶对数 Padé 行列式与 1−i 有理归一化

本轮完成题设**有限和多项式族**的全阶精确相邻行列式，并完成 `1−i` 处
两项归一化的有理性及相邻实行列式非零。递推呈现与有限和呈现的一致性
已经在 Lean 中对所有阶数证明，最终结果没有假设尚未证明的识别引理。
有限阶算例仅是回归，不代替全阶定理。

## 原始有限和定义

所有主声明在 `PiWeightedColon`。多项式系数域是 `ℚ`。记

```text
C_r = binom(2r,r),    H_n = sum_{k=1}^n 1/k,
pCoeff(r,j) = (-1)^j binom(r,j) binom(2r-j,r) / C_r,
lCoeff(r,j) = -2 pCoeff(r,j) (H_r-H_(r-j)).
P_r = sum_{j=0}^r pCoeff(r,j) x^j,
L_r = sum_{j=0}^r lCoeff(r,j) x^j.
```

这些定义对应 `logPadePCoeff`、`logPadeLCoeff`、`logPadeP` 和 `logPadeL`。
`harmonic` 使用固定 Mathlib 的有限有理和定义。`C_r` 始终非零。
对 `j>r`，系数由 `binom(r,j)=0` 消失，所以 Lean 的自然数截断减法不会
在支持范围外制造额外项。

精确全阶主声明为：

```lean
theorem logPade_adjacent_determinant (r : ℕ) :
  logPadeP r * logPadeL (r + 1) - logPadeP (r + 1) * logPadeL r =
    Polynomial.C (logPadeD r) * Polynomial.X ^ (2 * r + 1)
```

其中 `logPadeD r = (r!)^4 / ((2r)!(2r+1)!) : ℚ`。
`logPadeD_pos` 证明该常数对所有 `r` 为正；`logPade_adjacent_ne_zero`
证明整个相邻行列式多项式非零。

## 证明路线与识别步骤

三项递推采用无负自然数下标的形式：

```text
β_r = (r+1)^2 / [4(2r+1)(2r+3)],
F_(r+2) = (1-x/2)F_(r+1) - β_r x² F_r,
P_0=1, P_1=1-x/2, L_0=0, L_1=x.
```

`LogPadeRecurrence.lean` 定义递推族，证明相邻行列式递推
`W_(r+1)=β_r x² W_r`、`W_0=x`，以及精确阶乘常数递推
`d_(r+1)=β_r d_r`，得到递推族的全阶恒等式。

`LogPadeCoefficients.lean` 定义题设有限和，证明其实际系数、支持范围和
零次／一次系数。`LogPadeCoefficientRecurrence.lean` 将二项式系数转成
有理阶乘比，逐系数证明同一递推：内层用自由自然数指标消除截断减法；
最高次边界单独证明；支持范围外的项为零。分子直接使用
`harmonic_succ` 展开差值，也对全部指标及边界完成证明。

`LogPadeFiniteIdentity.lean` 先用多项式逐系数相等得到有限和的三项递推，
再通过两步归纳证明

```lean
logPade_finite_eq_recurrence (r : ℕ) :
  logPadeP r = logPadeRecP r ∧ logPadeL r = logPadeRecL r
```

最终 `logPade_adjacent_determinant` 使用已证明的识别结果转回原有限和族。
本轮无需参数微分、形式幂级数或复积分。

## 实际 1−i 归一化

`logPadeNormalizedQ` 和 `logPadeNormalizedP` 定义为

```text
q_r = P_r(1-i)/(1+i)^r,
p_r = 2i L_r(1-i)/(1+i)^r.
```

Lean 证明 `1+i≠0`，并利用
`1-(1-i)/2=(1+i)/2`、`(1-i)²=-(1+i)²` 把多项式递推变成有理递推：

```text
(q_0,p_0)=(1,0), (q_1,p_1)=(1/2,2),
q_(r+2)=q_(r+1)/2+β_r q_r,
p_(r+2)=p_(r+1)/2+β_r p_r.
```

`logPadeNormalizedQ_eq`、`logPadeNormalizedP_eq` 将**实际有限和**的复数
归一化值识别为该有理递推值的嵌入。`logPadeNormalizedQ_rational`、
`logPadeNormalizedP_rational` 分别给出 `∃ a : ℚ, value=(a:ℂ)`。
随后证明精确有理、复数及实数行列式

```text
q_r p_(r+1)-q_(r+1) p_r = 2(-1)^r d_r ≠ 0.
```

关键声明是 `logPadeNormalized_adjacent_determinant`、
`logPadeNormalized_adjacent_ne_zero`、`logPade_real_adjacent_determinant`
及 `logPade_real_adjacent_ne_zero`。本轮没有另行形式化每个 `q_r>0`。

## 验证和保存范围

新增五个证明模块、一个回归模块、一个完整类型／公理审计模块和五个预期
失败模块。新增全部 **87** 个具名定义和定理均审计。累计重放为 **93** 项
编译检查、**622** 个具名声明：28 个本地证明模块、6 个原始 A7 模块、
13 个回归模块、14 个审计模块、32 个预期失败。

正向回归检查精确全称类型、全部阶数的有限和识别、有理性与独立性，以及
小阶多项式和前四对 `(1,0),(1/2,2),(1/3,1),(1/5,19/30)`。
预期失败检查错误的幂指数、归一化行列式的交替符号、遗漏因子 2、
错误分子尺度及遗漏 `(1+i)^r`。每项必须只有目标错误、编译退出码为 1，
且没有 `.olean`。小阶数测试没有被当作全阶证明。

仅允许标准公理 `propext`、`Classical.choice`、`Quot.sound`，禁止 `sorry`、
`admit`、`native_decide`、自定义公理及 `unsafe`，警告作为错误。
保持 Lean 4.30.0、Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`
及全部九个依赖 pins，不引入外部依赖，也不更改既有 A7／√2 证明。
原 A7 回执继续保留；√2 阶段累计回执另存为
`verification/sqrt-two-replay-receipt.json`，其 SHA-256 为
`d0ece6537576e461acac8c772e5b191e133fd8eecfb9c42272969be818381531`。
独立 W2 记录不改动。`APPROXIMATION.md` 中的 535／81 是该 √2 阶段的计数；
新增后累计计数以本说明和当前重放回执为准。

从仓库根目录执行：

```sh
python3 pi-weighted-colon/scripts/replay.py \
  --lean /Users/keyishen/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean \
  --existing-mathlib-project /Users/keyishen/Documents/Codex/2026-10-08/task/pi-a7-mathlib-project \
  --out /tmp/pi-log-pade-replay
```

精确源码和输入依赖哈希、编译命令、退出码及递归公理集合保存在
`verification/source-hashes.json`、`verification/dependency-attestation.json`
和 `verification/replay-receipt.json`。`verification/LogPadeAudit.log`
保留所有新增声明的精确类型和公理输出。

## π 的应用与尚未形式化的定量层

背景是 [Calegari–Dimitrov–Tang §3](https://math.uchicago.edu/~fcale/papers/ICM.pdf)
讨论的对数与二项式超几何 Padé 构造。本轮的 Lean 定理验证了题设经典族
在 `1−i` 处的有理结构和相邻独立性。它没有引入或证明下列步骤：一般
二项式参数行列式、参数微分关系、形式对数余项消失阶、复对数分支、复
积分、`p_r/q_r` 收敛到 π、清分母后的整数误差、Baker 的 2.955 下界，
或 π 的坏逼近性。相邻独立性尚不足以满足此前全尺度近似对判据的误差和
分母增长条件。

以下为上游独立数学复核提供的**纸面补充，未在 Lean 中证明**：

```text
π-p_r/q_r ~ (-1)^r [4π/(1+√2)] (1+√2)^(-2r).
M'_r = 2^floor(r/2) binom(2r,r) lcm(1,...,r)
```

该指定清分母方案虽改善了 `2^r` 的因子，使用素数定理后，其实际整数
线性误差的 r 次根仍趋于 `√2 e/(1+√2)>1`。因此本次结构验证不能写成
已经取得有效 π 无理性度量或 BA 的定量进展。进一步约分或改变构造仍
有空间，这不是对所有方法的不可能性断言。
