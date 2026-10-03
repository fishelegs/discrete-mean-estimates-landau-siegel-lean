# Corrected joint phase：有限正质量桥已在 source 层闭合

2026-10-03。经独立来源复核；尚非Lean证明。保留原 (A) 的 −2022 和最终目标 −2024。

## 新的明确结果

在 q≥P=exp((log D)⁹) 的 primitive even character family 中，取原 literal M、辅助短多项式 S_X=Σₙ≤D²⁰ ν(n)χ(n)/√n，令 U=rM/conj M（仅在 M≠0 定义）。[PROOF.md](PROOF.md) 给出完整参数和误差：

\[
\mathbb P_+(M\ne0,\ |1+U|\le2h)
\le\frac{1+21\delta}{22-3542h^2},
\quad\delta=O(L^{-1399/84}),\quad0\le h<1/\sqrt{161}.
\]

并独立证明 P₊(M=0)=O(L⁻¹⁹⁷⁹ᐟ²)。因此 h=L⁻¹ 时，至少 21/22−O(L⁻²) 的 family 质量离开正确相位的抵消区。这是实际正质量估计，尚不是 almost-all / o(1) 反集中。

## 关键机制

精确逆卷积 υ*ν=δ 让 M₀S_X−1 的系数在 n≤X 消失；n>X 的双 cutoff 系数逐项受 2(ν_{>D⁴,≤X}*ν_{≤X}) 控制。原已证 ν² 尾给出

\[
\|M_0S_X-1\|_{2j}\le2c_q^{1/(2j)}T^{1/4}H_X^{4j^2+4j}
\quad(1\le j\le11).
\]

20 与 22 阶插值到 21 阶，误差为 O(L⁻¹³⁹⁹ᐟ⁸⁴)。D∤a 删除也完整处理：D 非平方自由时删除项恒零；D 平方自由时精确抽出 D⁻¹ᐟ² χ(D)μ(D)，无需 τ(D) 损失。

令 Tχ=Mχ conj(S_Xχ)，则 rχTχ=Uχ conj(MχS_Xχ)，在 M=0 上将 U 任取单位数仍成立。故前 21 个 U 矩由全族逆误差控制；Tᵏ 的全谱 ℓ¹≤(4D²⁰H_X²)ᵏ，CM 的 twisted root bound 为 2q⁻ᵏ/(q−3)+4k c_q q⁻¹ᐟ²，所有单位、principal subtraction、± alias 和长度均已支付。最后用 21 阶 Fejér 核得到 21/22 正质量。

没有使用 annulus 上的多项式逼近，没有把小概率尾乘上爆炸 supremum，也没有让逼近阶或矩阶随 D 增长。

## 固定高度与未闭接口

此 phase 桥对每个共同固定实 t 完全 uniform：M(t)、S_X(t) 的 n⁻ⁱᵗ 不改所有 coefficient / norm / ℓ¹ 预算；共同的 unit conductor–Γ phase 也不改 twisted root bound。完整式在 PROOF §10。

仍然没有：

1. q≈P 下完整 BPZ 同侧 B 第二矩定理；现有 Y 截尾修订仍只是其中局部进展
2. o(1) 正确 joint-phase 反集中；前 21 矩本身最多排除到 1/22，22 次单位根上的均匀分布证明这一有限信息的限制
3. 原 BPZ Mellin 分支的实际零点误差及独立 signed Z2；后续报告只闭合指定源对称分支的正误差采样，不能将共同固定 t 的 signed 矩直接替成 t(χ)=Imρ
4. 新 R4 strict-gain 方向；后续独立复核已确认该 corrected trial 在指定旧 span 含 H 时常数阶退化，仍须新的独立算术相关估计

若另行得到 E₊|B|²=o(L⁻²) 且 |v|≥1/2，则这里只给条件性的固定中心值 nonvanishing 比例 ≥21/22−o(1)，不能说恢复 Zhang 主结论。

## 检查

信任边界：除已有 Lean 验证的 actual ν² tail / arithmetic 外，本桥还引用 CM 所用的 hyper-Kloosterman 深定理（Smith, Theorem 6）。它是 source-level 外部数学输入，尚未在本仓库 Lean 形式化；不能把整个桥说成仅依赖现有 Lean 库的已形式化结果。

`python check_finite.py` 已通过；结果、实际源文件 SHA256 见 [finite_checks.json](finite_checks.json)。覆盖精确指数、ramified 删除、双 cutoff 系数、有限卷积能量、even-primitive principal 校正、含 odd ψ 的 Gauss CRT、twisted root 矩、M=0 phase identity、Fejér 系数及 22-root obstruction。它们是有限回归，不是渐近证明或 Lean 证书。

这只重建本项目的正确移植接口，不声称已发表 CM/BPZ 主定理有误。

后续范围核对：[实际加权零点正采样](../zero_measure_phase/STATUS.md)证明限定源分支下的相位趋于−1；共同高度的正质量结论不自动转移为Z2或strict gain。
