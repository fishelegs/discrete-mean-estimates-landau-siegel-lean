# 实际ν²τq加权尾：中央Lean核验通过

真实原χ与NormalizedAssumptionA、1≤q≤9、严格D²⁰<n≤Z和任意实上界Z≤P⁴下，已证明

    Σ ν(n)² τ_q(n)/n ≤ C_q L^(4q−2015),   C_q>0.

同一个最终D₀先于q、χ与端点量词，C_q只依赖q。保留原假设指数2022；没有把线性尾、majorant或最终尾界当作额外前提。

核心定理为[ squareNu_weighted_real_tail_uniform ](../ZhangLS/Spec/SquareNuTailConvolutionCapstone.lean)。证明由真实线性ν尾、平方支撑majorant、正卷积幂尾及收敛平方和组成。Lean采用较松的K=q²−2q；它只增加固定常数，L/P指数不变。

九个新证明模块与七个已有支持模块已中央fresh编译。独立语义审查接受；100显式公开声明与55生成声明合计155 proof-owned，另27回归/fixture-owned，全部182声明、全类型和公理闭包核验，只含propext、Classical.choice、Quot.sound。二十项回归覆盖严格端点、非整数floor、真实q=9、q=10阈值失效、K=0及两个有序交叉项。

[完整核验证据](square_nu_tail/VERIFICATION.json) · [独立语义审查](square_nu_tail/INDEPENDENT_REVIEW.md) · [源码与复现](square_nu_tail/REPRODUCE.md)

[来源层解析应用](square_factor_tail/STATUS.md)用此尾界支付全部strong-pair区域，消除此前j=3/4低e的log损失；这些完整解析完成估计尚未Lean化。真正weak-pair算术协方差、strict signed半范数阈值和原主结论仍缺。编号仍37原+3修订=40/51。

恢复后的885个指定依赖模块已逐个通过；这不是全部项目模块的fresh核验。本次是完整的上述算术桥及其依赖/语义/所有权核验，整库恢复与托管CI状态单独记录。
