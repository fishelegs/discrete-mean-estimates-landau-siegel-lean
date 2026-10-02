/-
  ZhangLS —— 张益唐 Landau–Siegel 论文全体系形式化蓝图总库
  
  聚合全部 44 个 Lean 4 形式化模块：
  对标国际顶尖数论形式化项目 TS6 架构，包含：
  顶层逻辑、代数骨架、微积分核、四大深水区基础设施、
  以及按 REAL_PLAN.md 攻克的真实实分析与 Dirichlet 级数血肉库！
-/

-- Layer 1 & 2: 顶层反证法、常数与代数骨架
import ZhangLS.Basic
import ZhangLS.AssumptionA
import ZhangLS.MainIdentity
import ZhangLS.NonNeg
import ZhangLS.MainTerms
import ZhangLS.Contradiction
import ZhangLS.Theorem1
import ZhangLS.IntervalIntegrals
import ZhangLS.CauchyReduction
import ZhangLS.AnalyticHypotheses

-- Layer 3: 初等算术、微积分与拓扑零点
import ZhangLS.ArithmeticBasics
import ZhangLS.KernelCalculus
import ZhangLS.RoucheGap
import ZhangLS.SmoothWeight
import ZhangLS.CharacterOrthogonality

-- Layer 4: 深水区解析引理
import ZhangLS.Estimates
import ZhangLS.CrossTermCancellation
import ZhangLS.ContourShift
import ZhangLS.TaylorApproximation
import ZhangLS.StirlingAsymptotics
import ZhangLS.BadCharacterDensity
import ZhangLS.ApproxFunctionalEquation

-- Phase 2 P1-P4 族解析数论底层基础设施
import ZhangLS.LargeSieveFoundation
import ZhangLS.HilbertInequality
import ZhangLS.AbelSummation
import ZhangLS.StieltjesIntegration
import ZhangLS.PerronFormula
import ZhangLS.EulerProducts
import ZhangLS.MellinConvolution
import ZhangLS.QuadraticReciprocity
import ZhangLS.ComplexAnalysisBounds
import ZhangLS.LogDerivativePoles
import ZhangLS.CauchyDerivativeFormula
import ZhangLS.FareySequence
import ZhangLS.ExponentialSumOrthogonality
import ZhangLS.LargeSieveMultiplicative
import ZhangLS.ResidueEvaluation
import ZhangLS.ModelZeroLattice
import ZhangLS.RoucheMinMaxBound
import ZhangLS.EulerProductNonvanishing

-- REAL_PLAN 真实实分析与解析数论血肉层 (无假模型，真实微积分与级数)
import ZhangLS.RealDirichletSeries
import ZhangLS.RealKernelCalculus
import ZhangLS.RealCharacterParseval
import ZhangLS.RealEulerProducts

-- 桥接国际数论形式化项目 AxiomMath/ZetaZeros 资产
import ZhangLS.ZetaZerosBridge

-- 桥接 Terence Tao (陶哲轩) 团队 PrimeNumberTheoremAnd 核心复分析资产
import ZhangLS.TaoAnalysisBridge

-- 深度复用 Tao 团队 MellinCalculus 攻克张益唐式 (10.6) Mellin 逆变换与常数 𝔡'
import ZhangLS.TaoMellinIntegration

-- 大筛法连续实变分析核心枢纽 (Gallagher's Lemma, 1967)
import ZhangLS.GallagherLemma

-- 真实连续零点排斥三段论边界模长下界与围道高斯积分衰减
import ZhangLS.RoucheContinuousBound
import ZhangLS.RealContourShift

-- 真实 Dirichlet 多项式乘积 F·G 截断相消与四大离散均值项 Θ₁ 双重和展开
import ZhangLS.RealDirichletPolynomialProduct
import ZhangLS.RealDiscreteMeanDecomp

-- 消灭 opaque F_poly 与 G_poly 的真实有限多项式构造
import ZhangLS.RealDirichletPolynomialsConcrete

-- 板块一任务 1.1：分母 Dirichlet 多项式无零点下界 |F(s, ψ)| ≥ ℒ⁻⁷⁹
import ZhangLS.RealFPolynomialLowerBound

-- 板块一任务 1.2 & 1.3：尾项截断的复平面围道积分放缩与 Rouché 辐角主导界
import ZhangLS.RealRoucheTailBound

-- 板块二任务 2.1 & 2.2：连续函数空间 Sobolev W¹ 导数能量与大筛法常数合成
import ZhangLS.RealSobolevEnergy

-- 板块二任务 2.3：Gauss 和等距与乘性特征到 Farey 点连续转换的大筛法终极定理
import ZhangLS.RealGaussSumLargeSieve

-- 板块三任务 3.2：Section 10 扰动多项式留数积分收敛与主常数 Re{𝔡'} > 5.100 保持
import ZhangLS.RealSection10Perturbations

-- 板块三任务 3.3：Section 15-17 三重 Mellin 围道积分展开与交叉项负抵消
import ZhangLS.RealTripleMellinCancellation

-- 板块三任务 3.3.1：Section 15 双重 Mellin 耦合留数核实参数解耦与 -7 负偏置提取
import ZhangLS.RealDoubleMellinKernel

-- 板块四任务 4.1：阶梯函数 X₄ 连续 Stieltjes 分部积分与 x⁻¹ 导数核提取
import ZhangLS.RealStieltjesKernelIntegral

-- 板块四任务 4.2：乘性特征二次矩均值测度与 Chebyshev-Markov 坏特征稀疏性 |Ψ₂| ≪ 𝒫 ℒ⁻⁷³⁹
import ZhangLS.RealBadCharacterMeasure

-- 板块三任务 3.3.A：对数矩基本积分递推与实轴微积分求值库
import ZhangLS.RealLogMomentCalculus

-- 板块三任务 3.3.B：Stirling 渐近展开与复垂线围道超多项式高斯衰减
import ZhangLS.RealStirlingContourDecay

-- 板块三任务 3.3.C：三变量留数核多元 Laurent 展开与负非对角交叉项提取
import ZhangLS.RealTripleLaurentResidue

-- 板块三任务 3.3.D：三大留数分量 Φ₁, Φ₂, Φ₃ 机器认证区间算术求值
import ZhangLS.RealPhiComponentBounds

-- 终极大山一 M1.1：对接陶哲轩 GeneralMeromorphic 架构与 Dirichlet L 函数全纯延拓留数通用库
import ZhangLS.RealMeromorphicContinuation

-- 终极大山一 M1.2：Montgomery-Vaughan 广义 Hilbert 离散算子范数与 Farey 测度嵌入
import ZhangLS.RealHilbertMeasureEmbedding

-- 终极大山二 M2.1：推广陶哲轩 ResidueCalcOnRectangles 至二维张量积矩形围道两阶段留数平移策略
import ZhangLS.RealDoubleResidueShift

-- 终极大山二 M2.2：特殊函数任意多项式对数定积分全自动递归闭式求值自动机
import ZhangLS.RealLogPolynomialAutomaton

-- 终极战役 Campaign V 任务 V.1：彻底消解 ZhangAnalyticEnvironment 包装的无条件顶层反证闭环定理
import ZhangLS.UnconditionalTheorem1

-- 终极战役 Campaign V 任务 V.2：原函数导数相消与微积分基本定理严格定积分连接
import ZhangLS.RealStrictCalculusIntegral

-- 终极战役 Campaign V 任务 V.3：复平面 4 段分段参数化曲线积分与 Cauchy-Goursat 闭围道边界相消
import ZhangLS.RealCauchyGoursatContour

-- 终极战役 Campaign V 任务 V.4：微观圆周全相角紧致有限覆盖网格与 Lipschitz 连续模长保真
import ZhangLS.RealCompactAngleCoverage

-- 论文瑕疵彻底修复 1：分母 Dirichlet 多项式 F(s, ψ) 微观紧致圆盘 Ω₁ 零点完全排除定理
import ZhangLS.Fix1_FPolynomialZeroExclusion

-- 论文瑕疵彻底修复 2：Section 17 奇异交叉项悬崖式抵消安全裕量 26 倍稳健拓宽定理
import ZhangLS.Fix2_RobustParameterMargin

-- Repaired trusted specification layer.  Legacy modules above remain imported
-- temporarily for migration, but new work should depend on `ZhangLS.Spec`.
import ZhangLS.Spec

-- Verification umbrella: forces every ZhangLS submodule into the default `lake build` closure.
import ZhangLS.All
