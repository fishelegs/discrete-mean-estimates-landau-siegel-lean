# Discrete mean estimates and the Landau–Siegel zero — Lean 形式化

云端里程碑（2026-10-02）：[完整 Proposition 2.1](ZhangLS/Spec/Proposition21.lean) 已证明并核验。真实Ψ₂被严格识别为Ψ中Ψ₁的补集，由已完成3.4、3.5、3.6的三个实际坏集并集界导出原文C𝒫L^-739，保留(A)和统一C/D₀量词。1模块及依赖、5回归、5标准公理接口、独立语义审查通过；新完整lake build PASS（4911项）。累计 **28/51完成，3项进行中（5.6、8.1、8.3），20项未开始**。详见[核验证据](audit/CLOUD_PROPOSITION21_STATUS.md)。

云端里程碑（2026-10-02）：[完整 Lemma 17.1](ZhangLS/Spec/Lemma171.lean) 已证明并通过中央核验：保留原文严格 n<D⁴、实际 a=(6/π²)L′(1,χ)²∏p/(p+1)、原始(A)和统一 ε/D₀ 量词，得到绝对 a+o(1)。真实Euler乘积、Mellin交换、留数及误差、有限/无限移线、左积分和去平滑均已证明，未把它们作为最终前提。20模块、15展开回归、143标准公理接口及独立语义审查通过；新完整lake build PASS（4910项）。累计 **27/51完成，3项进行中（2.1、5.6、8.1），21项未开始**。详见[核验证据与范围](audit/CLOUD_LEMMA171_STATUS.md)。

云端里程碑（2026-10-02）：[完整 Lemma 3.6](ZhangLS/Spec/Lemma36.lean) 的 `lemma36_proved : Lemma36Target` 已通过内核及原文语义检查。真实截断卷积满足 |varsigma(n)|≤|ν(n)|τ₂(n)，已完成3.2与3.3的实际均值接合；4L权重积分和34L²均方损失导出原文异常数≤C𝒫L^-739。6模块及依赖、16个回归、45个标准公理接口通过。累计 **26/51完成，4项进行中（2.1、5.6、8.1、17.1），21项未开始**。新引理、所需依赖及新云端完整lake build（4881项，含两层聚合）均通过；逐Spec重检和全部旧回归遍历仍另行进行。详见[证据与范围](audit/CLOUD_LEMMA36_STATUS.md)。

云端里程碑（2026-10-02）：[完整 Lemma 11.1](ZhangLS/Spec/Lemma111.lean) 的 `lemma111_proved : Lemma111Target` 已通过固定 Lean 4.30.0 内核验证。保留真实 Gaussian、原文帐篷函数、两个闭内部区间和三个开过渡区间；显式绝对常数 C=4000、c=1，并证明对所有 y>0 的更强统一误差 4000L^-24。4 个模块及其依赖构建、8 个原文展开/边界回归、32 个标准公理接口通过，独立语义审查接受。累计 **25/51 完成，4 项进行中（3.6、5.6、8.1、17.1），22 项未开始**。本轮是新引理及依赖的聚焦验证，尚未宣称旧模块/全部回归的新云端全量 PASS。详见 [验证范围与证据](audit/CLOUD_LEMMA111_STATUS.md) 和 [51 条结果依赖图](audit/CLOUD_DEPENDENCY_MAP.md)。

历史状态说明：根目录 STEP141_STATUS.md 是冻结于 Step127 的旧临时记录；已完成 3.2 的依据是实际源码及 audit/STEP137_STATUS.md，不能按文件编号大小判断最新数学进度。

本轮 Step 137 已完成完整 Lemma 3.2：`lemma32_proved : Lemma32Target` 保留原文实际ν²τ₂²、D⁴<n≤D⁸、归一化(A)、统一正绝对常数及充分大模数阈值。实际统一 Burgess 区间／部分和界由强归纳证明，Hasse界、CRT、复合四阶矩、放大、Fourier补全和区间边界均已接通；未假设最终算术界。13新模块、26接口、6定义，合计514个算术接口、两个Hasse最终定理和137个回归通过标准公理检查。Step137全量内核核验 **PASS**（628个逐模块Spec检查、Spec聚合、893个项目导入的构建、86个回归文件；982源码指纹不变；2026-10-02 19:01:20–2026-10-02 19:17:46 Asia/Shanghai）。严格审计357个已审查候选完全不变，非零退出保留。正式账本 **24/51完成、1项进行中、26项未开始**，5.6模数1情形仍待证明。详见[Step137状态](audit/STEP137_STATUS.md)。

本轮 Step 136 已正式接入 Fourier 补全和两端区间估计：10模块、33新接口、2定义；实际实二次 Gauss 和模长为√D，实际区间字符和≤2√D(1+logD)，小区间和N≥D^(79/128)的大区间均已达到D^(25/128)√N尺度。4858项构建、488个算术接口、两个Hasse最终定理及131个回归PASS；968源码指纹不变，955旧非聚合源码未变。增量检查承接Step135与Step130全量PASS，未运行968源码逐模块全量遍历；严格审计357候选／非零退出保留。中间区间Burgess归纳、统一部分和及完整3.2仍UNPROVED。账本23/51完成、2项进行中、26项未开始。详见[Step136状态](audit/STEP136_STATUS.md)。

本轮 Step 135 已正式接入 Burgess 放大组件：23模块、62新接口、10定义；实际重数质量≤AN、平方和≤3AN(1+logA)，实际移位和的加权四阶矩、互素乘子计数及D^(1/2048)密度控制、区间边界和有限平均均已证明。4848项构建、455个算术接口、两个Hasse最终定理及125个回归PASS；957源码指纹不变，931旧非聚合源码未变。增量检查承接Step134与Step130全量PASS，未运行957源码逐模块全量遍历；严格审计354候选／非零退出保留。Burgess参数选择与归纳、长区间估计、统一部分和及完整3.2仍UNPROVED。账本23/51完成、2项进行中、26项未开始。详见[Step135状态](audit/STEP135_STATUS.md)。

本轮 Step 134 已正式接入复合模数相关和、约数／根差平均及统一四阶矩：15模块、36新接口、7定义；实际原始实二次字符的四阶矩≤3DH²+C D^(17/32)H⁴，显式C=256·192^(192^32)。4817项构建、393个算术接口、两个Hasse最终定理与115个回归PASS；933源码指纹不变，915旧非聚合源码未变。增量检查承接Step133与Step130全量PASS，未运行933源码逐模块全量遍历；严格审计353候选／非零退出保留。Burgess放大、重数二阶矩、统一部分和及完整3.2仍UNPROVED。账本23/51完成、2项进行中、26项未开始。详见[Step134状态](audit/STEP134_STATUS.md)。

本轮 Step 133 已正式接入实际 Hasse 界与素数四阶矩：187个清理并重新编译的外部模块及5个算术模块，新增11接口；357个算术接口、两个Hasse最终定理和107个回归通过标准公理检查，项目4802项构建PASS。外部7900声明无非标准公理或未完成证明依赖。实际素数四阶矩≤3pH²+12H³+H⁴(2√p+1)，非配对相关和≤3√p。917源码指纹不变；本轮为承接Step132及Step130全量PASS的增量检查，未运行917源码逐模块全量遍历。严格审计350候选和非零退出保留。复合模数推广、Burgess放大、统一算术输入及完整3.2仍UNPROVED；账本23/51完成、2项进行中、26项未开始。详见[Step133状态](audit/STEP133_STATUS.md)。

本轮 Step 132 接入实际 CRT 分解与原始二次字符模数结构：16 个新模块、40 个接口、10 个定义，合计346项标准公理接口／101个回归及项目构建PASS。局部字符保留原始性、实值性和二次性；实际四次相关和按CRT分解；模数D=2^e m，其中e≤3、m为奇数且平方自由。724源码在增量检查期间指纹不变，705旧非聚合源码未变；未运行724源码的逐模块全量遍历，承接Step131增量检查和Step130全量PASS。Hasse最终定理及素数四阶矩已在独立临时环境通过标准公理检查，清理源码后的重编译及正式接入待完成。复合模数相关和界、Burgess放大、统一算术输入及完整3.2仍UNPROVED。账本23/51完成、2项进行中、26项未开始。详见[Step132状态](audit/STEP132_STATUS.md)。

本轮 Step 131 接入 Lemma 3.2 的全部重复根相关和与实际点数余项：8 个新模块、20 个新接口、3 个定义，合计306项标准公理接口／72个回归及项目构建通过。素数模数、H≤p 时，四阶矩≤3pH²+12H³加实际互异根余项；余项准确等于∑|#E(𝔽p)−p−2|。增量检查承接刚完成的Step130全量PASS；707源码在增量检查期间指纹不变，696个旧非聚合源码未变。未重复运行707源码的逐模块全量遍历。Hasse界、复合模数推广、Burgess放大及完整Lemma3.2仍UNPROVED。账本23/51完成、2项进行中、26项未开始。详见[Step131状态](audit/STEP131_STATUS.md)。

本轮 Step 130 接合 Lemma 3.2 的显式算术归约与实际有限域字符和：33 个新增模块、80 个新增接口、20 个定义；合计286项标准公理接口和61个回归、正式构建均PASS。实际字符部分和的统一 Burgess 界可推出实际左积分界并闭合原始尾和目标，但该算术输入仍UNPROVED。已无条件证明四阶矩展开、配对项≤3DH²、重复根相关和，以及四次字符和到实际椭圆曲线点数的精确恒等式。Step 130 全量内核验证 **PASS**（538模块、616导入、698源码、79回归，全部指纹不变；2026-10-02 13:22:29–2026-10-02 14:12:17 Asia/Shanghai）。完整 Lemma3.2 **UNPROVED**：四异根界、复合模数推广和 Burgess 放大仍缺。账本 **23/51完成、2项进行中、26项未开始**。详见 [Step 130 状态](audit/STEP130_STATUS.md)。

当前进度见 [progress.md](progress.md)（Step 137全量检查通过，24/51 完成，1 项进行中）。工程包含可信 `ZhangLS.Spec`
重建层和旧版骨架。Lean 编译成功只验证所写命题；旧版 `L`、零点计数等定义
仍不对应论文对象。论文级 `Theorem1Target`、`Theorem2Target` 尚未证明。

本轮 Step 129 接合 Lemma 3.2 的实际无限移线与原始尾和归约：19 个新增模块、58 个新增接口、8 个定义；合计206项标准公理接口和39个回归已通过正式检查。平滑差等于实际留数加实际左竖线积分；原始尾和乘正绝对常数≤C L^-2007加左竖线积分模长。修正因子在Re s≥3/4上统一≤Cφ D^(1/128)。Step 129 全量内核验证 **PASS**（505模块、583导入、664源码、78回归，全部指纹不变；2026-10-02 12:09:14–2026-10-02 12:54:39 Asia/Shanghai）。完整 Lemma3.2 **UNPROVED**：实际左竖线积分的统一小量界仍缺。账本 **23/51完成、2项进行中、26项未开始**。详见 [Step 129 状态](audit/STEP129_STATUS.md)。

此前 Step 128 接合 Lemma 3.2 的实际级数、Mellin 恒等式、尾和比较和留数：18 个新增模块、63 个新增辅助定理、9 个定义；与此前 Euler／圆积分基础合计148项标准公理接口和24个回归已独立检查。原始尾和乘正绝对常数不超过实际平滑差；实际留数等于正则分子的七阶导数除以7!，并有 C L^-2007 界。正式构建及148标准公理/24回归PASS。Step 128 全量内核验证 **PASS**（486模块、564导入、644源码、77回归，全部指纹不变；2026-10-02 11:11:06–2026-10-02 11:53:44 Asia/Shanghai）。完整 Lemma3.2 **UNPROVED**：全局移线及导出误差界、平滑差上界仍缺。账本 **23/51完成、2项进行中、26项未开始**。详见 [Step 128 状态](audit/STEP128_STATUS.md)。

此前 Step 127 接合 Lemma 3.2 的实际 Euler 修正与圆积分界：22 模块、85 个辅助定理、14 个定义及 8 个回归例已独立通过内核；原始(A)下、半径 L^-2024、原文 D^(8w)-D^(4w) 的归一化圆积分 ≤ C L^-2007，C 为正绝对常数。正式构建与85标准公理/8回归通过。Step 127 全量内核验证 **PASS**（468模块、546导入、625源码、76回归，全部指纹不变；2026-10-02 10:19:44–2026-10-02 11:06:01 Asia/Shanghai）。完整 Lemma3.2 **UNPROVED**：实际加权 Dirichlet 级数等式、全局 Mellin 与移线误差、原始尾和连接仍缺。账本 **23/51完成、2项进行中、26项未开始**。详见 [Step 127 状态](audit/STEP127_STATUS.md)。

此前 Step 126 已接合 [完整 Lemma 3.5](ZhangLS/Spec/Lemma35.lean)：`lemma35_proved : Lemma35Target` 保留原始Ψ、严格素数区间、实际X₃及中心s₀、P²端点与D⁴到P²积分、严格L^-585条件、原文𝒫、归一化(A)与统一C/D₀量词。显式C=50400(32+π²)，D₀由3.1指数吸收和实际素数质量下界推出；可积性、均方与质量比较全部已证。计数界L^-746强于原文L^-739。8模块、29标准公理接口、6回归（5原文展开）通过；602源码无占位、结构通过，严格审计126个候选完全不变，退出码1保留。Step 126 全量内核验证 **PASS**（446模块、524导入、602源码、75回归，全部指纹不变；2026-10-02 09:29:14–2026-10-02 10:11:22 Asia/Shanghai）。完整3.5已完成；账本 **23/51完成、1项进行中、27项未开始**，5.6模数1仍待证明。详见 [Step 126 状态](audit/STEP126_STATUS.md)。

此前 Step 125 已接合 [完整 Lemma 3.1](ZhangLS/Spec/Lemma31.lean)：`lemma31_proved : Lemma31Target` 保留原始ν、D⁴<n≤P²、实际L(1,χ)、原始归一化(A)与统一C/D₀量词。显式C=1260，D₀由指数衰减统一推出；平方卷积上界、实际字符调和截断2D/N、累计和6√D√N、一次尾和21L^-2013及总和30L²均已证明。23模块、76标准公理接口、7回归（6原文展开）通过；593源码无占位、结构通过，严格审计126个候选（旧125不变、新1为局部推导的有限Abel恒等式）且退出码1保留。Step 125 全量内核验证 **PASS**（438模块、516导入、593源码、74回归，全部指纹不变；2026-10-02 08:46:07–2026-10-02 09:26:35 Asia/Shanghai）。完整3.1已完成；账本 **22/51完成、1项进行中、28项未开始**，5.6模数1仍待证明。详见 [Step 125 状态](audit/STEP125_STATUS.md)。

此前 Step 124 已接合 [完整 Lemma 3.4](ZhangLS/Spec/Lemma34.lean)：`lemma34_proved : Lemma34Target` 保留原始Ψ、严格素数区间、实际ν20/υ20、中心s0、D80端点和积分、原始严格B阈值及原文𝒫。显式C=51208·81^1600，D₀=ceil(exp3)，无需(A)。13模块、44标准公理接口、4原文展开回归通过；569源码无占位、结构通过，严格审计125个旧候选不变且退出码1保留。Step 124 全量内核验证 **PASS**（415模块、493导入、569源码、73回归，全部指纹不变；2026-10-02 07:33:50–2026-10-02 08:09:46 Asia/Shanghai）。完整3.4已完成；账本 **21/51完成、1项进行中、29项未开始**，5.6模数1仍待证明。详见 [Step 124 状态](audit/STEP124_STATUS.md)。

此前 Step 123 已接合 [完整 Lemma 3.3](ZhangLS/Spec/Lemma33.lean)：`lemma33_proved : Lemma33Target` 保留原始Ψ、严格素数区间、实际Dirichlet和、原文𝒫、两条长度与实幂能量及统一量词次序。第一条常数1；第二条由已证采样／Fourier／分数分离／Gauss转换给出；共同C=32+π²、D₀=ceil(exp3)，无需(A)。8模块、44标准公理接口、3原文展开回归通过，555源码无占位且结构通过。严格静态审计125个已审查候选（旧124不变，新增1个为已推导对数阈值），退出码1保留。Step 123 全量内核验证 **PASS**（402模块、480导入、555源码、72回归，全部指纹不变；2026-10-02 06:31:56–2026-10-02 07:04:54 Asia/Shanghai）。完整3.3已完成；账本 **20/51完成、1项进行中、30项未开始**，5.6模数1仍待证明。详见 [Step 123 状态](audit/STEP123_STATUS.md)。

此前 Step 122 已接合 [完整 Lemma 6.1](ZhangLS/Spec/Lemma61.lean)：`lemma61_proved : Lemma61Target` 已通过内核与原文展开回归，保留原始Ψ、严格区域、实际L／K／N／E1及统一量词次序；有限Gaussian短和、原左侧对偶主项、实际尾和／Z误差、完整L水平边及统一常数／阈值均已证明。k=1/8，D₀=ceil(exp64)+1，C为显式正绝对常数。11模块、36标准公理接口、3展开回归通过；546源码无占位、结构通过，严格静态审计仍124个已审查候选。Step 122 全量内核验证 **PASS**（394模块、472导入、546源码、71回归，全部指纹不变；2026-10-02 05:54:47–2026-10-02 06:27:22 Asia/Shanghai）。完整6.1已完成；账本 **19/51完成、1项进行中、31项未开始**，5.6模数1仍待证明。详见 [Step 122 状态](audit/STEP122_STATUS.md)。

此前 Step 121 推进 [Lemma 6.1 的原左侧实际Z误差](ZhangLS/Spec/Lemma61OriginalLeftError.lean)：零点处可去的正则部分、实际误差积分可积性（含Re s=1/2）、精确反射误差路径移线及水平边预算已证明；原左侧归一化Z误差 ≤(35exp(246π+1)+16exp(2+4π))E₁(1/8)，L≥64。四模块、19项标准公理接口、3项展开回归通过；534源码无占位、结构通过，严格静态审计仍124个已审查候选。Step 121 全量内核验证 **PASS**（383模块、461导入、534源码、70回归，全部指纹不变；2026-10-02 05:18:02–2026-10-02 05:49:34 Asia/Shanghai）。完整6.1仍待有限对偶短和的Gaussian关系、完整L水平边预算及统一常数／阈值组合；账本 **18/51完成、2项进行中、31项未开始**，5.6模数1仍待证明。详见 [Step 121 状态](audit/STEP121_STATUS.md)。

此前 Step 120 推进 [Lemma 6.1 的实际对偶尾和截断](ZhangLS/Spec/Lemma61ReciprocalTailTruncation.lean)：原文 n<T³／n≥T³ 精确拆分、宽矩形中实际Z与P₄抵消、远左实际尾积分、两条水平边及实际Cauchy关系已证明；原左侧归一化尾积分 ≤2exp(2+4π)(M₂+M₅/₄)exp(−L¹⁰/8)，L≥64。五模块、24项标准公理接口、3项展开回归通过；529源码无占位、结构通过，静态审计仍124个已审查候选。Step 120 全量内核验证 **PASS**（379模块、457导入、529源码、69回归，全部指纹不变；2026-10-02 04:43:22–2026-10-02 05:14:33 Asia/Shanghai）。完整6.1仍待有限对偶短和的误差路径移线、完整水平边预算及统一常数／阈值组合；账本 **18/51完成、2项进行中、31项未开始**，5.6模数1仍待证明。详见 [Step 120 状态](audit/STEP120_STATUS.md)。

此前 Step 119 推进 [Lemma 6.1 的实际单L留数](ZhangLS/Spec/Lemma61SingleResidue.lean) 与 [右侧Gaussian截断](ZhangLS/Spec/Lemma61RightTruncation.lean)：原始Ψ下的实际功能方程、Re w=−1到2的实际留数和四边有限积分恒等式已证明；实际单L绝对级数给出统一上界，右侧有限归一化积分与实际K之差 ≤9M₂ exp(−L¹⁰/8)，L≥64。两模块、15项标准公理接口、3项展开回归通过；523源码无占位、结构通过，静态审计仍124个已审查候选。Step 119 全量内核验证 **PASS**（374模块、452导入、523源码、68回归，全部指纹不变；2026-10-02 04:09:35–2026-10-02 04:40:07 Asia/Shanghai）。完整6.1仍待左侧对偶积分、对偶尾和截断及水平边预算；账本 **18/51完成、2项进行中、31项未开始**，5.6模数1仍待证明。详见 [Step 119 状态](audit/STEP119_STATUS.md)。

此前 Step 118 推进 [Lemma 6.1 的实际Z误差](ZhangLS/Spec/Lemma61ActualZError.lean)：任意实部的锐利Gamma对数导数、原始Ψ下宽区域归一化Z界、实际水平模长模型、小复位移差商及闭位移端点均已证明。路径 Re w=1−2Re s 将对偶短和精确转为原文 n<T³ 的有限和；实际误差积分及归一化积分均 ≤35exp(246π+1) E1。五模块、28项标准公理接口、3项展开回归通过；520源码无占位、结构通过，静态审计仍124个已审查候选。Step 118 全量内核验证 **PASS**（372模块、450导入、520源码、67回归，全部指纹不变；2026-10-02 03:35:16–2026-10-02 04:06:10 Asia/Shanghai）。完整6.1仍待实际轮廓关系、对偶尾和截断、水平边及竖直尾预算；账本 **18/51完成、2项进行中、31项未开始**，5.6模数1仍待证明。详见 [Step 118 状态](audit/STEP118_STATUS.md)。

此前 Step 117 推进 [Lemma 6.1 的实际 Gaussian 输入](ZhangLS/Spec/Lemma61GaussianCutoff.lean)：原文 g*、P4、K、N、严格 n<T³ 的 E1 与原始Ψ／严格区域已定义；有限支撑恒等式、整函数性、E1正性／可积性、实际单个L的Gaussian Mellin恒等式和实际K／对偶N截断误差 ≤绝对常数 exp(−L¹⁰) 均已证明。四模块、32项标准公理接口、3项展开回归通过；514源码无占位、结构通过，静态审计仍124个已审查候选。Step 117 全量内核验证 **PASS**（367模块、445导入、514源码、66回归，全部指纹不变；2026-10-02 03:01:07–2026-10-02 03:32:21 Asia/Shanghai）。完整6.1仍待轮廓移动、对偶有限和截断及Z差的原文E1界，账本 **18/51完成、2项进行中、31项未开始**；5.6模数1仍待证明。详见 [Step 117 状态](audit/STEP117_STATUS.md)。

此前 Step 116 已接合 [完整 Lemma 5.9](ZhangLS/Spec/Lemma59.lean)：`lemma59_proved : Lemma59Target` 保留实际 L、原始 Ψ1、原文闭区域、全部实际零点的分离条件及统一常数／阈值。扩大近似函数方程、实际零点临界线／重数1／间距、真实排序乘积与数值预算均已证明。11模块、108项标准公理接口、3项原文及闭边界回归通过；509个源码无占位、结构通过，严格静态审计124个已审查候选。Step 116 全量内核验证 **PASS**（363模块、441导入、509源码、65回归，全部指纹不变；2026-10-02 02:24:29–2026-10-02 02:58:00 Asia/Shanghai）。完整Lemma5.9正式完成，账本 **18/51完成、1项进行中、32项未开始**；5.6模数1仍待证明。详见 [Step 116 状态](audit/STEP116_STATUS.md)。

此前 Step 115 已接入 [Lemma 5.9 的实际零点因子与剩余函数界](ZhangLS/Spec/Lemma59ZeroRemovedShift.lean)：实际 L=P Q 包括被移除零点；原始 Ψ1 下，Q 的原文第一位移商统一 ≤exp(166400π)，实际 L 商等于带真实解析重数的零点乘积乘 Q 商。五模块、33 项标准公理接口、5 项展开回归通过；497 个源码无占位、结构检查通过，严格静态审计 118 个已审查候选。Step 115 全量内核验证 **PASS**（352 模块、430 导入、497 源码、64 回归，全部指纹不变；2026-10-02 01:47:11–2026-10-02 02:18:15 Asia/Shanghai）。扩大近似函数方程和零点结构草稿已独立验证，尚未计入本轮覆盖。完整 Lemma 5.9 商及 Lemma 5.6 模数 1 仍未证明；账本 **17/51 完成、2 项进行中、32 项未开始**。详见 [Step 115 状态](audit/STEP115_STATUS.md)。

此前 Step 114 已接入 [Lemma 5.9 的实际局部零点与重数界](ZhangLS/Spec/Lemma59LocalZeroBudgets.lean)：半径 7/4 闭圆盘上的真实零点集、实际解析重数之和及精确成员条件已证明；原始 Ψ1 下，两项统一 ≤30log P，覆盖扩大闭高度窗口的两个端点。两模块、12 项标准公理检查、5 项展开回归通过，491 个源码无占位、结构检查通过。Step 114 全量内核验证 **PASS**（347 个可信模块、425 个导入、491 个源码、63 个回归；全部指纹不变；2026-10-02 01:11:10–2026-10-02 01:43:28 Asia/Shanghai）。严格静态审计为 116 个已审查候选。完整 Lemma 5.9 商和 Lemma 5.6 模数 1 情形仍未证明，账本 **17/51 完成、2 项进行中、32 项未开始**。独立实际因子草稿已通过 45 接口（33 个新增）和 5 项展开回归，证明 L=P Q、实际 Q 原文第一位移的统一绝对界及带真实重数的商恒等式，尚未计入本轮全量覆盖。详见 [Step 114 状态](audit/STEP114_STATUS.md)。

此前 Step 113 已接入 [Lemma 5.9 的原文闭区域辅助证明](ZhangLS/Spec/Lemma59UniformPolynomialInputs.lean) 和 [有限零点乘积界](ZhangLS/Spec/Lemma59FiniteZeroProducts.lean)：实际 F 的两侧界、非零性及 F′/F≤140800L 已从原始 Ψ1 推出，完整闭高度窗口与原文第一位移保留；实际零点分离推出 L 分母非零。零点按序距离给出望远镜乘积 N+1，上方零点因子 ≤1，至多两个近零因子的成本 ≤(1+η^-1)^2。五个辅助模块、27 项标准公理检查和 8 项展开回归已通过，488 个源码无占位、结构检查通过。Step 113 全量内核验证 **PASS**（345 个可信模块、423 个导入、488 个源码、62 个回归；全部指纹不变；2026-10-02 00:32:35–2026-10-02 01:03:17 Asia/Shanghai）。严格静态审计为 115 个已审查候选。完整 Lemma 5.9 商估计尚未证明，仍需实际扩大区域的零点结构与真实 L 因子接合；完整 Lemma 5.6 的模数 1 情形也保留待证。当前账本 **17/51 完成、2 项进行中、32 项未开始**。详见 [Step 113 状态](audit/STEP113_STATUS.md)。

此前 Step 112 推进 [Lemma 5.6 的实际素数质量与归一化](ZhangLS/Spec/Lemma56ActualPrimeMassNormalization.lean)：原始 (A) 下，实际严格窗口的 log p 质量 ≥P/(2L^68)，实际 p 质量 ≥P²/(4L^77)，并证明质量为正、窗口非空。用实际下截断 floor(P)+1 精确保留原文两个严格素数端点；实际主项与两项前缀误差给出上述下界。原文 q>1 本原特征的归一化指数估计已闭合，不添加质量下界假设，统一常数／阈值先于全部参数，保留闭振荡端点。四个新增可信模块、14 项标准公理接口、6 项展开回归通过。Step 112 全量内核验证 **PASS**（340 个可信模块、418 个导入、482 个源码、61 个回归；全部指纹不变；2026-10-01 23:52:35–2026-10-02 00:27:16 Asia/Shanghai）。严格静态审计为 114 个已审查候选，新增一处为局部已证实数下界的返回。完整 Lemma 5.6 的忠实模数 1 主特征目标仍待证明，账本 **17/51 完成、1 项进行中、33 项未开始**。详见 [Step 112 状态](audit/STEP112_STATUS.md)。

2026-10-01：可信层已完成 Proposition 2.2、Lemma 2.3、Lemma 4.1–4.8、Lemma 5.1–5.5 和 Lemma 5.7–5.8。
此前 Step 102 已完成[完整 Lemma 5.8](ZhangLS/Spec/Lemma58.lean)：实际 L 函数的线性误差在原文闭环域 α≤|s−1|≤10α 上 ≤(1+128e(10π)^2)L^-15，显式阈值可取 3^10000000；常数和阈值先于全部 D、χ、s。模块构建、四项原文及边界回归、七项标准公理检查通过；Step 102 全量内核核验 PASS，账本提升为 17/51。另有 Lemma 5.6 的算术／乘积特征基础草稿已验证，尚未接入项目，完整引理未证明。详见[Step 102 状态](audit/STEP102_STATUS.md)。
此前 Step 101 已完成[完整 Lemma 5.5](ZhangLS/Spec/Lemma55FullZeroExclusion.lean)：实际简单实零点距 1 的常数取 64，原文整个 Re s>1−2/log D、abs(Im s)<2D 内无其他零点，统一充分大模数阈值先于全部 D、χ、s。七模块、十项原文陈述及边界回归、50 项标准公理检查通过；Step 101 全量内核核验 PASS，账本提升为 16/51。另有完整 Lemma 5.8 独立草稿已验证，待下一步接入项目。详见[Step 101 状态](audit/STEP101_STATUS.md)。
此前 Step 100 已闭合 [实际 ζ 局部零点及归一化加权误差](ZhangLS/Spec/Lemma55ZetaWeightedPowerError.lean)：真实 ζ 总重数 ≤18log D，因子分解包含被移除零点；实际高阶对数导数精确保留 1 处极点贡献，全部检测阶数 J 的加权误差 ≤108000log D。十个模块、十二项回归及 66 项标准公理检查通过；Step 100 全量内核核验 PASS。另有独立草稿已验证实际算术正性、圆盘外例外项界及四组零点和统一上界，尚未接入可信项目。共同最大项的四组零点检测和统一阈值反证仍待闭合，完整 Lemma 5.5 保持进行中。
此前 Step 99 继续 [Lemma 5.5](ZhangLS/Spec/Lemma55.lean)：[实际零点检测](ZhangLS/Spec/Lemma55ExceptionalZeroRemoval.lean) 已证明：任意其他原文区域零点，在移除已证简单实零点后，给出加权偶次逆幂和下界 J/4−13log D。Fejér 权重介于 0 和 2；真实高阶对数导数与逆幂和已接合。[保留几何衰减的归一化误差](ZhangLS/Spec/Lemma55WeightedPowerError.lean) ≤79200log D，与全部检测阶数 J 无关，移除简单零点后此界保持成立。实零点与 1 处极点的加权逆幂差 ≤2(1−β)J(J+1)exp(4J/log D)。八个新增模块、实际对象／高度两端／零移除／全检测阶数回归及 60 项标准公理检查通过；Step 99 全量内核核验 PASS。ζ 的实际局部公式和算术正性上界仍待闭合，完整 Lemma 5.5 保持进行中，总账本 15/51 完成、1 项进行中、35 项未开始。
此前 Step 98 继续 [Lemma 5.5](ZhangLS/Spec/Lemma55.lean)：已抽取全部实际局部零点因子，剩余函数整解析、在完整闭局部圆盘内非零，且全平面（含被移除零点）保持实际 L=P Q 恒等式。归一化解析对数满足闭圆盘界 990log D；[实际高阶对数导数余项](ZhangLS/Spec/Lemma55HigherLogDerivative.lean) 除以 n! 后 ≤990(n+1)log D (8/9)^(n+1)，任意有限组阶数的总和 ≤71280log D。六个新增模块与实际对象／可去零点取值／两端高度／全阶回归及 33 项标准公理检查通过；Step 98 全量内核核验 PASS。此前已证简单实零点、局部唯一性及全原文区域的实际有限零点集。原文 Re s>1−2/L、|Im s|<2D 的全部区域内无其他零点仍未证明；完整 Lemma 5.5 保持进行中，总账本 15/51 完成、1 项进行中、35 项未开始。
此前已接合完整 [Lemma 5.4](ZhangLS/Spec/Lemma54.lean) 的 `lemma54_proved : Lemma54Target`：实际正轴积分的零点附近、小范围窗口外和两个大范围尾项全部已积分，指数误差已在一个统一模数阈值吸收。实际 δ 在完整 1/2≤Re s≤2 上满足 |δ(s)|≤C L^3200/|s|²，在完整 |s−1|<10α 内满足 |δ(s)−1|≤Cα log L；两项共用一个显式正绝对常数和一个先于全部 D、s 的模数阈值。六个新增模块、完整原始陈述回归和 19 项标准公理检查通过；Step 95 全量内核验证 PASS，完整 Lemma 5.4 正式完成，总进度 15/51。
此前 [第一项原始估计](ZhangLS/Spec/Lemma54UniformSecondMoment.lean) 已在完整闭条带 1/2≤Re s≤2 上证明 |δ(s)|≤C_M L^3200/|s|²，C_M 为显式绝对常数，模数阈值在所有 D、s 之前统一存在；Step 93 全量内核验证 PASS。
此前 [Lemma53.lean](ZhangLS/Spec/Lemma53.lean) 的 `lemma53_proved : Lemma53Target` 已接合完整原始两范围估计。大 x 的左尾、左竖边、下方右射线及右端趋零均已证明；统一常数 `C=4(e+1)+2+2+e+sqrt(π)exp(2)`、`k=1/2`，模数阈值统一存在。实际 Δ 保留原始逆 Mellin 定义；不增加轮廓、尾界或恒等式假设。三个新增模块、完整原始陈述回归及十二项标准公理检查通过。Step 90 全量内核验证 PASS，Lemma 5.3 正式完成。
此前 [Lemma52.lean](ZhangLS/Spec/Lemma52.lean) 的
`lemma52_proved : Lemma52Target` 保留真实 Ψ、闭实部边界和完整高度窗口，
证明原始三位移的实际 Y 乘积公式，相对误差为 `126π L^-123`。
位移使用已证 Lemma 2.3 的同一常数；实际连续平方根分支存在，
结论对每个有效分支成立。分支可微性、对数导数、竖直输运和误差
均已证明，充分大模数阈值统一存在。此前 [Lemma51.lean](ZhangLS/Spec/Lemma51.lean)
已证明四个实际 Z 位移估计，常数 22exp(600π)、闭式阈值 3^(3^200)。
当前664个源码无占位、结构检查通过；Step129全量核验PASS，覆盖505可信模块、583导入、78回归；严格静态审计132个已审查候选（旧131不变，新增1为局部导出连续性），非零严格退出保留。最近完成核验为Step129 PASS。
Step 98 全量内核审计 PASS：207 个可信模块、285 个项目导入、335 个源文件和 47 个回归全部通过；2026-10-01 10:01:34–10:20:09（北京时间）。
核验记录见 [全量验证报告](audit/lean_kernel_verification.txt)，
Step 99 全量内核核验 PASS：215 个可信模块、293 个项目导入、344 个源文件和 48 个回归全部通过；2026-10-01 10:48:30–11:07:43（北京时间）。
Step 100 全量内核核验 PASS：225 个可信模块、303 个项目导入、355 个源文件和 49 个回归全部通过；2026-10-01 11:29:29–11:49:34（北京时间）。
Step 101 全量内核核验 PASS：232 个可信模块、310 个项目导入、363 个源文件和 50 个回归全部通过；2026-10-01 12:13:18–12:35:57 Asia/Shanghai。
Step 102 全量内核核验 PASS：233 个可信模块、311 个项目导入、365 个源文件和 51 个回归全部通过；2026-10-01 12:38:43–13:00:25 Asia/Shanghai。
Step 103 全量内核核验 PASS：2026-10-01 13:25:59–13:46:27 Asia/Shanghai。
Step 104 全量内核核验 PASS：2026-10-01 14:03:29–14:25:35 Asia/Shanghai。
Step 105 全量内核核验 PASS：2026-10-01 14:49:47–15:13:26 Asia/Shanghai。
Step 106 全量内核核验 PASS：2026-10-01 15:43:30–16:08:18 Asia/Shanghai。
Step 107 全量内核核验 PASS：2026-10-01 16:33:40–16:58:53 Asia/Shanghai。
Step 111 全量内核核验 PASS：2026-10-01 23:17:56–23:48:28 Asia/Shanghai。
Step 112 全量内核核验 PASS：2026-10-01 23:52:35–2026-10-02 00:27:16 Asia/Shanghai。
Step 113 全量内核核验 PASS：2026-10-02 00:32:35–2026-10-02 01:03:17 Asia/Shanghai。
Step 114 全量内核核验 PASS：2026-10-02 01:11:10–2026-10-02 01:43:28 Asia/Shanghai。
本轮证明与验证状态见 [Step 114 状态](audit/STEP114_STATUS.md)。

论文：Yitang Zhang, *Discrete mean estimates and the Landau–Siegel zero*, arXiv:2211.02515 (2022).

上层分析与风险点见 [`../Zhang2022_Analysis.md`](../Zhang2022_Analysis.md)。

## 这个项目是什么

本项目使用 Lean 4.30.0 和 mathlib，形式化张益唐的论文
[Discrete mean estimates and the Landau-Siegel zero](https://arxiv.org/abs/2211.02515)。
实际数学对象上的证明位于 `ZhangLS/Spec/`；逐项完成情况见
[progress.md](progress.md)，最新内核验收见 [audit/lean_kernel_verification.txt](audit/lean_kernel_verification.txt)。
论文的全部主结论仍待完成。

旧版骨架存在直接传递结论假设、任意定义余项等问题；没有 `sorry` 并不消除
这些数学缺口。状态账本见 [audit/STATUS.md](audit/STATUS.md)。

## 模块依赖图

```
                       ┌─────────────────────────────────────────────┐
                       │                                             │
   Basic ──▶ AssumptionA ──▶ Estimates ──┐                            │
              │                           ├──▶ MainTerms ──▶ Contradiction ──▶ Theorem1
              ├──▶ MainIdentity ──▶ NonNeg ┘                            │
              │                                                        │
              └────────────────────────────────────────────────────────┘
```

| 文件 | 论文位置 | 内容 | 关键定理 |
|---|---|---|---|
| `Basic.lean` | 全局 | 指数常数集中管理 | `exps.compare_4_4_4_8` 等 |
| `AssumptionA.lean` | §1, §5 | 假设 (A) + Lemma 5.5 / 5.7 | `AssumptionA`, `Lemma_5_7` |
| `MainIdentity.lean` | (2.18) | 主恒等式 | `MainIdentity : Ξ* = 0` |
| `NonNeg.lean` | 旧版占位 | 整数玩具模型；不是论文 Lemma 2.3 的证明 | `Lemma_2_3_Proved_Int` |
| `Spec/Lemma23RealSign.lean` | Lemma 2.3 的实变量与复系数桥接 | 无零点区间端点同号；条件性推出竖线复系数实且非负 | `endpoint_mul_pos_of_continuousOn_nonzero`, `lemma23_verticalLine_coefficient_nonneg` |
| `Estimates.lean` | §3–§6 | 大筛法 / 近似函数方程 / 估计 | `Lemma_3_3_large_sieve`, `Lemma_4_4`, `Lemma_5_6` |
| `MainTerms.lean` | Prop 2.4/2.5/2.6 | 主项与误差项上下界 | `Proposition_2_4`, `Proposition_2_5`, `Proposition_2_6` |
| `Contradiction.lean` | §2 末 | 合并为矛盾 | `Contradiction_under_A`, `Not_AssumptionA` |
| `Theorem1.lean` | Theorem 1/2 | 顶层结论 | `Theorem1`, `Theorem2` |

## 数值预核的结果（已运行）

运行 `python3 tools/numerical_check.py`（mpmath + sympy），得到两点结论：

**(I) 指数算术审计 — 5/5 通过。** 论文里隐式用到的所有 "ℒ^{e_i} = o(ℒ^{e_j})"
关系（误差吸收链）作为纯整数不等式都成立，对应 `Basic.lean` 里的 8 个 `by decide` 定理。
这一层目前没有发现错算。

**(II) L(1,χ) 与 𝔞 的高精度计算 — 公式自洽，但揭示了一个聚焦点。**
对 D ∈ {5, 8, 13, 17, 29, 53}：

| D | L(1,χ) 级数 | L(1,χ) 类数公式 | 比值 | 𝔞 |
|---|---|---|---|---|
| 5 | 0.43041 | 0.43041 | 1.000 | 0.0643 |
| 8 | 0.62323 | 0.62323 | 1.000 | 0.0629 |
| 13 | 0.66276 | 0.66274 | 1.000 | 0.0547 |
| 17 | 1.01608 | 1.01608 | 1.000 | 0.0650 |
| 29 | 0.61179 | 0.61177 | 1.000 | 0.0211 |
| 53 | 0.54000 | 0.54002 | 1.000 | 0.0158 |

- 级数与类数公式两列高度一致（比值 = 1.000）→ **χ 的定义与 L(1,χ) 公式自洽**。✓
- 但所有小 D 上 **𝔞 ≪ 1**（0.02–0.06）。这不与论文矛盾，因为这些 D 上假设 (A)
  本身不成立（L(1,χ) 远未小到 ℒ^{-2022}）。它真正告诉我们的是：
  **"𝔞 ≫ 1" 的全部负担都落在 `Lemma 5.7`（`L'(1,χ) ≫ D/φ(D)`）的下界上**，
  因为 𝔞 公式里的 ∏_{q|D} q/(q+1) 会随 D 素因子增多而变小。
- 一个 toy 诊断印证了链路自洽：在 (A) 下 Siegel 零点距 1 约 ℒ^{-2022}，
  使 `L'(1,χ) ≈ 1/(1−ρ̃) ≈ ℒ^{2022}`，远超 `𝔞 > 1` 所要求的 ~1.4–1.8。
  即 `𝔞 ≫ 1` 不是独立假设，而是 (A) 的推论。

> **这意味着：** 数值层面没发现论文量级不自洽；剩下的核心论证（主恒等式 (2.18)、
> Lemma 2.3 非负性、Prop 2.4/2.5/2.6 的三个界）
> 无法用纯数值证实，必须进入 Lean。

## 推进顺序的建议（按"杠杆"由高到低）

1. **填 `MainIdentity`** —— 论文的算术骨架；纯等式、无估计，最应该先定下。
2. **填 `Exponents` 比较** —— 全是 `decide`，已在 `Basic.lean` 完成；数值审计也确认自洽。
3. **数值预核** —— 已运行（见上节）；公式自洽，未发现量级错算。
4. **Lemma 2.3 已完成** —— 可信层已闭合实际连续后继零点、无零区间及实际系数非负性；最终定理见 `Spec/Lemma23.lean`。旧版 `NonNeg` 的整数模型仍不计作论文证明。
5. **Lemma 5.7 已完成** —— 最终定理见 `Spec/Lemma57LeftQuadraticGrowth.lean`；无需回到旧版 `Lemma_5_7` 占位接口。
6. **填 `MainTerms`** —— 三个上下界；每填好一个，看 `Contradiction` 是否向 `False` 靠近。
7. 最后填 `Estimates`（§3–§6，工作量最大、最依赖 Mathlib 现有解析数论基础设施）。

## 构建

```bash
lake update
lake exe cache get
ZHANGMATH_SPEC_JOBS=4 tools/verify_all_lean.sh
```

需要安装由 `lean-toolchain` 固定的 Lean 工具链。该命令逐个核验全部 Spec 源码、
Spec 聚合、全工程构建和全部审计回归；任何内核检查失败都会使验收失败。
省略 `ZHANGMATH_SPEC_JOBS` 时按原来的串行模式运行。论文级数学完成度另由状态账本跟踪。

`ZhangLS/External/HasseWeil/` 保留外部 Hasse 界证明的许可证与来源说明；
引入记录和清理后的声明审计见 `audit/external_hasse_clean_manifest.json`。

## 与"修复论文"的关系

如果论文确实存在错误，最可能在 [`Zhang2022_Analysis.md` §4](../Zhang2022_Analysis.md) 所列的几个高风险点之一。
本骨架的设计使这些点各自成为独立可证伪的 `theorem`；一旦定位，可以：
- **若是恒等式错误** → 修改 `MainIdentity` 的右端项划分，重新检查 `MainTerms` 的三个界；
- **若是非负性错误** → 在 `NonNeg` 中加入修正项（如排除个别零点），重新审视 `MainTerms`；
- **若是常数算术错误** → 调整 `Exponents`，自动级联到所有依赖该指数的 `theorem`。

## Repair migration status — Step 14

The trusted `Spec` layer now contains an unconditional finite Euler-product proof
of the reciprocal-divisor estimate used in Lemma 5.7:

```text
(1 / 4) * (D / φ(D)) ≤ ∑_{d ∣ D} 1 / d.
```

This closes the reciprocal-divisor branch of the arithmetic extraction.  At that historical step, kernel verification required the pinned toolchain
outside the then-restricted container; current verification is recorded above.

## Repair migration — Step 15

The trusted `ZhangLS/Spec` layer now contains Zhang's Gaussian smoothing weight
for Lemma 5.7 and proves the explicit divisor-range lower bound `g >= 1/2`.
Combined with the unconditional reciprocal-divisor constant `1/4`, the finite
divisor subsum is bounded below by `(1/8) * D / phi(D)` at source level.
See `MIGRATION_STEP_15.md` and `audit/STEP15_STATUS.md`.

## Trusted Spec migration: Step 16

The Lemma 5.7 arithmetic branch now contains the finite smoothed sum over
`1 <= n <= D`.  Assuming only the standard sign property `νχ(n) >= 0`, this sum is
proved to dominate the divisor subsum and hence is at least
`(1/8) * D / φ(D)`.  The next isolated task is to prove this sign property from the
real quadratic Dirichlet character structure.

## Step 17 repair note

The trusted Spec layer now proves the nonnegativity of Zhang's divisor-character
coefficient unconditionally by identifying it with mathlib's quadratic-character
`DirichletCharacter.zetaMul`.  This closes the finite arithmetic side of Lemma 5.7:
`lemma57InitialArithmeticLowerBound_proved` has explicit constant `1/8` and no
coefficient-sign hypothesis.  Kernel compilation was pending at that historical step; current verification
is recorded above.

## Trusted Spec migration — Step 18

Step 18 adds `ZhangLS/Spec/Lemma57FullSmoothedSeries.lean`, defining the actual infinite
Gaussian-smoothed arithmetic series from Lemma 5.7 and proving that it inherits the explicit
`(1/8) * D/φ(D)` lower bound once global Gaussian nonnegativity and summability are established.
See `MIGRATION_STEP_18.md` and `audit/STEP18_STATUS.md`.

## Trusted-spec migration update — Step 20

The full Lemma 5.7 smoothed-series convergence problem has been reduced to a pure Gaussian tail estimate.  The trusted layer now proves `0 ≤ νχ(n)/n ≤ 1` for positive `n`, and `lemma57FullSmoothedSummable_of_cubicDecay` turns an eventual bound `g_D(D^4/n) ≤ C n^{-3}` into full summability.  The remaining target is `ZhangGaussianCubicDecay D`.

## Step 21: mandatory Lean kernel verification

Verification policy is now strict: source inspection is not enough. `ZhangLS/All.lean` imports every
project submodule, and `tools/verify_all_lean.sh` checks coverage, rejects `sorry`/`admit`, and runs
`lake build` under the pinned Lean/mathlib versions. GitHub Actions runs the same command. A result is
called Lean-verified only after that command exits successfully.

## Step 24 verification update

The strict verifier now checks every trusted Spec module individually before checking `ZhangLS/Spec/All.lean` and the full project. Per-module kernel logs are written under `audit/spec_kernel_logs/`. Step 24 also aligns several fragile arithmetic proofs with the exact mathlib v4.30 API, including the correction from `Finset.sum_div_divisors` to `Nat.sum_div_divisors`.

At Step 24 the package was not kernel-verified because Lean/Lake were unavailable. The current pinned toolchain is available and the latest full verification is recorded above. Only `tools/verify_all_lean.sh` ending in `LEAN_KERNEL_VERIFICATION=PASS` counts as verified.
### Step 25

API alignment against mathlib v4.30 corrected `Nat.mem_divisors` projection order, replaced `mem_primeFactors` tuple projections with dedicated helpers, and made `Complex.reCLM` finite-sum transport explicit. Verification now also rejects a mismatched active Lean version, and bootstrap uses the same authoritative full verifier as CI. At Step 25 kernel status was FAIL/NOT_RUN because Lean/Lake were unavailable; the current verification status is recorded above.


## Step 26 verification note

Step 26 performs another pinned-mathlib API alignment pass and strengthens the
pre-kernel source checks.  In particular, the prime-factor reconstruction now
uses `Nat.prod_primeFactors_pow_factorization` directly and the Gaussian interval
symmetry call uses the correct implicit integrand argument.  These are source
repairs, not a substitute for compilation.  A verified build still requires
`tools/verify_all_lean.sh` to report `LEAN_KERNEL_VERIFICATION=PASS` under Lean
4.30.0.

### Migration Step 27

Step 27 aligns two finite-sum proofs with direct mathlib v4.30 APIs: the real part
of a complex finite sum now uses `Complex.re_sum`, and the divisor-character
single-term reduction uses `Finset.sum_eq_single` by direct application. See
`MIGRATION_STEP_27.md`. Kernel verification is still not claimed in this container.

### Step 28

Batch v4.30.0 API alignment fixed exact-division casts, inverse-order theorem
arguments, the divisor-character single-term reduction, and a real endpoint bug
in the square-reciprocal tail (`Ioo 8 (N + 1)` now includes the final `N`).
These are source repairs only.  The project is Lean-verified only when
`tools/verify_all_lean.sh` reports `LEAN_KERNEL_VERIFICATION=PASS`.

## Step 29 — Gaussian cubic tail closure

The trusted Spec layer now contains source-level proofs reducing Zhang's Gaussian
weight to a genuine half-line tail, bounding that tail exponentially, deriving the
`n^-3` majorant along `D^4/n`, and closing full smoothed-series summability and the
`1/8 * D/φ(D)` Gaussian arithmetic lower bound.  Static gates pass; these new terms
remain **awaiting Lean 4.30.0 kernel compilation** because this sandbox has no
`lean`/`lake` executable.  See `MIGRATION_STEP_29.md` and `audit/STEP29_STATUS.md`.

## Step 30 — focused kernel and CI closure

The complete trusted `ZhangLS/Spec` layer, including the Step 29 Gaussian tail,
cubic decay, summability, and arithmetic lower-bound endpoints, now compiles under
the pinned Lean 4.30.0 kernel.  A dedicated regression module and CI command
(`tools/verify_step30_gaussian.sh`) pin the three terminal APIs.  The focused gate
and all 19 Spec modules pass; the repository-wide `lake build` still fails in 37
older non-Spec scaffold modules.  See `MIGRATION_STEP_30.md` and
`audit/STEP30_STATUS.md`.

## Step 31 — repository-wide kernel closure

The 37 legacy compilation failures were repaired without promoting the legacy
mathematical models to trusted status. The full project and all audit regressions
now pass the pinned Lean 4.30.0 gate. A false Taylor-absorption statement was
corrected by adding its missing nonnegativity hypothesis. See
`MIGRATION_STEP_31.md` and `audit/STEP31_STATUS.md`.

## Step 32 — exact Lemma 5.7 Mellin/residue interface

The trusted layer now contains Zhang's actual Mellin integrand and normalized
vertical integrals, proves the half-plane Dirichlet-product identity, and computes
the exact local residue coefficient
`L'(1,χ) + (γ + 4 log D)L(1,χ)`. The new interfaces require integrability
explicitly and reduce the remaining Lemma 5.7 work to Mellin inversion, contour
shifting, and one explicit analytic error bound. See `MIGRATION_STEP_32.md` and
`audit/STEP32_STATUS.md`.

## Step 33 — scalar Gaussian inverse-Mellin kernel

The trusted layer now proves absolute integrability of the scalar Gaussian
kernel on every nonzero vertical line and identifies the paper's normalized
integral exactly with mathlib's `mellinInv` at the reciprocal argument.  The
kernel evaluation is reduced to the single honest transform calculation
`M[x ↦ g_D(x⁻¹)](s) = ω₁(s)/s`; no scalar convergence condition remains hidden.
See `MIGRATION_STEP_33.md` and `audit/STEP33_STATUS.md`.

## Step 34 — exact Gaussian Mellin transform

The trusted layer now proves the transform left open in Step 33:
`M[x ↦ g_D(x⁻¹)](s) = ω₁(s)/s` for `Re(s)>0`, including convergence.  The proof
uses the log-coordinate Gaussian derivative, a complex Gaussian integral,
two-sided tail bounds, and improper integration by parts.  Thus the scalar
inverse-Mellin formula is now unconditional.  See `MIGRATION_STEP_34.md` and
`audit/STEP34_STATUS.md`.

## Step 35 — full Mellin identity

The trusted layer now proves `Lemma57MellinIdentity` unconditionally for every
`D > 1`.  Absolute convergence at real part `2` and the common Gaussian kernel
justify the series/integral interchange, and Step 34 evaluates each coefficient
integral as the corresponding term of Zhang's full smoothed sum.  Only the
leftward contour shift and its Assumption-(A) error bound remain in Lemma 5.7.
See `MIGRATION_STEP_35.md` and `audit/STEP35_STATUS.md`.

## Step 36 — contour-shift limit passage

The trusted layer now proves the complete limiting step from finite rectangular
contours to the two infinite vertical lines.  Symmetric truncations converge
whenever the corresponding vertical integrand is honestly integrable, and the
finite residue identities plus horizontal-edge decay imply the exact
`Lemma57ContourShiftIdentity`.  The finite rectangle theorem, left-line
integrability, and horizontal decay remain explicit analytic obligations; they
have not been hidden inside default-valued integrals.
See `MIGRATION_STEP_36.md` and `audit/STEP36_STATUS.md`.

## Step 37 — contour analyticity and local residue

The trusted layer now proves that the pole-removed numerator is entire and the
actual Mellin integrand is analytic away from zero.  Cauchy's derivative
formula computes its normalized integral on every positive-radius centered
circle as the exact residue `L'(1,χ) + (γ + 4 log D)L(1,χ)`.  The finite
rectangle theorem is thereby reduced to deforming this circle through the
punctured rectangle; left-line integrability and horizontal decay remain
separate global estimates.
See `MIGRATION_STEP_37.md` and `audit/STEP37_STATUS.md`.

## Step 38 — rectangle orientation and winding

The trusted layer now defines the positively oriented finite rectangle and
computes its inverse-kernel boundary integral exactly as `2πi`.  The proof uses
real rational integrals and arctangent identities rather than an implicit
complex-log branch.  It also proves that the normalized finite-shift statement
is precisely equivalent to the standard unnormalized rectangle residue
identity.  The remaining finite-contour step is the principal-part and entire
remainder decomposition of the actual Mellin integrand.
See `MIGRATION_STEP_38.md` and `audit/STEP38_STATUS.md`.

## Step 39 — principal-part rectangle theorem

The trusted layer constructs an entire remainder by two divided differences,
splits the genuine Mellin integrand into its `s⁻²`, `s⁻¹`, and entire
parts, and proves the exact finite rectangle residue theorem.  Consequently
`Lemma57FiniteRectangleShift` is unconditional for `D > 1`.
See `MIGRATION_STEP_39.md` and `audit/STEP39_STATUS.md`.

## Step 40 — Gaussian absorption of contour growth

The trusted layer isolates a standard exponential-growth estimate for the
undamped `ζ(1+s)L(1+s,χ)/s` factor away from its pole.  It proves that Zhang's
Gaussian absorbs this growth on the shifted vertical line and both horizontal
edges, yielding the exact infinite contour shift from that single input.  The
growth estimate itself, and then the Assumption-(A) shifted-integral error
bound, remain to be proved.
See `MIGRATION_STEP_40.md` and `audit/STEP40_STATUS.md`.

## Step 41 — critical-half-strip reduction

The trusted layer proves explicit uniform bounds for the actual Riemann zeta
and Dirichlet L-functions on `re s ≥ 3/2` using their absolutely convergent
Dirichlet series.  Hence the right half of the contour strip needs no growth
hypothesis: the exact contour shift now follows from exponential growth only
on `-1/2 ≤ re s ≤ 1/2`.  Proving this remaining critical-half-strip estimate
is the next analytic task.
See `MIGRATION_STEP_41.md` and `audit/STEP41_STATUS.md`.

## Step 42 — completed Mellin strip bounds

The trusted layer proves a general uniform vertical-strip bound for the entire
completed Mellin transform attached to any mathlib weak functional-equation
pair.  It applies this to the pole-corrected completed Riemann zeta function
and then restores the two explicit rational pole terms under distance cutoffs.
The next bridge is a quantitative reciprocal-Gamma bound converting completed
function bounds into bounds for the ordinary zeta and Dirichlet L-functions.
See `MIGRATION_STEP_42.md` and `audit/STEP42_STATUS.md`.

## Step 43 — reciprocal Gamma and ordinary zeta growth

Euler's integral bounds `Gamma` uniformly on positive vertical strips.
Reflection and the complex sine exponential bound then control the reciprocal
`Gammaℝ` factor on the zeta contour strip. Combined with Step 42, this proves
exponential vertical growth for ordinary Riemann zeta away from its pole.
The completed Dirichlet L-function and the odd Gamma factor remain before
the full critical-strip growth interface can be discharged.
See `MIGRATION_STEP_43.md` and `audit/STEP43_STATUS.md`.

## Step 44 — completed Dirichlet L strip bounds

The trusted layer proves uniform strip bounds for strong FE-pair Mellin
transforms and hence for completed odd Hurwitz terms. Combining these with
Step 42's even terms and mathlib's finite Hurwitz formula gives a uniform
bound for the actual completed Dirichlet L-function of a primitive real
character with modulus greater than one. The shifted odd Gamma factor is the
remaining bridge to ordinary Dirichlet L growth.
See `MIGRATION_STEP_44.md` and `audit/STEP44_STATUS.md`.

## Step 45 — shifted Gamma and unconditional contour shift

The trusted layer bounds reciprocal Gamma across real part one by combining
compactness with Gamma recurrence and reflection. This controls the odd
Dirichlet Gamma factor, converts Step 44's completed L bound to ordinary L
growth, and discharges the remaining critical-strip growth interface.
Consequently the exact infinite Lemma 5.7 contour shift holds for primitive
real characters of modulus greater than one. The shifted-integral error
estimate under Assumption (A) is the next analytic obligation.
See `MIGRATION_STEP_45.md` and `audit/STEP45_STATUS.md`.

## Step 46 — shifted-integral Gaussian envelope

The trusted layer isolates the exact `D⁻²` Gaussian factor on the shifted
vertical line and proves an unconditional norm envelope for that integral.
A separate sub-Gaussian pointwise condition gives an explicit Gaussian
moment bound, but that condition has not been proved for the actual zeta/L
factor. The final small-error estimate also needs a proof that `L(1,χ)` is
nonnegative before Assumption (A) can bound its residue correction.
See `MIGRATION_STEP_46.md` and `audit/STEP46_STATUS.md`.

## Step 47 — positivity at one and Assumption-(A) residue bound

The trusted layer proves positivity of the genuine `L(1,χ)` for primitive
real characters with modulus greater than one. It follows that Assumption
(A) bounds the absolute residue correction. Combining this with Step 46
reduces the analytic error to one explicit Gaussian-weighted shifted
integral; its required smallness is still unproved.
See `MIGRATION_STEP_47.md` and `audit/STEP47_STATUS.md`.

## Step 48 — explicit residue-error budget

For `log D ≥ 2`, the trusted layer proves that the absolute residue
correction is no more than `(1/32) D/φ(D)`. It also proves that this
logarithmic condition holds for all sufficiently large moduli. An equally
small bound for the shifted integral would now finish the analytic-error
budget; that integral estimate is still open.
See `MIGRATION_STEP_48.md` and `audit/STEP48_STATUS.md`.

## Step 49 — quadratic Gaussian moment

The trusted layer proves an explicit Gaussian moment bound for a quadratic
pointwise growth estimate on the undamped shifted-line factor. This yields
a quantitative bound for the actual shifted integral under that separate
analytic input. The input and the necessary modulus dependence of its
coefficient remain unproved.
See `MIGRATION_STEP_49.md` and `audit/STEP49_STATUS.md`.

## Step 50 — conductor-linear growth suffices eventually

The trusted layer shows that any quadratic left-line growth bound with
coefficient at most `D` makes Step 49's Gaussian estimate small enough for
the full analytic-error budget once `D` is sufficiently large. This is a
uniform sufficient-condition theorem; the actual zeta/L growth bound is
still unproved.
See `MIGRATION_STEP_50.md` and `audit/STEP50_STATUS.md`.

## Steps 51–57 — unconditional growth and Lemma 5.7 closure

Steps 51–54 derive an Abel representation and critical-line bounds for the
actual primitive-character L-function. Step 55 proves the zeta-factor bound
and the unconditional infinite contour shift, with a quadratic bound on the
shifted line. Step 56 feeds this into the Gaussian moment to prove the error
budget for sufficiently large moduli. Finally, Step 57 corrects the target to
reflect the paper's standing sufficiently-large-modulus convention from §2
and proves `Lemma57Target` at constant `1/16` under Assumption (A), with
the explicit threshold `D₀ = 3^10,000,000`. The proof exposes this witness in
`lemma57_one_sixteenth_at_explicit_threshold`; it is a closed, computable natural
number, though intentionally not expanded to its enormous decimal representation.

See `MIGRATION_STEP_57.md`, `audit/STEP57_STATUS.md`, and the paper-by-paper
ledger in `progress.md`. The complete project and audit regression checks
passed on Lean 4.30.0.


Step130临时进展：Lemma3.4的实际系数与均值基础已归档（31标准公理接口、4实际对象例子）。证明了实际二十重卷积到标准τ40的上界、τ40²≤τ1600、带权调和数界、原始Ψ上X1/X2在1≤x≤D80的统一均方界及可积性。完整B均方界与异常字符计数仍未证明；未修改项目Lean源文件，账本保持20/1/30。详见[audit/STEP130_STATUS.md](audit/STEP130_STATUS.md)。
