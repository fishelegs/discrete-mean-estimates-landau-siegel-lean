import Lake
open Lake DSL

package «zhang_ls» where
  -- 张益唐 Landau–Siegel 论文 (arXiv:2211.02515) 的形式化蓝图
  -- 目标：把论文的依赖图固化为 Lean 定理签名，便于独立、累积地填充与核验。
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`weak.mathlib.safeAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

@[default_target]
lean_lib «ZhangLS» where
  globs := #[.andSubmodules `ZhangLS]
