import Lake
open Lake DSL
package DeterminantValidation where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLeanArgs := #["-j1", "-M4096"]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI
lean_lib PrimeNumberTheoremAnd
lean_lib EarlyDeterminantAdapter
