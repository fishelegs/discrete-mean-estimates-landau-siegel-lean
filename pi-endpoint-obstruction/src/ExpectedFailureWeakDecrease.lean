import PiRowRank
import Mathlib.Tactic.FinCases
set_option autoImplicit false

-- A swap preserves the constant weight, so weak decrease alone is insufficient.
example : ∀ i : Fin 2, Equiv.swap (0 : Fin 2) 1 i = i := by
  apply PiRowRank.finite_injective_downward_eq_self (fun _ => 0)
    (Equiv.swap (0 : Fin 2) 1) ?_ (Equiv.swap (0 : Fin 2) 1).injective
  intro i _
  norm_num
