import ZhangLS.Spec.PositiveGcdReindex
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
open ZhangLS.Spec
example : positiveGcdLift ⟨2,⟨(1,2),by decide⟩⟩=(2,4) := by decide
example : positiveGcdLift ⟨3,⟨(1,1),by decide⟩⟩=(3,3) := by decide
example (i:positiveGcdIndex) :
    Nat.gcd ((positiveGcdLift i).1:ℕ) ((positiveGcdLift i).2:ℕ)=(i.1:ℕ) :=
  positiveGcd_lift_gcd i
example (F:ℕ+×ℕ+→ℂ) (hF:Summable F) :
    (∑'m:ℕ+,∑'n:ℕ+,F (m,n))=
      ∑'d:ℕ+,∑'lk:{lk:ℕ+×ℕ+ // Nat.Coprime (lk.1:ℕ) (lk.2:ℕ)},
        F (d*lk.val.1,d*lk.val.2) := positiveGcd_nested_tsum F hF
-- GENERATED AXIOM CHECKS
#print axioms ZhangLS.Spec.positiveGcdIndex
#print axioms ZhangLS.Spec.positiveGcdLift
#print axioms ZhangLS.Spec.positiveGcd_lift_gcd
#print axioms ZhangLS.Spec.positiveGcd_lift_injective
#print axioms ZhangLS.Spec.positiveGcd_lift_surjective
#print axioms ZhangLS.Spec.positiveGcdEquiv
#print axioms ZhangLS.Spec.positiveGcd_tsum_reindex
#print axioms ZhangLS.Spec.positiveGcd_nested_tsum
#print axioms ZhangLS.Spec.positiveGcd_scaled_ratio
