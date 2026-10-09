import FixedQuadratic.ArithmeticErrors
open FixedQuadratic
-- The exact logarithmic lower theorem exports two Q costs, not one.
example {m : ℕ} (q C : ℝ) (R M : Fin m → ℝ) (e : Fin m → ℕ) (z : ℂ)
    (hq : 0 < q) (hC : 0 < C) (hR : ∀ i, 0 < R i) (hM : ∀ i, 0 < M i)
    (hz : z ≠ 0)
    (hp : (∏ i, (R i)^e i) ≤ q^2*C*(∏ i, (M i)^e i)*‖z‖) :
    -Real.log q-Real.log C-(∑ i, (e i : ℝ)*Real.log (M i))+
      (∑ i, (e i : ℝ)*Real.log (R i)) ≤ Real.log ‖z‖ := by
  exact logarithmic_norm_product_lower q C R M e z hq hC hR hM hz hp
