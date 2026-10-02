import ZhangLS.Spec.Lemma36IntegralMean

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

-- The new B is exactly the genuine centered condition-(3.6) expression.
example {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) :
    lemma36ActualB χ ψ =
      ‖∑ n ∈ Finset.Ioc (D^4) ⌊((D : ℝ)^8)⌋₊,
        lemma23ActualVarsigma χ n * ψ (n : ZMod q) *
          Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))‖ +
        ∫ t : ℝ in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8),
          ‖∑ n ∈ Finset.Ioc (D^4) ⌊t⌋₊,
            lemma23ActualVarsigma χ n * ψ (n : ZMod q) *
              Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))‖ / t := rfl

-- Both original endpoints remain visible, and the length is exactly 4 log D.
example {D : ℕ} (hL : 3 ≤ Real.log (D : ℝ)) :
    (∫ t : ℝ in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), 1/t) =
      4*Real.log (D : ℝ) :=
  lemma36_inverse_integral hL

-- The actual complex-valued tail is integrable, before taking norms or weights.
example {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) :
    IntegrableOn (fun t : ℝ => ∑ n ∈ Finset.Ioc (D^4) ⌊t⌋₊,
      lemma23ActualVarsigma χ n * ψ (n : ZMod q) *
        Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ)))
      (Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8)) :=
  lemma36_actual_X4_integrable χ ψ

-- The mean-to-integral step keeps the original actual primitive family.
example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (K : ℝ)
    (hmean : ∀ t : ℝ, t ≤ (D : ℝ)^8 →
      (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX4 χ ψ.2 t‖^2) ≤ K) :
    (∑ ψ ∈ lemma33ActualFamily D,
      (∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ.2 t‖/t)^2) ≤
      16*K*lemma23PaperL D^2 := by
  convert lemma36_actual_integral_mean_square_le χ hL K hmean using 1
  ring

-- The final second-moment statement expands B to its actual endpoint and integral.
example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (K : ℝ) (hK : 0 ≤ K)
    (hmean : ∀ t : ℝ, t ≤ (D : ℝ)^8 →
      (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX4 χ ψ.2 t‖^2) ≤ K) :
    (∑ ψ ∈ lemma33ActualFamily D,
      (‖lemma23ActualX4 χ ψ.2 ((D : ℝ)^8)‖ +
        ∫ t : ℝ in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ.2 t‖/t)^2) ≤
      34*K*lemma23PaperL D^2 :=
  lemma36_actual_B_mean_square_le χ hL K hK hmean

#print axioms lemma36_actual_X4_eq_partial_sum
#print axioms lemma36_actual_X4_measurable
#print axioms lemma36_actual_X4_partial_norm_bound
#print axioms lemma36_actual_X4_integrable
#print axioms lemma36_actual_X4_power_weighted_integrable
#print axioms lemma36_interval_parameters
#print axioms lemma36_inverse_integral
#print axioms lemma36_inverse_integrable
#print axioms lemma36_actual_weighted_integral_cauchy
#print axioms lemma36_actual_weighted_square_integral_mean_le
#print axioms lemma36_actual_integral_mean_square_le
#print axioms lemma36_actual_B_nonneg
#print axioms lemma36_actual_B_mean_square_le
end ZhangLS.Spec
