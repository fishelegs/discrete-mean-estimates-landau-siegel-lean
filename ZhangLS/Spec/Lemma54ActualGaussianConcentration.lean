import ZhangLS.Spec.Lemma54CentralWindow

/-! # Actual paper scales in the Gaussian concentration estimates -/

namespace ZhangLS.Spec

open MeasureTheory Set Filter

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma54_window_gaussian_damping {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    Real.exp (-((Real.pi * lemma23PaperL D ^ 405 / lemma53PaperScale D) ^ 2) / 2) ≤
      Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have hLpos : 0 < lemma23PaperL D := by linarith
  have heq : Real.pi * lemma23PaperL D ^ 405 / lemma53PaperScale D =
      Real.pi * lemma23PaperL D ^ 5 := by
    unfold lemma53PaperScale
    rw [show (405 : ℕ) = 5 + 400 by norm_num, pow_add]
    field_simp
  rw [heq]
  apply Real.exp_le_exp.mpr
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hp : 0 ≤ lemma23PaperL D ^ 10 := by positivity
  have heq2 : (Real.pi * lemma23PaperL D ^ 5) ^ 2 =
      Real.pi ^ 2 * lemma23PaperL D ^ 10 := by ring
  rw [heq2]
  nlinarith [mul_le_mul_of_nonneg_right hpi hp]

theorem lemma54_window_compl_gap (D : ℕ) {x : ℝ}
    (hx : x ∈ (lemma54PaperWindow D)ᶜ) :
    lemma23PaperL D ^ 405 ≤ |x - lemma51PaperT0 D| := by
  by_contra hh
  have ha := abs_lt.mp (lt_of_not_ge hh)
  apply hx
  change lemma51PaperT0 D - lemma23PaperL D ^ 405 ≤ x ∧
    x ≤ lemma51PaperT0 D + lemma23PaperL D ^ 405
  constructor <;> linarith

theorem lemma54_actual_gaussian_exterior_mass {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hgap : ∀ x ∈ S, lemma23PaperL D ^ 405 ≤ |x - lemma51PaperT0 D|) :
    (∫ x : ℝ in S, lemma54PaperGaussian D x) ≤
      2 * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have hB : 0 < lemma53PaperScale D := lt_of_lt_of_le (by norm_num) (lemma54_scale_ge_one hL)
  apply (lemma54_gaussian_exterior_mass hB
    (pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 405) hS hgap).trans
  exact mul_le_mul_of_nonneg_left (lemma54_window_gaussian_damping hL) (by norm_num)

theorem lemma54_actual_gaussian_exterior_quadratic_mass {D : ℕ}
    (hL : 2000 ≤ lemma23PaperL D) {S : Set ℝ} (hS : MeasurableSet S)
    (hgap : ∀ x ∈ S, lemma23PaperL D ^ 405 ≤ |x - lemma51PaperT0 D|) :
    (∫ x : ℝ in S, (1 + x ^ 2) * lemma54PaperGaussian D x) ≤
      144 * lemma23PaperL D ^ 1838 * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  let B := lemma53PaperScale D
  let t := lemma51PaperT0 D
  have hB1 : 1 ≤ B := lemma54_scale_ge_one hL
  have hB : 0 < B := by linarith
  have ht1 : 1 ≤ t := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB1
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hdiv : 8 * B ^ 2 / Real.pi ^ 2 ≤ 8 * B ^ 2 := div_le_self (by positivity) hpi
  have hcoef : 8 * (1 + t ^ 2) * (1 + 8 * B ^ 2 / Real.pi ^ 2) ≤
      144 * t ^ 2 * B ^ 2 := by
    calc
      _ ≤ 8 * (2 * t ^ 2) * (9 * B ^ 2) := by
        apply mul_le_mul
        · nlinarith
        · linarith
        · positivity
        · positivity
      _ = _ := by ring
  have hpow : t ^ 2 * B ^ 2 = lemma23PaperL D ^ 1838 := by
    dsimp [t, B, lemma51PaperT0, lemma53PaperScale]
    ring
  calc
    _ ≤ (8 * (1 + t ^ 2) * (1 + 8 * B ^ 2 / Real.pi ^ 2)) *
        Real.exp (-((Real.pi * lemma23PaperL D ^ 405 / B) ^ 2) / 2) :=
      lemma54_gaussian_exterior_quadratic_mass hB
        (pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 405) hS hgap
    _ ≤ (144 * t ^ 2 * B ^ 2) * Real.exp (-(lemma23PaperL D ^ 10) / 2) :=
      mul_le_mul hcoef (lemma54_window_gaussian_damping hL) (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [mul_assoc (144 : ℝ), hpow]

theorem lemma54_actual_gaussian_window_mass {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) :
    |(∫ x : ℝ in lemma54PaperWindow D, lemma54PaperGaussian D x) - 1| ≤
      2 * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have hi := lemma54_actual_gaussian_mass hD
  have ha := integral_add_compl (lemma54_window_measurable D) hi.1
  rw [hi.2] at ha
  have hn : 0 ≤ ∫ x : ℝ in (lemma54PaperWindow D)ᶜ, lemma54PaperGaussian D x := by
    apply integral_nonneg
    intro x
    exact (lemma54_gaussian_density_pos (lemma53_scale_pos hD) _ _).le
  have hb := lemma54_actual_gaussian_exterior_mass hL (lemma54_window_measurable D).compl
    (fun x hx => lemma54_window_compl_gap D hx)
  rw [abs_of_nonpos (by linarith)]
  linarith

end ZhangLS.Spec
