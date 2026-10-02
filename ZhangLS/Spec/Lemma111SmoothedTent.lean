import ZhangLS.Spec.Lemma111GaussianBounds

/-!
# The actual smoothed tent from Lemma 11.1

The tent is (2.28); both smoothed weights are precisely the integrals in §11.
The exponentially accurate region retains all four closed endpoints, while
all three transition neighborhoods in (11.3) are open.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ZhangLS.Spec

open MeasureTheory
open scoped Real

noncomputable def lemma111Tent (u : ℝ) : ℝ :=
  if u < 1 / 2 then 0
  else if u ≤ 251 / 500 then 500 * (u - 1 / 2)
  else if u ≤ 63 / 125 then 500 * (63 / 125 - u)
  else 0

noncomputable def lemma111SmoothedOne (D : ℕ) (y : ℝ) : ℝ :=
  -500 * (∫ z in (1 / 2 : ℝ)..(251 / 500 : ℝ),
    zhangGaussianWeight D (lemma23PaperP D ^ z / y)) +
  500 * (∫ z in (251 / 500 : ℝ)..(63 / 125 : ℝ),
    zhangGaussianWeight D (lemma23PaperP D ^ z / y))

/-- The complementary shifted cutoff, recorded to retain the actual §11
normalization. It is not a premise of Lemma 11.1. -/
noncomputable def lemma111SmoothedTwo (D : ℕ) (y : ℝ) : ℝ :=
  -500 * (∫ z in (62 / 125 : ℝ)..(249 / 500 : ℝ),
    zhangGaussianWeight D (lemma23PaperP D ^ z * (D : ℝ) * lemma23PaperL D ^ 519 / y)) +
  500 * (∫ z in (249 / 500 : ℝ)..(1 / 2 : ℝ),
    zhangGaussianWeight D (lemma23PaperP D ^ z * (D : ℝ) * lemma23PaperL D ^ 519 / y))

noncomputable def lemma111EtaPlus (D : ℕ) : ℝ :=
  Real.exp (lemma23PaperL D ^ (-10 : ℤ))

noncomputable def lemma111EtaMinus (D : ℕ) : ℝ :=
  Real.exp (-(lemma23PaperL D ^ (-10 : ℤ)))

def Lemma111Interior (D : ℕ) (y : ℝ) : Prop :=
  y ∈ Set.Icc (lemma23PaperP D ^ (1 / 2 : ℝ) * lemma111EtaPlus D)
    (lemma23PaperP D ^ (251 / 500 : ℝ) * lemma111EtaMinus D) ∪
  Set.Icc (lemma23PaperP D ^ (251 / 500 : ℝ) * lemma111EtaPlus D)
    (lemma23PaperP D ^ (63 / 125 : ℝ) * lemma111EtaMinus D)

def Lemma111Transition (D : ℕ) (y : ℝ) : Prop :=
  y ∈ Set.Ioo (lemma23PaperP D ^ (1 / 2 : ℝ) * lemma111EtaMinus D)
    (lemma23PaperP D ^ (1 / 2 : ℝ) * lemma111EtaPlus D) ∪
  Set.Ioo (lemma23PaperP D ^ (251 / 500 : ℝ) * lemma111EtaMinus D)
    (lemma23PaperP D ^ (251 / 500 : ℝ) * lemma111EtaPlus D) ∪
  Set.Ioo (lemma23PaperP D ^ (63 / 125 : ℝ) * lemma111EtaMinus D)
    (lemma23PaperP D ^ (63 / 125 : ℝ) * lemma111EtaPlus D)

def Lemma111Target : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ y : ℝ,
    (Lemma111Interior D y →
      |lemma111Tent (Real.log y / Real.log (lemma23PaperP D)) -
        lemma111SmoothedOne D y| ≤ C * Real.exp (-c * lemma23PaperL D ^ 10)) ∧
    (Lemma111Transition D y →
      |lemma111Tent (Real.log y / Real.log (lemma23PaperP D)) -
        lemma111SmoothedOne D y| ≤ C * lemma23PaperL D ^ (-10 : ℤ))

lemma lemma111_tent_second_difference (u : ℝ) :
    lemma111Tent u =
      500 * (max (63 / 125 - u) 0 - 2 * max (251 / 500 - u) 0 + max (1 / 2 - u) 0) := by
  unfold lemma111Tent
  split_ifs with h₁ h₂ h₃
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    ring

lemma lemma111_weight_log_coordinate {D : ℕ} (hD : 1 < D)
    {y : ℝ} (hy : 0 < y) (z : ℝ) :
    zhangGaussianWeight D (lemma23PaperP D ^ z / y) =
      lemma111Profile D (z - Real.log y / Real.log (lemma23PaperP D)) := by
  have hL : lemma23PaperL D ≠ 0 := (Real.log_pos (by exact_mod_cast hD)).ne'
  unfold lemma111Profile
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have harg : lemma23PaperP D ^ z / y =
      Real.exp (Real.log (lemma23PaperP D) * z - Real.log y) := by
    rw [Real.rpow_def_of_pos hP, Real.exp_sub, Real.exp_log hy]
  rw [harg]
  congr 2
  unfold lemma23PaperP
  rw [Real.log_exp]
  field_simp

/-- Exact identity for the actual (untruncated) smoothing weight. -/
lemma lemma111_smoothed_second_difference {D : ℕ} (hD : 1 < D)
    {y : ℝ} (hy : 0 < y) :
    lemma111SmoothedOne D y =
      let u := Real.log y / Real.log (lemma23PaperP D)
      500 * (lemma111Primitive D (63 / 125 - u) -
        2 * lemma111Primitive D (251 / 500 - u) + lemma111Primitive D (1 / 2 - u)) := by
  unfold lemma111SmoothedOne
  simp_rw [lemma111_weight_log_coordinate hD hy]
  rw [lemma111_integral_profile hD, lemma111_integral_profile hD]
  ring

lemma lemma111_second_difference_error {a b c a' b' c' E : ℝ}
    (ha : |a - a'| ≤ E) (hb : |b - b'| ≤ E) (hc : |c - c'| ≤ E) :
    |500 * (c - 2 * b + a) - 500 * (c' - 2 * b' + a')| ≤ 2000 * E := by
  have heq : 500 * (c - 2 * b + a) - 500 * (c' - 2 * b' + a') =
      500 * ((c - c') + (-(2 * (b - b'))) + (a - a')) := by ring
  rw [heq, abs_mul]
  norm_num
  calc
    500 * |(c - c') + (-(2 * (b - b'))) + (a - a')| ≤
        500 * (|c - c'| + 2 * |b - b'| + |a - a'|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _ ≤ |(c - c') + (-(2 * (b - b')))| + |a - a'| := abs_add_le _ _
        _ ≤ (|c - c'| + |-(2 * (b - b'))|) + |a - a'| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_neg, abs_mul]; norm_num
    _ ≤ _ := by linarith

/-- Stronger than the boundary estimate (11.3): a uniform `4000 L⁻²⁴`
error bound holds for every positive `y`, including all three breakpoints. -/
lemma lemma111_smoothed_uniform_bound {D : ℕ} (hD : 1 < D)
    {y : ℝ} (hy : 0 < y) :
    |lemma111Tent (Real.log y / Real.log (lemma23PaperP D)) -
      lemma111SmoothedOne D y| ≤ 4000 / lemma111Scale D := by
  rw [abs_sub_comm, lemma111_tent_second_difference, lemma111_smoothed_second_difference hD hy]
  dsimp only
  have h := lemma111_second_difference_error
    (lemma111_primitive_error_uniform hD (1 / 2 - Real.log y / Real.log (lemma23PaperP D)))
    (lemma111_primitive_error_uniform hD (251 / 500 - Real.log y / Real.log (lemma23PaperP D)))
    (lemma111_primitive_error_uniform hD (63 / 125 - Real.log y / Real.log (lemma23PaperP D)))
  convert h using 1
  ring

end ZhangLS.Spec
