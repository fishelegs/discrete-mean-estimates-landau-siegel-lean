import ZhangLS.Spec.Lemma53LargeRange

/-! # The faithful original target of Lemma 5.3

The actual inverse Mellin definition, the exact oscillatory identity,
both complete original x ranges, and one uniform constant and threshold.
-/

namespace ZhangLS.Spec

open Complex Filter

set_option maxHeartbeats 1000000

noncomputable def lemma53ErrorConstant : ℝ :=
  lemma53SmallErrorConstant + 2 + Real.exp 1 + Real.sqrt Real.pi * Real.exp 2

theorem lemma53_error_constant_bounds :
    0 < lemma53ErrorConstant ∧ 1 ≤ lemma53ErrorConstant ∧
      lemma53SmallErrorConstant ≤ lemma53ErrorConstant ∧
      2 + Real.exp 1 ≤ lemma53ErrorConstant ∧
      Real.sqrt Real.pi * Real.exp 2 ≤ lemma53ErrorConstant := by
  unfold lemma53ErrorConstant lemma53SmallErrorConstant
  have he := Real.exp_pos 1
  have hp : 0 ≤ Real.sqrt Real.pi * Real.exp 2 := by positivity
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

def Lemma53AtConstants (C k : ℝ) (D₀ : ℕ) : Prop :=
  ∀ D : ℕ, D₀ ≤ D → ∀ x : ℝ, 0 < x →
    (x ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ) →
      ‖lemma53PaperDelta D x -
        lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ ≤
        C * lemma44PaperAlpha D *
          ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ +
        C * Real.exp (-k * lemma23PaperL D ^ 10)) ∧
    (lemma51PaperT0 D ^ (51 / 50 : ℝ) < x →
      ‖lemma53PaperDelta D x‖ ≤
        C * (Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) +
          Real.exp (-(x ^ (99 / 100 : ℝ)) / lemma53PaperScale D)))

def Lemma53Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℝ, 0 < k ∧ ∃ D₀ : ℕ, Lemma53AtConstants C k D₀

theorem lemma53_proved : Lemma53Target := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop 2000))
  obtain ⟨hC0, hC1, hCs, hCl, hCr⟩ := lemma53_error_constant_bounds
  refine ⟨lemma53ErrorConstant, hC0, 1 / 2, by norm_num, max N 2, ?_⟩
  intro D hD x hx
  have hD' : 1 < D := lt_of_lt_of_le (by norm_num : 1 < 2) ((le_max_right N 2).trans hD)
  have hL := hN D ((le_max_left N 2).trans hD)
  constructor
  · intro hxhi
    have he := lemma53_small_range_estimate hD' hL hx hxhi
    apply he.trans
    have ha : 0 ≤ lemma44PaperAlpha D := by
      unfold lemma44PaperAlpha lemma23PaperP
      rw [Real.log_exp]
      positivity
    have hm := mul_le_mul_of_nonneg_right hC1
      (mul_nonneg ha (norm_nonneg
        (lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)))))
    have hs := mul_le_mul_of_nonneg_right hCs (Real.exp_nonneg (-(lemma23PaperL D ^ 10) / 2))
    have hex : -(lemma23PaperL D ^ 10) / 2 = -(1 / 2 : ℝ) * lemma23PaperL D ^ 10 := by ring
    rw [← hex]
    nlinarith only [hm, hs]
  · intro hxhi
    apply (lemma53_large_range_estimate hD' hL hx hxhi).trans
    have hl := mul_le_mul_of_nonneg_right hCl
      (Real.exp_nonneg (-((lemma53PaperScale D * Real.log x / 100) ^ 2)))
    have hr := mul_le_mul_of_nonneg_right hCr
      (Real.exp_nonneg (-(x ^ (99 / 100 : ℝ)) / lemma53PaperScale D))
    nlinarith only [hl, hr]

end ZhangLS.Spec
