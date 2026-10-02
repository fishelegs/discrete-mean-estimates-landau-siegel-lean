import ZhangLS.Spec.Lemma153ZeroGlobal
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def lemma153ReducedCorrection (f A y t z : ℂ) : ℂ :=
  1+2*(t*(f-1)+f*A*y*(1-t))*z +
    (t^2*(1-f)-f*t+f*A*y*(t^2-1))*z^2

lemma lemma153_reduced_correction_identity (B lam K A y t z : ℂ) (hB : B ≠ 0) :
    lemma153ShiftedLocalCorrection B (B+lam*A*y*K) ((1-A*y)*K) K lam t z =
      lemma153ReducedCorrection (lam*K/B) A y t z := by
  rw [lemma153_shifted_local_polynomial B (B+lam*A*y*K) ((1-A*y)*K) K lam t z hB (by ring)]
  unfold lemma153ReducedCorrection
  field_simp
  ring

/-- Cancellation that makes the center perturbation summable. The mixed
normalized factor λK/B equals λ/((1−χy)Mprime), with every division justified. -/
lemma lemma153_mixed_ratio_reduction (a b u v y lam : ℂ)
    (hB : lemma153BaseClosed a b u v y ≠ 0)
    (hv : v = 0 ∨ v = 1 ∨ v = -1)
    (hu : 1-u ≠ 0) (hy : 1-y ≠ 0) (hvu : 1-v*u ≠ 0) (hvy : 1-v*y ≠ 0)
    (hay : 1-a*y ≠ 0) (hby : 1-b*y ≠ 0)
    (hau : 1-a*(v*u) ≠ 0) (hbu : 1-b*(v*u) ≠ 0) :
    lam*lemma152KappaRational a b y/lemma153BaseClosed a b u v y =
      lam/((1-v*y)*lemma152LocalCorrection a b u v y) := by
  rw [← lemma153_base_closed_correction_identity a b u v y hv hu hy hvu hvy hay hby hau hbu]
  unfold lemma152LocalRemoval lemma152KappaRational
  repeat' field_simp [hB,hu,hy,hvu,hvy,hay,hby,hau,hbu,mul_comm]
  all_goals ring

lemma lemma153_mixed_ratio_sub_one (B lam K A y : ℂ) (u : ℝ)
    (hA : ‖A‖ ≤ 2) (hy : ‖y‖ ≤ u)
    (he : ‖lam*((1-A*y)*K)/B-1‖ ≤ 10000*u) (hf : ‖lam*K/B‖ ≤ 10000) :
    ‖lam*K/B-1‖ ≤ 30000*u := by
  rw [show lam*K/B-1 = (lam*((1-A*y)*K)/B-1)+(lam*K/B)*A*y by ring]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hu : 0 ≤ u := (norm_nonneg _).trans hy
  have hh : ‖lam*K/B‖*‖A‖*‖y‖ ≤ 10000*2*u := by gcongr
  nlinarith only [he,hh]

lemma lemma153_norm_mul_difference (a b c d : ℂ) :
    ‖a*b-c*d‖ ≤ ‖a‖*‖b-d‖+‖a-c‖*‖d‖ := by
  rw [show a*b-c*d = a*(b-d)+(a-c)*d by ring]
  simpa only [norm_mul] using norm_add_le (a*(b-d)) ((a-c)*d)

lemma lemma153_norm_square_difference (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a^2-b^2‖ ≤ 2*‖a-b‖ := by
  rw [show a^2-b^2 = (a-b)*(a+b) by ring,norm_mul]
  have hh : ‖a+b‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
  nlinarith [norm_nonneg (a-b),mul_le_mul_of_nonneg_left hh (norm_nonneg (a-b))]

end ZhangLS.Spec
