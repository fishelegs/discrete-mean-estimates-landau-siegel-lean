import ZhangLS.Spec.Lemma61ReciprocalSeriesSplit

/-! # Actual reciprocal tail truncation for Lemma 6.1

The original n<T^3 finite sum and its n>=T^3 tail are split exactly.
Actual Gamma conductor growth cancels with actual P4, uniformly on the
wide high rectangle. Far-left and both horizontal tail integrals, the
actual local Cauchy relation and the original-left tail error are proved.
The full Lemma61Target remains unproved: finite polynomial error-line
shift, full horizontal edges and final constants/thresholds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def lemma61ActualReciprocalTailIntegrand {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s w : ℂ) : ℂ :=
  lemma23DirichletZ ψ (s + w) *
    (∑' n : ℕ, lemma61ReciprocalTailTerm D ψ⁻¹ (1 - s - w) n) *
    exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) * lemma57OmegaOne D w / w

lemma lemma61_reciprocal_far_left_term_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hL : 3 ≤ lemma23PaperL D)
    {s w : ℂ} (hs : s.re ≤ 1) (hw : w.re ≤ -4) (n : ℕ) :
    ‖lemma61ReciprocalTailTerm D ψ (1 - s - w) n‖ *
      Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) ≤
        ((n : ℝ) ^ 2)⁻¹ * Real.exp ((w.re + 6) * Real.log (lemma56PaperT D)) := by
  by_cases hn0 : n = 0
  · simp [hn0,lemma61ReciprocalTailTerm]
  by_cases hcut : lemma56PaperT D ^ 3 ≤ (n : ℝ)
  swap
  · simp only [lemma61ReciprocalTailTerm,if_neg hcut,norm_zero,zero_mul]
    positivity
  have hnr : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have ht := lemma61_T_log_bounds hL
  have ht0 : 0 ≤ Real.log (lemma56PaperT D) := by linarith only [ht.1,hL]
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
  have hlog : 3 * Real.log (lemma56PaperT D) ≤ Real.log (n : ℝ) := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log
      (pow_pos (Real.exp_pos _) 3) hcut
  have he : -(1 - s - w).re = s.re + w.re - 1 := by simp; ring
  have hpe : (s.re + w.re - 1) * Real.log (n : ℝ) -
      2 * w.re * Real.log (lemma56PaperT D) ≤
      -2 * Real.log (n : ℝ) + (w.re + 6) * Real.log (lemma56PaperT D) := by
    have h1 := mul_le_mul_of_nonneg_right hs hnlog
    have h2 := mul_le_mul_of_nonpos_left hlog (by linarith only [hw] : w.re + 2 ≤ 0)
    nlinarith only [h1,h2]
  have hnexp : ((n : ℝ) ^ 2)⁻¹ = Real.exp (-2 * Real.log (n : ℝ)) := by
    rw [show -2 * Real.log (n : ℝ) = -(2 * Real.log (n : ℝ)) by ring,
      Real.exp_neg,show 2 * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hnr 2)]
  unfold lemma61ReciprocalTailTerm
  rw [if_pos hcut,lemma44_norm_LSeries_term_eq_real_exp _ _ hn0,he]
  calc
    _ ≤ Real.exp ((s.re + w.re - 1) * Real.log (n : ℝ)) *
        Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) := by
      have hp := ψ.norm_le_one (n : ZMod p)
      nlinarith only [mul_le_mul_of_nonneg_right hp (Real.exp_nonneg ((s.re + w.re - 1) * Real.log (n : ℝ))),
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg ((s.re + w.re - 1) * Real.log (n : ℝ))))
          (Real.exp_nonneg (-2 * w.re * Real.log (lemma56PaperT D)))]
    _ ≤ _ := by
      rw [hnexp,← Real.exp_add,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [hpe]

lemma lemma61_reciprocal_far_left_sum_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hL : 3 ≤ lemma23PaperL D)
    {s w : ℂ} (hs : s.re ≤ 1) (hw : w.re ≤ -4) :
    ‖∑' n : ℕ, lemma61ReciprocalTailTerm D ψ (1 - s - w) n‖ *
      Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) ≤
        lemma44InverseSquareMass * Real.exp ((w.re + 6) * Real.log (lemma56PaperT D)) := by
  have hz : 1 < (1 - s - w).re := by simp only [sub_re,one_re]; linarith only [hs,hw]
  have hnorm := summable_norm_iff.mpr (lemma61_reciprocal_tail_summable (D := D) ψ hz)
  have hscaled := hnorm.mul_right (Real.exp (-2 * w.re * Real.log (lemma56PaperT D)))
  have hmajor := lemma44_inverse_square_summable.mul_right
    (Real.exp ((w.re + 6) * Real.log (lemma56PaperT D)))
  calc
    _ ≤ (∑' n : ℕ, ‖lemma61ReciprocalTailTerm D ψ (1 - s - w) n‖) *
        Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) :=
      mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hnorm) (Real.exp_nonneg _)
    _ = ∑' n : ℕ, ‖lemma61ReciprocalTailTerm D ψ (1 - s - w) n‖ *
        Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) := (tsum_mul_right).symm
    _ ≤ ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ * Real.exp ((w.re + 6) * Real.log (lemma56PaperT D)) :=
      hscaled.tsum_le_tsum (lemma61_reciprocal_far_left_term_bound ψ hL hs hw) hmajor
    _ = _ := by rw [tsum_mul_right]; rfl

lemma lemma61_far_left_exponent_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    (-(lemma23PaperL D ^ 9) + 6) * Real.log (lemma56PaperT D) ≤
      -(lemma23PaperL D ^ 10) / 2 := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 3
  have h39 := pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num : 3 ≤ 9)
  have h9 : 12 ≤ lemma23PaperL D ^ 9 := by norm_num at h3; linarith only [h3,h39]
  have ht := lemma61_T_log_bounds hL
  have ht0 : 0 ≤ Real.log (lemma56PaperT D) := by linarith only [ht.1,hL]
  calc
    _ ≤ (-(lemma23PaperL D ^ 9) / 2) * Real.log (lemma56PaperT D) :=
      mul_le_mul_of_nonneg_right (by linarith only [h9]) ht0
    _ ≤ (-(lemma23PaperL D ^ 9) / 2) * lemma23PaperL D :=
      mul_le_mul_of_nonpos_left ht.1 (by linarith only [pow_nonneg h0.le 9])
    _ = _ := by ring

lemma lemma61_actual_far_left_tail_point_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma61ActualReciprocalTailIntegrand (D := D) ψ s
      (-((lemma23PaperL D ^ 9 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      lemma44InverseSquareMass * Real.exp (2 + 4 * Real.pi - lemma23PaperL D ^ 10 / 2) *
        Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
  let w : ℂ := -((lemma23PaperL D ^ 9 : ℝ) : ℂ) + (v : ℂ) * I
  have hre : w.re = -(lemma23PaperL D ^ 9) := by
    simp only [w,neg_re,add_re,ofReal_re,ofReal_im,mul_re,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
  have him : w.im = v := by
    simp only [w,neg_im,add_im,ofReal_re,ofReal_im,mul_im,I_re,I_im,mul_zero,mul_one,zero_add,add_zero,neg_zero]
  have h0 : 0 < lemma23PaperL D := by linarith
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 3
  have h39 := pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num : 3 ≤ 9)
  have h9 : 12 ≤ lemma23PaperL D ^ 9 := by norm_num at h3; linarith only [h3,h39]
  have hwre : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 := by rw [hre]; constructor <;> linarith only [h9]
  have hz := lemma61_actual_Z_P4_cancellation ψ hψ hL hs hwre (by simpa only [him] using hv)
  have ho := lemma61_large_shift_gaussian_bound hL hwre
  rw [him] at ho
  have hd := lemma61_large_shift_denominator_bound (w := w) (by rw [hre]; linarith only [h9])
  have ht := lemma61_reciprocal_far_left_sum_bound ψ⁻¹ hL
    (lemma61_region_real_parts hL hs).2.le (w := w) (by rw [hre]; linarith only [h9])
  have he := lemma61_far_left_exponent_bound hL
  have hm : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  unfold lemma61ActualReciprocalTailIntegrand
  change ‖lemma23DirichletZ ψ (s + w) * (∑' n : ℕ, lemma61ReciprocalTailTerm D ψ⁻¹ (1 - s - w) n) *
    exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) * lemma57OmegaOne D w / w‖ ≤ _
  calc
    _ = ‖lemma23DirichletZ ψ (s + w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ *
        ‖∑' n : ℕ, lemma61ReciprocalTailTerm D ψ⁻¹ (1 - s - w) n‖ * ‖lemma57OmegaOne D w‖ * ‖w‖⁻¹ := by
      simp only [div_eq_mul_inv,norm_mul,norm_inv]
      ring
    _ ≤ (Real.exp (1 + 4 * Real.pi) * Real.exp (-2 * w.re * Real.log (lemma56PaperT D))) *
        ‖∑' n : ℕ, lemma61ReciprocalTailTerm D ψ⁻¹ (1 - s - w) n‖ *
        (Real.exp 1 * Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) * 1 := by
      gcongr
    _ = Real.exp (2 + 4 * Real.pi) *
        (‖∑' n : ℕ, lemma61ReciprocalTailTerm D ψ⁻¹ (1 - s - w) n‖ *
          Real.exp (-2 * w.re * Real.log (lemma56PaperT D))) *
        Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
      rw [show 2 + 4 * Real.pi = (1 + 4 * Real.pi) + 1 by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ Real.exp (2 + 4 * Real.pi) * (lemma44InverseSquareMass *
        Real.exp ((w.re + 6) * Real.log (lemma56PaperT D))) *
        Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) := by gcongr
    _ ≤ Real.exp (2 + 4 * Real.pi) * (lemma44InverseSquareMass *
        Real.exp (-(lemma23PaperL D ^ 10) / 2)) *
        Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
      gcongr
      simpa only [hre] using he
    _ = _ := by
      rw [show 2 + 4 * Real.pi - lemma23PaperL D ^ 10 / 2 =
        (2 + 4 * Real.pi) + (-(lemma23PaperL D ^ 10) / 2) by ring]
      simp only [Real.exp_add]
      ring

lemma lemma61_far_left_integral_exponent_absorption {L : ℝ} (hL : 3 ≤ L) :
    L ^ 20 * Real.exp (-(L ^ 10) / 2) ≤ Real.exp (-(L ^ 10) / 4) := by
  have h0 : 0 < L := by linarith
  have hlog : Real.log (L ^ 20) ≤ 20 * L := by
    rw [Real.log_pow]
    have h := Real.log_le_sub_one_of_pos h0
    norm_num
    linarith only [h]
  have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 5
  have h59 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by norm_num : 5 ≤ 9)
  have h9 : 80 ≤ L ^ 9 := by norm_num at h5; linarith only [h5,h59]
  have hd : 20 * L ≤ L ^ 10 / 4 := by
    nlinarith only [mul_le_mul_of_nonneg_right h9 h0.le]
  calc
    _ ≤ Real.exp (20 * L) * Real.exp (-(L ^ 10) / 2) :=
      mul_le_mul_of_nonneg_right (Real.le_exp_of_log_le hlog) (Real.exp_nonneg _)
    _ = Real.exp (20 * L + -(L ^ 10) / 2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hd])

lemma lemma61_actual_far_left_tail_integral_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61ActualReciprocalTailIntegrand (D := D) ψ s
          (-((lemma23PaperL D ^ 9 : ℝ) : ℂ) + (v : ℂ) * I) * I)‖ ≤
      (2 * lemma44InverseSquareMass * Real.exp (2 + 4 * Real.pi)) *
        Real.exp (-(lemma23PaperL D ^ 10) / 4) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hm : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hab : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20 := neg_le_self (pow_nonneg h0.le 20)
  have hp : ∀ v ∈ Set.uIoc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
      ‖lemma61ActualReciprocalTailIntegrand (D := D) ψ s
        (-((lemma23PaperL D ^ 9 : ℝ) : ℂ) + (v : ℂ) * I) * I‖ ≤
      lemma44InverseSquareMass * Real.exp (2 + 4 * Real.pi - lemma23PaperL D ^ 10 / 2) := by
    intro v hv
    rw [uIoc_of_le hab] at hv
    have hv' : |v| ≤ lemma23PaperL D ^ 20 := abs_le.mpr ⟨hv.1.le,hv.2⟩
    rw [norm_mul,norm_I,mul_one]
    apply (lemma61_actual_far_left_tail_point_bound ψ hψ hL hs hv').trans
    have he : Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg v)) (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity :
      0 ≤ lemma44InverseSquareMass * Real.exp (2 + 4 * Real.pi - lemma23PaperL D ^ 10 / 2))
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hp
  have hn := (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one
    (norm_nonneg (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      lemma61ActualReciprocalTailIntegrand (D := D) ψ s
        (-((lemma23PaperL D ^ 9 : ℝ) : ℂ) + (v : ℂ) * I) * I))).trans (by simpa only [one_mul] using hb)
  rw [← norm_mul] at hn
  apply hn.trans
  calc
    _ = (2 * lemma44InverseSquareMass * Real.exp (2 + 4 * Real.pi)) *
        (lemma23PaperL D ^ 20 * Real.exp (-(lemma23PaperL D ^ 10) / 2)) := by
      rw [abs_of_nonneg (by positivity),show 2 + 4 * Real.pi - lemma23PaperL D ^ 10 / 2 =
        (2 + 4 * Real.pi) + (-(lemma23PaperL D ^ 10) / 2) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma61_far_left_integral_exponent_absorption hL) (by positivity)

end ZhangLS.Spec
