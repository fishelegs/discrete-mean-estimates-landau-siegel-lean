import ZhangLS.Spec.CoprimeProfileAbelFormula
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
namespace ZhangLS.Spec.CoprimeProfileAbel
open Finset MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def profileWeight (K : ℝ → ℝ) (B t : ℝ) : ℝ := K (Real.log t / B) / t
noncomputable def profileWeightDeriv (K K' : ℝ → ℝ) (B t : ℝ) : ℝ :=
  (K' (Real.log t / B) / B - K (Real.log t / B)) / t ^ 2

noncomputable def weightedProfileSum (D : ℕ) (K : ℝ → ℝ) (B b : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp (b * B)⌋₊,
    (if n.Coprime D then (n.totient : ℝ) / (n : ℝ) ^ 2 else 0) * K (Real.log n / B)

lemma continuous_supported_endpoints {K : ℝ → ℝ} {a b : ℝ}
    (hK : Continuous K) (hsupport : Function.support K ⊆ Set.Icc a b) : K a = 0 ∧ K b = 0 := by
  have hclosed : IsClosed {t : ℝ | K t = 0} := isClosed_eq hK continuous_const
  have hl : Set.Iio a ⊆ {t : ℝ | K t = 0} := by
    intro t ht
    by_contra hn
    have hmem := hsupport hn
    exact (not_le_of_gt ht) hmem.1
  have hr : Set.Ioi b ⊆ {t : ℝ | K t = 0} := by
    intro t ht
    by_contra hn
    have hmem := hsupport hn
    exact (not_le_of_gt ht) hmem.2
  constructor
  · exact hclosed.closure_subset_iff.mpr hl (by simp [closure_Iio])
  · exact hclosed.closure_subset_iff.mpr hr (by simp [closure_Ioi])

lemma profileWeight_hasDerivAt (K K' : ℝ → ℝ) (hK : ∀ u, HasDerivAt K (K' u) u)
    {B t : ℝ} (hB : 0 < B) (ht : 0 < t) :
    HasDerivAt (profileWeight K B) (profileWeightDeriv K K' B t) t := by
  have hd := ((hK (Real.log t / B)).comp t ((Real.hasDerivAt_log ht.ne').div_const B)).div
    (hasDerivAt_id t) ht.ne'
  convert hd using 1
  unfold profileWeightDeriv
  dsimp
  field_simp

lemma profileWeightDeriv_continuousOn (K K' : ℝ → ℝ)
    (hK : Continuous K) (hK' : Continuous K') {B L R : ℝ} (hL : 0 < L) :
    ContinuousOn (profileWeightDeriv K K' B) (Set.Icc L R) := by
  have hlog : ContinuousOn (fun t => Real.log t / B) (Set.Icc L R) := by
    intro t ht
    exact ((Real.continuousAt_log (by linarith [ht.1])).div_const B).continuousWithinAt
  unfold profileWeightDeriv
  apply ContinuousOn.div
    (((hK'.comp_continuousOn hlog).div_const B).sub (hK.comp_continuousOn hlog))
    (continuous_id.pow 2).continuousOn
  intro t ht
  exact pow_ne_zero 2 (by dsimp at *; linarith [ht.1])

lemma profileWeightDeriv_bound (K K' : ℝ → ℝ) {B M0 M1 t : ℝ} (hB : 0 < B)
    (hK : |K (Real.log t / B)| ≤ M0) (hK' : |K' (Real.log t / B)| ≤ M1) :
    |profileWeightDeriv K K' B t| ≤ (M0 + M1 / B) / t ^ 2 := by
  unfold profileWeightDeriv
  rw [abs_div, abs_of_nonneg (sq_nonneg t)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  calc
    _ ≤ |K' (Real.log t / B) / B| + |K (Real.log t / B)| := by
      simpa using abs_sub_le (K' (Real.log t / B) / B) 0 (K (Real.log t / B))
    _ ≤ M1 / B + M0 := by
      apply add_le_add _ hK
      rw [abs_div, abs_of_pos hB]
      exact div_le_div_of_nonneg_right hK' hB.le
    _ = _ := by ring

/-- Exact logarithmic change of variables, retaining both real endpoints. -/
lemma profileWeight_integral (K K' : ℝ → ℝ) (hK : ∀ u, HasDerivAt K (K' u) u)
    {a b B : ℝ} (hB : 0 < B) (hab : a ≤ b) :
    (∫ t in Real.exp (a * B)..Real.exp (b * B), profileWeight K B t) =
      B * (∫ u in a..b, K u) := by
  let L := Real.exp (a * B)
  let R := Real.exp (b * B)
  have hLR : L ≤ R := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hB.le)
  have hLp : 0 < L := Real.exp_pos _
  have hlogd : ∀ t ∈ Set.uIcc L R, HasDerivAt (fun x => Real.log x / B) (t⁻¹ / B) t := by
    intro t ht
    rw [Set.uIcc_of_le hLR] at ht
    exact (Real.hasDerivAt_log (by linarith [ht.1])).div_const B
  have hlogc : ContinuousOn (fun t : ℝ => t⁻¹ / B) (Set.uIcc L R) := by
    rw [Set.uIcc_of_le hLR]
    apply ContinuousOn.div_const
    apply ContinuousOn.inv₀ continuous_id.continuousOn
    intro t ht
    dsimp at *
    linarith [ht.1]
  have hcK : Continuous K := continuous_iff_continuousAt.mpr (fun u => (hK u).continuousAt)
  have hs := intervalIntegral.integral_comp_mul_deriv hlogd hlogc hcK
  have hfunc : (fun x => (K ∘ (fun x => Real.log x / B)) x * (x⁻¹ / B)) =
      (fun x => B⁻¹ * profileWeight K B x) := by
    funext x
    unfold profileWeight
    simp only [Function.comp_apply, div_eq_mul_inv]
    ring
  rw [hfunc, intervalIntegral.integral_const_mul] at hs
  have ha : Real.log L / B = a := by dsimp [L]; rw [Real.log_exp]; field_simp
  have hb : Real.log R / B = b := by dsimp [R]; rw [Real.log_exp]; field_simp
  rw [ha, hb] at hs
  change (∫ t in L..R, profileWeight K B t) = _
  have hBne : B ≠ 0 := hB.ne'
  calc
    _ = B * (B⁻¹ * (∫ t in L..R, profileWeight K B t)) := by field_simp
    _ = _ := by rw [hs]

lemma weighted_term_eq (D n : ℕ) (K : ℝ → ℝ) (B : ℝ) :
    (if n.Coprime D then (n.totient : ℝ) / (n : ℝ) ^ 2 else 0) * K (Real.log n / B) =
      profileWeight K B n * coefficient D n := by
  unfold profileWeight coefficient
  by_cases hc : n.Coprime D
  · rw [if_pos hc, if_pos hc]
    simp only [div_eq_mul_inv, pow_two, mul_inv_rev]
    ring
  · rw [if_neg hc, if_neg hc, zero_mul, mul_zero]

lemma weightedProfileSum_eq_interval (D : ℕ) (K : ℝ → ℝ) {a b B : ℝ}
    (hB : 0 < B) (hsupport : Function.support K ⊆ Set.Icc a b) (hKa : K a = 0) :
    weightedProfileSum D K B b =
      ∑ n ∈ Finset.Ioc ⌊Real.exp (a * B)⌋₊ ⌊Real.exp (b * B)⌋₊,
        profileWeight K B n * coefficient D n := by
  unfold weightedProfileSum
  simp_rw [weighted_term_eq]
  symm
  apply Finset.sum_subset
  · intro n hn
    have hnI := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hnI.2⟩
  · intro n hn hnot
    have hnI := Finset.mem_Icc.mp hn
    have hnL : n ≤ ⌊Real.exp (a * B)⌋₊ := by
      by_contra hnl
      exact hnot (Finset.mem_Ioc.mpr ⟨by omega, hnI.2⟩)
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hnI.1
    have hnle : (n : ℝ) ≤ Real.exp (a * B) :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mp hnL
    have hlog : Real.log n / B ≤ a := by
      apply (div_le_iff₀ hB).mpr
      simpa only [Real.log_exp] using Real.log_le_log hnpos hnle
    have hzero : K (Real.log n / B) = 0 := by
      rcases lt_or_eq_of_le hlog with hlt | heq
      · by_contra hne
        exact (not_le_of_gt hlt) (hsupport hne).1
      · rw [heq, hKa]
    simp only [profileWeight, hzero, zero_div, zero_mul]

lemma logarithmic_window {a b B t : ℝ} (hB : 0 < B)
    (ht : t ∈ Set.Icc (Real.exp (a * B)) (Real.exp (b * B))) :
    Real.log t / B ∈ Set.Icc a b := by
  have htp : 0 < t := (Real.exp_pos _).trans_le ht.1
  constructor
  · apply (le_div_iff₀ hB).mpr
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) ht.1
  · apply (div_le_iff₀ hB).mpr
    simpa only [Real.log_exp] using Real.log_le_log htp ht.2

/-- Actual weighted Abel remainder identity for a C¹ compact profile. The
finite sum has an inclusive upper cutoff; compact support proves both endpoint
terms vanish rather than dropping them. -/
theorem weighted_abel_identity {D : ℕ} (K K' : ℝ → ℝ) {a b B : ℝ}
    (hB : 0 < B) (hab : a ≤ b)
    (hK : ∀ u, HasDerivAt K (K' u) u) (hK' : Continuous K')
    (hsupport : Function.support K ⊆ Set.Icc a b) :
    weightedProfileSum D K B b - mainConstant D * B * (∫ u in a..b, K u) =
      -(∫ t in Real.exp (a * B)..Real.exp (b * B),
        profileWeightDeriv K K' B t * (summatory D t - mainConstant D * t)) := by
  have hcK : Continuous K := continuous_iff_continuousAt.mpr (fun u => (hK u).continuousAt)
  have hends := continuous_supported_endpoints hcK hsupport
  have hLR : Real.exp (a * B) ≤ Real.exp (b * B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hB.le)
  have hf : ∀ t ∈ Set.Icc (Real.exp (a * B)) (Real.exp (b * B)),
      HasDerivAt (profileWeight K B) (profileWeightDeriv K K' B t) t := by
    intro t ht
    exact profileWeight_hasDerivAt K K' hK hB ((Real.exp_pos _).trans_le ht.1)
  have hfL : profileWeight K B (Real.exp (a * B)) = 0 := by
    unfold profileWeight
    rw [Real.log_exp, mul_div_cancel_right₀ a hB.ne', hends.1, zero_div]
  have hfR : profileWeight K B (Real.exp (b * B)) = 0 := by
    unfold profileWeight
    rw [Real.log_exp, mul_div_cancel_right₀ b hB.ne', hends.2, zero_div]
  have he := abel_remainder_identity D (Real.exp_pos _).le hLR
    (profileWeight K B) (profileWeightDeriv K K' B) hf
    (profileWeightDeriv_continuousOn K K' hcK hK' (Real.exp_pos _)) hfL hfR
  rw [← weightedProfileSum_eq_interval D K hB hsupport hends.1,
    profileWeight_integral K K' hK hB hab] at he
  simpa only [mul_assoc] using he

/-- A fully proved error in the actual profile and derivative bounds. -/
theorem weighted_abel_error {D : ℕ} (hD : 0 < D) (K K' : ℝ → ℝ)
    {a b B M0 M1 : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hB : 0 < B)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hK : ∀ u, HasDerivAt K (K' u) u) (hK' : Continuous K')
    (hsupport : Function.support K ⊆ Set.Icc a b)
    (hbound0 : ∀ u ∈ Set.Icc a b, |K u| ≤ M0)
    (hbound1 : ∀ u ∈ Set.Icc a b, |K' u| ≤ M1) :
    |weightedProfileSum D K B b - mainConstant D * B * (∫ u in a..b, K u)| ≤
      ((D.divisors.card : ℝ) * (1 + b * B) + 2) *
        (M0 + M1 / B) / Real.exp (a * B) := by
  have hcK : Continuous K := continuous_iff_continuousAt.mpr (fun u => (hK u).continuousAt)
  have hends := continuous_supported_endpoints hcK hsupport
  have hL : 1 ≤ Real.exp (a * B) := Real.one_le_exp_iff.mpr (mul_nonneg ha hB.le)
  have hLR : Real.exp (a * B) ≤ Real.exp (b * B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hB.le)
  have hf : ∀ t ∈ Set.Icc (Real.exp (a * B)) (Real.exp (b * B)),
      HasDerivAt (profileWeight K B) (profileWeightDeriv K K' B t) t := by
    intro t ht
    exact profileWeight_hasDerivAt K K' hK hB ((Real.exp_pos _).trans_le ht.1)
  have hfL : profileWeight K B (Real.exp (a * B)) = 0 := by
    unfold profileWeight
    rw [Real.log_exp, mul_div_cancel_right₀ a hB.ne', hends.1, zero_div]
  have hfR : profileWeight K B (Real.exp (b * B)) = 0 := by
    unfold profileWeight
    rw [Real.log_exp, mul_div_cancel_right₀ b hB.ne', hends.2, zero_div]
  have hdBound : ∀ t ∈ Set.Icc (Real.exp (a * B)) (Real.exp (b * B)),
      |profileWeightDeriv K K' B t| ≤ (M0 + M1 / B) / t ^ 2 := by
    intro t ht
    exact profileWeightDeriv_bound K K' hB
      (hbound0 _ (logarithmic_window hB ht)) (hbound1 _ (logarithmic_window hB ht))
  have he := abel_remainder_bound hD hL hLR (by positivity : 0 ≤ M0 + M1 / B)
    (profileWeight K B) (profileWeightDeriv K K' B) hf
    (profileWeightDeriv_continuousOn K K' hcK hK' (Real.exp_pos _)) hfL hfR hdBound
  rw [← weightedProfileSum_eq_interval D K hB hsupport hends.1,
    profileWeight_integral K K' hK hB hab, Real.log_exp] at he
  simpa only [mul_assoc] using he

/-- The original single-norm window, with B literally log P. -/
theorem original_window_abel_error {D : ℕ} (hD : 0 < D) (K K' : ℝ → ℝ)
    {P M0 M1 : ℝ} (hP : 1 < P) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hK : ∀ u, HasDerivAt K (K' u) u) (hK' : Continuous K')
    (hsupport : Function.support K ⊆ Set.Icc (251 / 500 : ℝ) (201 / 400))
    (hbound0 : ∀ u ∈ Set.Icc (251 / 500 : ℝ) (201 / 400), |K u| ≤ M0)
    (hbound1 : ∀ u ∈ Set.Icc (251 / 500 : ℝ) (201 / 400), |K' u| ≤ M1) :
    |weightedProfileSum D K (Real.log P) (201 / 400) -
      mainConstant D * Real.log P * (∫ u in (251 / 500 : ℝ)..(201 / 400), K u)| ≤
      ((D.divisors.card : ℝ) * (1 + (201 / 400) * Real.log P) + 2) *
        (M0 + M1 / Real.log P) / Real.exp ((251 / 500) * Real.log P) :=
  weighted_abel_error hD K K' (by norm_num) (by norm_num) (Real.log_pos hP)
    hM0 hM1 hK hK' hsupport hbound0 hbound1

end ZhangLS.Spec.CoprimeProfileAbel
