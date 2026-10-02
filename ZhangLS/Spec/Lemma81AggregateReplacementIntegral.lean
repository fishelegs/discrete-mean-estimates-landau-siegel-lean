import ZhangLS.Spec.Lemma81AggregateReplacementPointwise

/-! # Integrated actual aggregate replacement in Lemma 8.1

Finite sum/integral interchange, all actual contour integrability, the
original Gaussian mass and both proved moments yield the required uniform
P²L^-78 replacement error. No aggregate error bound is assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory
open scoped Real Classical
set_option maxHeartbeats 2000000

noncomputable def lemma81CIntegral {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p)
    (a₁ a₂ : ℕ → ℂ) (x : ℝ) : ℂ :=
  lemma81NormalizedSegmentIntegral D x (lemma81CIntegrand D c ψ a₁ a₂)

lemma lemma81_normalization_factor_norm_le_one : ‖((2*Real.pi : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
  exact inv_le_one_of_one_le₀ (by nlinarith only [Real.one_le_pi_div_two])

lemma lemma81_normalized_family_error_bound {ι : Type*} (S : Finset ι)
    (D : ℕ) (x : ℝ) (f g : ι → ℂ → ℂ) (hL : 3 ≤ lemma23PaperL D)
    (hf : ∀ i ∈ S, IntervalIntegrable (fun t => f i (lemma81SegmentPoint D x t)) volume
      (-(lemma23PaperL D^405)) (lemma23PaperL D^405))
    (hg : ∀ i ∈ S, IntervalIntegrable (fun t => g i (lemma81SegmentPoint D x t)) volume
      (-(lemma23PaperL D^405)) (lemma23PaperL D^405)) :
    IntervalIntegrable (fun t => ∑ i ∈ S, ‖f i (lemma81SegmentPoint D x t)-g i (lemma81SegmentPoint D x t)‖)
      volume (-(lemma23PaperL D^405)) (lemma23PaperL D^405) ∧
    ‖∑ i ∈ S, (lemma81NormalizedSegmentIntegral D x (f i)-lemma81NormalizedSegmentIntegral D x (g i))‖ ≤
      ∫ t in (-(lemma23PaperL D^405))..(lemma23PaperL D^405),
        ∑ i ∈ S, ‖f i (lemma81SegmentPoint D x t)-g i (lemma81SegmentPoint D x t)‖ := by
  have hab : -(lemma23PaperL D^405) ≤ lemma23PaperL D^405 :=
    neg_le_self (pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 405)
  have hint (i : ι) (hi : i ∈ S) : IntervalIntegrable
      (fun t => ‖f i (lemma81SegmentPoint D x t)-g i (lemma81SegmentPoint D x t)‖) volume
      (-(lemma23PaperL D^405)) (lemma23PaperL D^405) := ((hf i hi).sub (hg i hi)).norm
  have hsum : IntervalIntegrable
      (fun t => ∑ i ∈ S, ‖f i (lemma81SegmentPoint D x t)-g i (lemma81SegmentPoint D x t)‖) volume
      (-(lemma23PaperL D^405)) (lemma23PaperL D^405) := by
    have he : (∑ i ∈ S, fun t => ‖f i (lemma81SegmentPoint D x t)-g i (lemma81SegmentPoint D x t)‖) =
        (fun t => ∑ i ∈ S, ‖f i (lemma81SegmentPoint D x t)-g i (lemma81SegmentPoint D x t)‖) := by
      funext t
      simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum S hint
  refine ⟨hsum,?_⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ S, ∫ t in (-(lemma23PaperL D^405))..(lemma23PaperL D^405),
        ‖f i (lemma81SegmentPoint D x t)-g i (lemma81SegmentPoint D x t)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      unfold lemma81NormalizedSegmentIntegral
      rw [← mul_sub,← intervalIntegral.integral_sub (hf i hi) (hg i hi),norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) lemma81_normalization_factor_norm_le_one).trans
        (intervalIntegral.norm_integral_le_integral_norm hab)
    _ = _ := (intervalIntegral.integral_finsetSum hint).symm

/-- Uniform actual integrated replacement at the full original coefficient
and branch quantifiers, with the precise P²L^-78 aggregate scale. -/
theorem lemma81_uniform_aggregate_replacement_integral {c : ℝ} (hc : 0 < c)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      ∀ (χ : RealPrimitiveCharacter D) (a₁ a₂ : ℕ → ℂ),
      Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
      (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
      ‖∑ ψ ∈ lemma81GoodFamily χ,
        (lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D) -
          lemma81CIntegral D c ψ.2 a₁ a₂ (lemma44PaperAlpha D))‖ ≤
        C*lemma23PaperP D^2*lemma23PaperL D^(-78 : ℤ) := by
  obtain ⟨Cp,hCp,Np,hpoint⟩ := lemma81_uniform_aggregate_replacement_pointwise hc hB₁ hB₂
  obtain ⟨Ni,hint⟩ := lemma81_uniform_actual_contour_integrability hc
  let C := Cp*(2*Real.pi*Real.exp 1)
  refine ⟨C,by dsimp [C]; positivity,max Np (max Ni lemma23SectionFourModulusThreshold),?_⟩
  intro D hD χ a₁ a₂ ha₁ ha₂ Y hY
  have hDp := (le_max_left Np (max Ni lemma23SectionFourModulusThreshold)).trans hD
  have hDi := (le_max_left Ni lemma23SectionFourModulusThreshold).trans
    ((le_max_right Np (max Ni lemma23SectionFourModulusThreshold)).trans hD)
  have hsection := (le_max_right Ni lemma23SectionFourModulusThreshold).trans
    ((le_max_right Np (max Ni lemma23SectionFourModulusThreshold)).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold hsection).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  let F := lemma81GoodFamily χ
  let f : lemma33CharacterIndex D → ℂ → ℂ := fun ψ => lemma81TildeIntegrand D c ψ.2 (Y ψ) a₁ a₂
  let g : lemma33CharacterIndex D → ℂ → ℂ := fun ψ => lemma81CIntegrand D c ψ.2 a₁ a₂
  have hi (ψ : lemma33CharacterIndex D) (hψ : ψ ∈ F) :=
    hint χ ψ.2 hDi ((lemma81_mem_good_family χ ψ).mp hψ) (Y ψ) (hY ψ hψ) a₁ a₂
  have hb := lemma81_normalized_family_error_bound F D (lemma44PaperAlpha D) f g hL
    (fun ψ hψ => (hi ψ hψ).1) (fun ψ hψ => (hi ψ hψ).2.2.1)
  have hΩ : Continuous (fun t => ‖lemma81Omega D (lemma81SegmentPoint D (lemma44PaperAlpha D) t)‖) := by
    have hω := (lemma81_omega_differentiable D).continuous
    unfold lemma81SegmentPoint
    fun_prop
  let E := Cp*lemma23PaperP D^2*lemma23PaperL D^(-78 : ℤ)
  have hEn : 0 ≤ E := by dsimp [E]; positivity
  have hmono : (∫ t in (-(lemma23PaperL D^405))..(lemma23PaperL D^405),
      ∑ ψ ∈ F, ‖f ψ (lemma81SegmentPoint D (lemma44PaperAlpha D) t)-g ψ (lemma81SegmentPoint D (lemma44PaperAlpha D) t)‖) ≤
      E*(∫ t in (-(lemma23PaperL D^405))..(lemma23PaperL D^405),
        ‖lemma81Omega D (lemma81SegmentPoint D (lemma44PaperAlpha D) t)‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (neg_le_self (pow_nonneg hLp.le 405)) hb.1
      ((hΩ.const_mul E).intervalIntegrable _ _)
    intro t ht
    exact hpoint D hDp χ a₁ a₂ ha₁ ha₂ Y hY _
      (lemma81_right_point_mem_segment hL (by rwa [uIcc_of_le (neg_le_self (pow_nonneg hLp.le 405))]))
  change ‖∑ ψ ∈ F, (lemma81NormalizedSegmentIntegral D (lemma44PaperAlpha D) (f ψ)-
    lemma81NormalizedSegmentIntegral D (lemma44PaperAlpha D) (g ψ))‖ ≤ _
  apply hb.2.trans
  apply hmono.trans
  have hmass := lemma81_actual_finite_gaussian_mass hL
    (x := lemma44PaperAlpha D) (by rw [abs_of_pos (lemma44_alpha_pos_le_one hL).1]; exact (lemma44_alpha_pos_le_one hL).2)
  apply (mul_le_mul_of_nonneg_left hmass hEn).trans_eq
  dsimp [E,C]
  ring

end ZhangLS.Spec
