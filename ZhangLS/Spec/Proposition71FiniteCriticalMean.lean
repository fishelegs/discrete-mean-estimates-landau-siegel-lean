import ZhangLS.Spec.Proposition71FiniteContourShift
import ZhangLS.Spec.Proposition71GenericExceptionalSaving
import ZhangLS.Spec.Lemma81GaussianMass

/-! # The actual critical-line finite-model mean for the true functional equation

Exact |Z|=1 cancels the conductor completely on J(0). The original Gaussian
mass and the independently proved actual Ψ₂ polynomial saving are then used.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Finset
open scoped Classical
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096

lemma proposition71_normalized_segment_const_mul (D : ℕ) (x : ℝ) (w : ℂ) (f : ℂ → ℂ) :
    lemma81NormalizedSegmentIntegral D x (fun s => w*f s)=w*lemma81NormalizedSegmentIntegral D x f := by
  unfold lemma81NormalizedSegmentIntegral
  rw [intervalIntegral.integral_const_mul]
  ring

lemma proposition71_finite_front_critical_norm {D N p : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (ψ : DirichletCharacter ℂ p) (Y X : ℕ) (c a : ℕ → ℂ) {s : ℂ} (hs : s.re=1/2) :
    ‖proposition71FiniteFrontKernel D θ ψ Y X c a s‖=
      ‖lemma81FiniteCharacterPolynomial Y c ψ s‖*
        ‖lemma81FiniteCharacterPolynomial X a ψ⁻¹ (1-s)‖*‖lemma81Omega D s‖ := by
  unfold proposition71FiniteFrontKernel
  rw [norm_mul,norm_mul,norm_mul,norm_inv,lemma23DirichletZ_norm_eq_one_on_critical_line θ hθ hN hs,
    inv_one,one_mul]

lemma proposition71_finite_front_segment_integrable {D N p : ℕ} [NeZero N]
    (hL : 3≤lemma23PaperL D) (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (ψ : DirichletCharacter ℂ p) (Y X : ℕ) (c a : ℕ → ℂ) (w : ℂ) (x : ℝ) :
    IntervalIntegrable (fun t => w*proposition71FiniteFrontKernel D θ ψ Y X c a
      (lemma81SegmentPoint D x t)) volume (-(lemma23PaperL D^405)) (lemma23PaperL D^405) := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hH : 0≤lemma23PaperL D^405 := pow_nonneg hLp.le _
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le (neg_le_self hH)] at ht
  have him : |(lemma81SegmentPoint D x t).im-(lemma23PaperCenter D).im|≤2*lemma23PaperL D^405+3 := by
    have he : (lemma81SegmentPoint D x t).im-(lemma23PaperCenter D).im=t := by simp [lemma81SegmentPoint]
    rw [he]
    have hh : |t|≤lemma23PaperL D^405 := abs_le.mpr ht
    linarith
  have hpos : 0<(lemma81SegmentPoint D x t).im := by
    linarith only [(lemma61_wide_height_data hL him).2.1]
  have hc : ContinuousAt (fun t : ℝ => lemma81SegmentPoint D x t) t := by
    unfold lemma81SegmentPoint
    fun_prop
  exact (((proposition71_finite_front_differentiableAt D θ hθ hN ψ Y X c a hpos).continuousAt.comp hc).const_mul w).continuousWithinAt

/-- Uniform o(prime mass) on the critical segment, for arbitrary actual
primitive functional-equation characters, including conductor Dp. -/
theorem proposition71_finite_critical_exceptional_little_o
    (Bc Ba W : ℝ) (hBc : 0<Bc) (hBa : 0<Ba) (hW : 0<W)
    (ε : ℝ) (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ (N : lemma33CharacterIndex D → ℕ) [∀ψ, NeZero (N ψ)]
        (θ : (ψ : lemma33CharacterIndex D) → DirichletCharacter ℂ (N ψ)),
      (∀ψ∈proposition21ActualPsi2Family χ, (θ ψ).IsPrimitive) →
      (∀ψ∈proposition21ActualPsi2Family χ, N ψ≠1) →
      ∀ (X : ℕ), X≤⌊lemma23PaperP D⌋₊ → ∀ c a : ℕ → ℂ,
      (∀n∈Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖c n‖≤Bc*(lemma34Tau 5 n : ℝ)) →
      (∀n∈Finset.Icc 1 X, ‖a n‖≤Ba) →
      ∀ w : lemma33CharacterIndex D → ℂ, (∀ψ∈proposition21ActualPsi2Family χ, ‖w ψ‖≤W) →
      ‖∑ψ∈proposition21ActualPsi2Family χ, w ψ*lemma81NormalizedSegmentIntegral D 0
        (proposition71FiniteFrontKernel D (θ ψ) ψ.2 ⌊lemma23PaperP D^2⌋₊ X c a)‖≤ε*lemma33ActualPrimeMass D := by
  let η := ε/(W*(2*Real.pi*Real.exp 1))
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨Nm,hNm,hmean⟩ := proposition71_generic_exceptional_little_o Bc Ba hBc hBa η hη
  refine ⟨max Nm lemma23SectionFourModulusThreshold,hNm.trans (le_max_left _ _),?_⟩
  intro D hD χ hA N _ θ hθ hN X hX c a hc ha w hw
  have hDm := (le_max_left _ _).trans hD
  have hDs := (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold hDs).1
  have hLp : 0<lemma23PaperL D := by linarith
  let E := proposition21ActualPsi2Family χ
  let F : lemma33CharacterIndex D → ℂ → ℂ := fun ψ s => w ψ*
    proposition71FiniteFrontKernel D (θ ψ) ψ.2 ⌊lemma23PaperP D^2⌋₊ X c a s
  have hI (ψ : lemma33CharacterIndex D) (hψ : ψ∈E) :
      IntervalIntegrable (fun t => F ψ (lemma81SegmentPoint D 0 t)) volume
        (-(lemma23PaperL D^405)) (lemma23PaperL D^405) :=
    proposition71_finite_front_segment_integrable hL (θ ψ) (hθ ψ hψ) (hN ψ hψ) ψ.2 _ X c a (w ψ) 0
  have hb := lemma81_normalized_family_error_bound E D 0 F (fun _ _ => 0) hL hI
    (fun _ _ => intervalIntegrable_const)
  simp only [sub_zero,lemma81NormalizedSegmentIntegral,intervalIntegral.integral_zero,mul_zero] at hb
  have hb' : ‖∑ψ∈E, w ψ*lemma81NormalizedSegmentIntegral D 0
      (proposition71FiniteFrontKernel D (θ ψ) ψ.2 ⌊lemma23PaperP D^2⌋₊ X c a)‖≤
      ∫t in -(lemma23PaperL D^405)..lemma23PaperL D^405,
        ∑ψ∈E, ‖F ψ (lemma81SegmentPoint D 0 t)‖ := by
    convert hb.2 using 1
    congr 1
    apply sum_congr rfl
    intro ψ hψ
    rw [←proposition71_normalized_segment_const_mul]
    rfl
  have hpoint (t : ℝ) :
      (∑ψ∈E, ‖F ψ (lemma81SegmentPoint D 0 t)‖)≤
        (W*(η*lemma33ActualPrimeMass D))*‖lemma81Omega D (lemma81SegmentPoint D 0 t)‖ := by
    let s := lemma81SegmentPoint D 0 t
    have hs : s.re=1/2 := by simp [s,lemma81SegmentPoint,lemma23PaperCenter]
    have hm := hmean D hDm χ hA c a X hX hc ha s hs
    calc
      _≤∑ψ∈E, W*(‖lemma81FiniteCharacterPolynomial ⌊lemma23PaperP D^2⌋₊ c ψ.2 s‖*
          ‖lemma81FiniteCharacterPolynomial X a ψ.2⁻¹ (1-s)‖*‖lemma81Omega D s‖) := by
        apply sum_le_sum
        intro ψ hψ
        dsimp [F]
        rw [norm_mul,proposition71_finite_front_critical_norm (θ ψ) (hθ ψ hψ) (hN ψ hψ) ψ.2 _ X c a hs]
        exact mul_le_mul_of_nonneg_right (hw ψ hψ) (by positivity)
      _=W*proposition71GenericExceptionalMean χ X c a s*‖lemma81Omega D s‖ := by
        unfold proposition71GenericExceptionalMean
        dsimp [E]
        simp only [mul_sum,sum_mul]
        apply sum_congr rfl
        intro ψ hψ
        ring
      _≤_ := by gcongr
  have hΩ : Continuous (fun t => ‖lemma81Omega D (lemma81SegmentPoint D 0 t)‖) := by
    have hω := (lemma81_omega_differentiable D).continuous
    unfold lemma81SegmentPoint
    fun_prop
  have hK : 0≤W*(η*lemma33ActualPrimeMass D) := by
    have hM : 0≤lemma33ActualPrimeMass D := by unfold lemma33ActualPrimeMass; exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    positivity
  apply hb'.trans
  calc
    _≤(W*(η*lemma33ActualPrimeMass D))*(∫t in -(lemma23PaperL D^405)..lemma23PaperL D^405,
        ‖lemma81Omega D (lemma81SegmentPoint D 0 t)‖) := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (neg_le_self (pow_nonneg hLp.le _)) hb.1
        ((hΩ.const_mul _).intervalIntegrable _ _)
      exact fun t ht => hpoint t
    _≤(W*(η*lemma33ActualPrimeMass D))*(2*Real.pi*Real.exp 1) :=
      mul_le_mul_of_nonneg_left (lemma81_actual_finite_gaussian_mass hL (x := 0) (by norm_num)) hK
    _=_ := by dsimp [η]; field_simp

end ZhangLS.Spec
