import ZhangLS.Spec.Lemma81IntegralFourthMoment

/-! # Fourth moment of the actual Gaussian error E₁ in Lemma 6.1

Two Cauchy inequalities control the actual integrated short polynomial.
The interval-length estimate suffices because L^-68 absorbs its fourth
power; the additive exponential term is treated with an actual family bound.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology Classical
set_option maxHeartbeats 2000000

/-- The genuine E₁ fourth moment, uniform in every nonnegative decay rate. -/
theorem lemma81_uniform_actual_E1_fourth_moment :
    ∃ N : ℕ, lemma61ModulusThreshold ≤ N ∧ ∀ D : ℕ, N ≤ D →
      ∀ (s : ℂ) (k : ℝ), |s.re-1/2| ≤ lemma44PaperAlpha D → 0 ≤ k →
      (∑ ψ ∈ lemma33ActualFamily D, lemma61ActualE1 D ψ.2 s k ^ 4) ≤
        136*lemma81FourthMomentConstant*lemma23PaperP D^2*lemma23PaperL D^36 := by
  obtain ⟨N,hN,hmoment⟩ := lemma81_uniform_six_one_polynomial_moments
  refine ⟨N,hN,?_⟩
  intro D hD s k hs hk
  have hparam := lemma61_parameters_at_threshold (hN.trans hD)
  have hL : 3 ≤ lemma23PaperL D := by linarith only [hparam.2]
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  let F := lemma33ActualFamily D
  let M := lemma81FourthMomentConstant*lemma23PaperP D^2*lemma23PaperL D^36
  let H := lemma23PaperL D^20
  let g : lemma33CharacterIndex D → ℝ → ℝ := fun ψ v =>
    ‖lemma61ShortPolynomial D ψ.2 (s+I*(v : ℂ))‖ *
      Real.exp (-(v^2)/(4*lemma23PaperL D^30))
  let J : lemma33CharacterIndex D → ℝ := fun ψ => ∫ v in (-H)..H, g ψ v
  have hH : 0 < H := pow_pos hLp 20
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg lemma81_fourth_moment_constant_pos.le (sq_nonneg _)) (pow_nonneg hLp.le 36)
  have hMshort := (hmoment D hD s hs).2.2
  have hg (ψ : lemma33CharacterIndex D) : Continuous (g ψ) :=
    lemma61_error_integrand_continuous ψ.2 s
  have hgnonneg (ψ : lemma33CharacterIndex D) (v : ℝ) : 0 ≤ g ψ v := by
    dsimp [g]
    positivity
  have hJnonneg (ψ : lemma33CharacterIndex D) : 0 ≤ J ψ :=
    intervalIntegral.integral_nonneg_of_forall (by linarith only [hH]) (hgnonneg ψ)
  have hg4 (v : ℝ) : (∑ ψ ∈ F, g ψ v^4) ≤ M := by
    have hw : Real.exp (-(v^2)/(4*lemma23PaperL D^30)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg v)) (by positivity))
    calc
      _ ≤ ∑ ψ ∈ F, ‖lemma61ShortPolynomial D ψ.2 (s+I*(v : ℂ))‖^4 := by
        apply Finset.sum_le_sum
        intro ψ hψ
        apply pow_le_pow_left₀ (hgnonneg ψ v)
        exact mul_le_of_le_one_right (norm_nonneg _) hw
      _ ≤ _ := hMshort v
  have hJ4 : (∑ ψ ∈ F, J ψ^4) ≤ (2*H)^4*M := by
    have hh := lemma81_finite_family_integral_fourth F g
      (by linarith only [hH] : -H < H) (fun ψ _ => (hg ψ).continuousOn) (fun v _ => hg4 v)
    simpa only [show H-(-H) = 2*H by ring] using hh
  have hscale : (lemma23PaperL D^(-68 : ℤ))^4 * (2*H)^4 =
      16*lemma23PaperL D^(-192 : ℤ) := by
    dsimp [H]
    simp only [zpow_neg,zpow_ofNat]
    field_simp
    ring
  have hfirst : (∑ ψ ∈ F, (lemma23PaperL D^(-68 : ℤ)*J ψ)^4) ≤ 16*M := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    calc
      _ ≤ (lemma23PaperL D^(-68 : ℤ))^4 * ((2*H)^4*M) :=
        mul_le_mul_of_nonneg_left hJ4 (by positivity)
      _ = (16*lemma23PaperL D^(-192 : ℤ))*M := by rw [← mul_assoc,hscale]
      _ ≤ _ := by
        have hh := zpow_le_one_of_nonpos₀ hL1 (by norm_num : (-192 : ℤ) ≤ 0)
        nlinarith only [mul_le_mul_of_nonneg_right hh hM]
  have hP1 : 1 ≤ lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg hLp.le 9)
  have hX1 : 1 ≤ ⌊lemma23PaperP D⌋₊ := Nat.le_floor (by exact_mod_cast hP1)
  have hcard : (F.card : ℝ) ≤ M := by
    have hh := lemma81_actual_polynomial_fourth_moment (by norm_num : (0 : ℝ) ≤ 1)
      hL 1 hX1 (fun _ => (1 : ℂ)) (fun _ _ => by norm_num) hs
    simpa [lemma81FiniteCharacterPolynomial,lemma23FiniteDirichletPolynomial,F,M] using hh
  have htail : (Real.exp (-k*lemma23PaperL D^10))^4 ≤ 1 := by
    apply pow_le_one₀ (Real.exp_nonneg _)
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) (pow_nonneg hLp.le 10))
  have hpoint (ψ : lemma33CharacterIndex D) : lemma61ActualE1 D ψ.2 s k^4 ≤
      8*((lemma23PaperL D^(-68 : ℤ)*J ψ)^4+(Real.exp (-k*lemma23PaperL D^10))^4) := by
    have hh := add_pow_le (mul_nonneg (zpow_nonneg hLp.le (-68 : ℤ)) (hJnonneg ψ))
      (Real.exp_nonneg (-k*lemma23PaperL D^10)) 4
    simpa only [show (2 : ℝ)^(4-1) = 8 by norm_num] using hh
  calc
    _ ≤ ∑ ψ ∈ F, 8*((lemma23PaperL D^(-68 : ℤ)*J ψ)^4+(Real.exp (-k*lemma23PaperL D^10))^4) :=
      Finset.sum_le_sum (fun ψ _ => hpoint ψ)
    _ = 8*((∑ ψ ∈ F, (lemma23PaperL D^(-68 : ℤ)*J ψ)^4)+
        (F.card : ℝ)*(Real.exp (-k*lemma23PaperL D^10))^4) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 8*(16*M+M) := by
      have ht : (F.card : ℝ)*(Real.exp (-k*lemma23PaperL D^10))^4 ≤ M :=
        (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)).trans (by simpa using hcard)
      linarith only [hfirst,ht]
    _ = _ := by dsimp [M]; ring

end ZhangLS.Spec
