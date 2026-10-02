import ZhangLS.Spec.Lemma59FiniteComplexProducts

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma59_log_zero_count_budget {D : ℕ} {N : ℕ}
    (hL : 100 ≤ lemma23PaperL D) (hN : (N : ℝ) ≤ 30 * lemma23PaperL D ^ 9) :
    (N : ℝ) + 1 ≤ 31 * lemma23PaperL D ^ 9 ∧
      1 + Real.log ((N : ℝ) + 1) ≤ 41 * lemma23PaperL D := by
  let L := lemma23PaperL D
  have hLp : 0 < L := by dsimp [L]; linarith only [hL]
  have hL1 : 1 ≤ L := by dsimp [L]; linarith only [hL]
  have hp : 1 ≤ L ^ 9 := one_le_pow₀ hL1
  have hn : (N : ℝ) + 1 ≤ 31 * L ^ 9 := by
    change (N : ℝ) ≤ 30 * L ^ 9 at hN
    linarith only [hN,hp]
  refine ⟨hn,?_⟩
  have hh := Real.log_le_log (by positivity : 0 < (N : ℝ) + 1) hn
  have he : Real.log (31 * L ^ 9) = Real.log 31 + 9 * Real.log L := by
    rw [Real.log_mul (by norm_num : (31 : ℝ) ≠ 0) (pow_ne_zero 9 hLp.ne'),Real.log_pow]
    norm_num
  rw [he] at hh
  have h31 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 31)
  have hl := Real.log_le_self hLp.le
  change 1 + Real.log ((N : ℝ) + 1) ≤ 41 * L
  linarith only [hh,h31,hl,hL1]

lemma lemma59_relaxed_scale_shift_budget {D : ℕ} {c₀ δ : ℝ}
    (hL : 100 ≤ lemma23PaperL D) (hc : 0 < c₀)
    (hsmall : c₀ * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    (hδ : δ ≤ lemma44PaperAlpha D) :
    δ ≤ (1 + 2 * c₀ * lemma44PaperAlpha D * lemma23PaperL D) * lemma46InnerRadius D c₀ ∧
      δ ≤ 2 * lemma46InnerRadius D c₀ := by
  have ha := (lemma59_alpha_bounds hL).1
  have hl : 0 < lemma23PaperL D := by linarith only [hL]
  have hx : 0 < c₀ * lemma44PaperAlpha D * lemma23PaperL D := by positivity
  have hb := mul_nonneg hx.le (show 0 ≤ 1 - 2 * (c₀ * lemma44PaperAlpha D * lemma23PaperL D) by linarith only [hsmall])
  have hc' := mul_nonneg ha.le hb
  unfold lemma46InnerRadius
  constructor <;> nlinarith only [hδ,hsmall,ha,hc']

lemma lemma59_uniform_relaxed_product_budget {D N : ℕ} {c₀ : ℝ}
    (hL : 100 ≤ lemma23PaperL D) (hc : 0 < c₀)
    (hN : (N : ℝ) ≤ 30 * lemma23PaperL D ^ 9) :
    ((N : ℝ) + 1) * Real.exp ((2 * c₀ * lemma44PaperAlpha D * lemma23PaperL D) *
      (1 + Real.log ((N : ℝ) + 1))) ≤
      31 * Real.exp (82 * Real.pi * c₀) * lemma23PaperL D ^ 9 := by
  let L := lemma23PaperL D
  let a := lemma44PaperAlpha D
  have hLp : 0 < L := by dsimp [L]; linarith only [hL]
  have ha : 0 < a := (lemma59_alpha_bounds hL).1
  have hL1 : 1 ≤ L := by linarith only [hLp,show 100 ≤ L from hL]
  have hpow : L ^ 2 ≤ L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
  have hscale : a * L ^ 9 = Real.pi := by
    dsimp [a,lemma44PaperAlpha,lemma23PaperP,L]
    rw [Real.log_exp]
    field_simp [pow_ne_zero 9 hLp.ne']
  have hb := lemma59_log_zero_count_budget hL hN
  have he : (2 * c₀ * a * L) * (1 + Real.log ((N : ℝ) + 1)) ≤ 82 * Real.pi * c₀ := by
    have hm := mul_le_mul_of_nonneg_left hb.2 (by positivity : 0 ≤ 2 * c₀ * a * L)
    have hp := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 82 * c₀ * a)
    have hh : 82 * c₀ * a * L ^ 9 = 82 * Real.pi * c₀ := by
      calc
        _ = 82 * c₀ * (a * L ^ 9) := by ring
        _ = _ := by rw [hscale]; ring
    change (2 * c₀ * a * L) * (1 + Real.log ((N : ℝ) + 1)) ≤ 82 * Real.pi * c₀
    change (2 * c₀ * a * L) * (1 + Real.log ((N : ℝ) + 1)) ≤ (2 * c₀ * a * L) * (41 * L) at hm
    nlinarith only [hm,hp,hh]
  have hexp := Real.exp_le_exp.mpr he
  calc
    _ ≤ (31 * L ^ 9) * Real.exp (82 * Real.pi * c₀) :=
      mul_le_mul hb.1 hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

lemma lemma59_proved : Lemma59Target := by
  intro c hc η hη
  obtain ⟨c₀,hc₀,N₀,hzeros⟩ := lemma59_uniform_actual_local_zero_structure
  obtain ⟨CQ,hCQ,hQall⟩ := lemma59_uniform_actual_zero_removed_first_shift
  obtain ⟨NQ,hQ⟩ := hQall c hc
  obtain ⟨NZ,hZ⟩ := lemma59_uniform_actual_local_zero_bound
  obtain ⟨NS,hSsection,hS⟩ := lemma46_exists_contraction_threshold hc₀
  obtain ⟨NH,hHsection,hH⟩ := lemma52_exists_shift_threshold hc
  let C := 31 * Real.exp (82 * Real.pi * c₀) * (1 + η⁻¹) ^ 3 * CQ
  have hC : 0 < C := by dsimp [C]; positivity
  let D₀ := max N₀ (max NQ (max NZ (max NS NH)))
  refine ⟨C,hC,D₀,?_⟩
  intro D p _ χ ψ hD hψ s hs hpoint
  have hD₀ : N₀ ≤ D := (le_max_left _ _).trans hD
  have hDQ : NQ ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDZ : NZ ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hDS : NS ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD)))
  have hDH : NH ≤ D := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD)))
  have hsection := hHsection.trans hDH
  have hparams := lemma23_sectionFour_parameters_at_explicit_threshold hsection
  have hL : 100 ≤ lemma23PaperL D := by
    have hh := Real.log_le_self (by linarith only [hparams.1] : 0 ≤ lemma23PaperL D)
    linarith only [hh,hparams.2]
  have hθ := lemma59_family_character_nonprincipal ψ hψ.1
  let S := lemma59LocalZeroFinset ψ s.im
  let δ := lemma23PaperOffsetOne D c
  let g := lemma46InnerRadius D c₀
  let ε := 2 * c₀ * lemma44PaperAlpha D * lemma23PaperL D
  have hb := lemma59_paper_offset_one_bounds hL hc (by nlinarith only [hH D hDH])
  have hz := hzeros χ ψ hD₀ hψ hs.2
  have hg : 0 < g := hz.2.1
  have hcrit : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ => (hz.2.2 ρ hρ).1
  have hsep : ∀ ρ ∈ S, ∀ σ ∈ S, ρ ≠ σ → g ≤ ‖σ - ρ‖ :=
    fun ρ hρ σ hσ hne => (hz.2.2 ρ hρ).2.2 σ hσ hne.symm
  have hηpoint : ∀ ρ ∈ S, η * δ ≤ ‖s - ρ‖ := by
    intro ρ hρ
    have hm := (lemma59_mem_actual_local_zero_finset ψ hθ s.im ρ).mp hρ
    exact (mul_le_mul_of_nonneg_left hb.2 hη.le).trans (hpoint ρ hm.2)
  have hα := (lemma59_alpha_bounds hL).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hshift := lemma59_relaxed_scale_shift_budget hL hc₀ (hS D hDS) hb.2
  have hprod := lemma59_separated_complex_zero_product_bound S hg hb.1 hε hη
    hshift.1 hshift.2 hcrit hsep hηpoint
  have hcard : (S.card : ℝ) ≤ 30 * lemma23PaperL D ^ 9 :=
    (hZ χ ψ hDZ hψ (t := s.im) (by linarith only [hs.2])).2
  have hbudget := lemma59_uniform_relaxed_product_budget hL hc₀ hcard
  have hP := hprod.trans (mul_le_mul_of_nonneg_right hbudget
    (by positivity : 0 ≤ (1 + η⁻¹) ^ 3))
  have hQbound := hQ χ ψ hDQ hψ hs
  have heq : (∏ ρ ∈ S,
      ((s + I * (δ : ℂ) - ρ) / (s - ρ)) ^ analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ) =
      ∏ ρ ∈ S, (s + I * (δ : ℂ) - ρ) / (s - ρ) := by
    apply Finset.prod_congr rfl
    intro ρ hρ
    rw [(hz.2.2 ρ hρ).2.1,pow_one]
  rw [lemma59_actual_L_quotient_factorization ψ hθ s.im s (I * (δ : ℂ)),
    lemma59_actual_zero_factor_ratio_eq_product ψ hθ s.im s (I * (δ : ℂ)),norm_mul]
  change ‖∏ ρ ∈ S,
      ((s + I * (δ : ℂ) - ρ) / (s - ρ)) ^ analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ‖ *
      ‖lemma59ZeroRemovedL ψ s.im (s + I * (δ : ℂ)) / lemma59ZeroRemovedL ψ s.im s‖ ≤ _
  rw [heq]
  have hm := mul_le_mul hP hQbound (norm_nonneg _) (by positivity :
    0 ≤ (31 * Real.exp (82 * Real.pi * c₀) * lemma23PaperL D ^ 9) * (1 + η⁻¹) ^ 3)
  apply hm.trans_eq
  dsimp [C]
  simp only [lemma23PaperP,Real.log_exp]
  ring

end ZhangLS.Spec
