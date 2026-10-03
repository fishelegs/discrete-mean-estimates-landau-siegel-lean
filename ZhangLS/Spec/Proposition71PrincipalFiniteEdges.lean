import ZhangLS.Spec.Proposition71PrincipalBoundaryPointwise
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical Topology
set_option maxHeartbeats 3000000

/-- The actual left edge and both connecting horizontal edges, estimated
without suppressing q, τ₅(d), or any finite Euler factor. -/
theorem proposition71_principal_finite_edges :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → 2000≤lemma23PaperL D →
      ∀ c : ℝ, 0<c → c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 →
      ∀ d m : ℕ, d≠0 → ∀ q : ℝ, 1≤q →
      let F := proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
      let a := 1-1/lemma23PaperL D
      let b := 1+lemma44PaperAlpha D
      let H := proposition71ZetaAuxHeight D
      (‖∫t : ℝ in -(H/2)..(H/2),F ((a : ℂ)+(t : ℂ)*I)‖≤
        4*lemma54MellinStripConstant*(9*Real.exp 1)^4*proposition71PrincipalArithmeticBound D d m*
          q^a*lemma23PaperL D^3244*H) ∧
      ∀t : ℝ, |t|=H/2 →
      ‖∫σ : ℝ in a..b,F ((σ : ℂ)+(t : ℂ)*I)‖≤
        16*lemma54MellinStripConstant*(9*Real.exp 1)^4*proposition71PrincipalArithmeticBound D d m*
          q^b*lemma23PaperL D^3244/H^2 := by
  obtain ⟨D₀,hD₀,hbound⟩ := proposition71_principal_separated_pointwise
  refine ⟨D₀,hD₀,?_⟩
  intro D hDN hL c hc hsmall d m hd q hq1
  dsimp only
  let F := proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
  let a := 1-1/lemma23PaperL D
  let b := 1+lemma44PaperAlpha D
  let H := proposition71ZetaAuxHeight D
  let C := 4*lemma54MellinStripConstant*(9*Real.exp 1)^4*
    proposition71PrincipalArithmeticBound D d m*lemma23PaperL D^3244
  have hq : 0<q := by linarith
  have hH : 0<H := proposition71_zeta_aux_height_pos D
  have hα := (proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)).1
  have hlogpos : 0<lemma23PaperL D := by linarith
  have hLp : 0<1/lemma23PaperL D := by positivity
  have hab : a<b := by dsimp [a,b]; linarith
  have hA := proposition71_principal_arithmetic_bound_nonneg hL d m
  have hCM := lemma54_mellin_strip_constant_pos
  have hC : 0≤C := by dsimp [C]; positivity
  have hpt (s : ℂ) (hs : s∈Icc a b ×ℂ Icc (-(H/2)) (H/2))
      (hs1 : s≠1) (hsep : ∀j : Fin 3,1/lemma23PaperL D≤‖s+lemma83PaperBeta D c j-1‖) :
      ‖F s‖≤C*q^s.re/(1+s.im^2) := by
    have hh := hbound D hDN hL c hc hsmall d m hd q hq s
      (by simpa only [a,b,H,neg_div] using hs) hs1 hsep
    apply hh.trans_eq
    dsimp [C]
    ring
  constructor
  · have hb : ∀ t∈Set.uIoc (-(H/2)) (H/2),‖F ((a : ℂ)+(t : ℂ)*I)‖≤C*q^a := by
      intro t ht
      rw [uIoc_of_le (by linarith : -(H/2)≤H/2)] at ht
      have hs : (a : ℂ)+(t : ℂ)*I∈Icc a b ×ℂ Icc (-(H/2)) (H/2) := by
        constructor
        · simpa using (show a≤a ∧ a≤b from ⟨le_rfl,hab.le⟩)
        · simpa using (show -(H/2)≤t ∧ t≤H/2 from ⟨ht.1.le,ht.2⟩)
      have hsep (j : Fin 3) := proposition71_principal_left_pole_separation hL c
        (s := (a : ℂ)+(t : ℂ)*I) (by simp [a]) j
      have hh := hpt _ hs (hsep 0).1 (fun j => (hsep j).2)
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,
        sub_zero,add_zero,add_im,mul_im,mul_one,zero_add] at hh
      exact hh.trans (div_le_self (by positivity) (by nlinarith [sq_nonneg t]))
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have he : |H/2-(-(H/2))|=H := by rw [show H/2-(-(H/2))=H by ring,abs_of_pos hH]
    rw [he] at hh
    apply hh.trans_eq
    dsimp [C]
    ring
  · intro t ht
    let B := 4*C*q^b/H^2
    have hB : 0≤B := by dsimp [B]; positivity
    have hb : ∀ σ∈Set.uIoc a b,‖F ((σ : ℂ)+(t : ℂ)*I)‖≤B := by
      intro σ hσ
      rw [uIoc_of_le hab.le] at hσ
      have him : |(((σ : ℂ)+(t : ℂ)*I) : ℂ).im|=H/2 := by simpa using ht
      have hs : (σ : ℂ)+(t : ℂ)*I∈Icc a b ×ℂ Icc (-(H/2)) (H/2) := by
        constructor
        · simpa using (show a≤σ ∧ σ≤b from ⟨hσ.1.le,hσ.2⟩)
        · simpa using (abs_le.mp ht.le)
      have hsep (j : Fin 3) := proposition71_principal_horizontal_pole_separation hL hc hsmall him j
      have hh := hpt _ hs (hsep 0).1 (fun j => (hsep j).2)
      have hre : (((σ : ℂ)+(t : ℂ)*I) : ℂ).re=σ := by simp
      have him' : (((σ : ℂ)+(t : ℂ)*I) : ℂ).im=t := by simp
      rw [hre,him'] at hh
      have hsq : t^2=H^2/4 := by rw [←sq_abs t,ht]; ring
      have hpow : q^σ≤q^b := Real.rpow_le_rpow_of_exponent_le hq1 hσ.2
      have hh' := div_le_div₀ (by positivity : 0≤C*q^b)
        (mul_le_mul_of_nonneg_left hpow hC) (by positivity : 0<H^2/4)
        (by rw [hsq]; linarith : H^2/4≤1+t^2)
      apply (hh.trans hh').trans_eq
      dsimp [B]
      field_simp
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have hw : |b-a|≤1 := proposition71_short_rectangle_width hL
    apply (hh.trans (mul_le_of_le_one_right hB hw)).trans_eq
    dsimp [B,C]
    ring

end ZhangLS.Spec
