import ZhangLS.Spec.Proposition141LargeConductorSaving

/-! # Uniform original-parameter attachment of the large-conductor saving

All parameter and prime-mass thresholds are selected before χ, β or the two
coefficient sequences. The support lemma below derives d h R≤2D P₄ from the
literal a*(dk)≠0 and h*r=D₂*k, retaining the closed support endpoint.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- The genuine short coefficient support supplies the conductor-scale
cutoff, including the original D₂ (then its harmless upper bound D). -/
theorem proposition141_supported_conductor_scale {D D₁ D₂ d h r k:ℕ}
    {Ba:ℝ} {a:ℕ→ℂ} (ha:Proposition141AdmissibleSequence D Ba a)
    (hD:D=D₁*D₂) (hD₁:0<D₁) (_hd:0<d) (_hk:0<k) (han:a (d*k)≠0)
    (hN:h*r=D₂*k) {R:ℝ} (_hR:0≤R) (hRr:R≤(r:ℝ)) :
    ((d*h:ℕ):ℝ)*R≤2*(D:ℝ)*lemma61PaperP4 D := by
  have hs := proposition141_nonzero_support ha han
  have hD₂ : D₂≤D := by rw [hD]; nlinarith
  have hp4 : 0≤lemma61PaperP4 D := by
    unfold lemma61PaperP4
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (zpow_nonneg (Real.exp_pos _).le _))
      (pow_nonneg (Real.log_natCast_nonneg D) _)
  calc
    ((d*h:ℕ):ℝ)*R≤((d*h:ℕ):ℝ)*(r:ℝ) := mul_le_mul_of_nonneg_left hRr (Nat.cast_nonneg _)
    _=((D₂:ℝ)*((d*k:ℕ):ℝ)) := by
      have he : d*h*r=D₂*(d*k) := by rw [mul_assoc,hN]; ring
      exact_mod_cast he
    _≤(D₂:ℝ)*(2*lemma61PaperP4 D) := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _≤(D:ℝ)*(2*lemma61PaperP4 D) := mul_le_mul_of_nonneg_right (by exact_mod_cast hD₂) (by positivity)
    _=_ := by ring

/-- The real original D³ lower boundary, actual support cutoff, full complex
shift and arbitrary modulus filter all fit one uniform threshold under (A). -/
theorem proposition141_uniform_localized_large_saving :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),
      D₀≤D → NormalizedAssumptionA χ → ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
      ∀B:ℝ,0≤B → ∀κ:ℕ→ℂ,Proposition141KappaBound B κ → ∀D₁ d h:ℕ,
      0<D₁ → 0<d → 0<h → ∀R:ℝ,(D:ℝ)^3≤R →
      ((d*h:ℕ):ℝ)*R≤2*(D:ℝ)*lemma61PaperP4 D →
      ∀Q:Finset ℕ,(∀r∈Q,1<r) → (∀r∈Q,(r:ℝ)≤2*R) →
      proposition141LocalizedWeightedMean χ β κ D₁ d h R Q/R^(3/2:ℝ) ≤
        proposition141LargeMeanConstant*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*(h:ℝ)*
          lemma56PrimeMass D*lemma23PaperL D^3351/(D:ℝ)^(3/2:ℝ) := by
  obtain ⟨Nt,ht2,ht⟩ := proposition141_uniform_t0_le_D
  obtain ⟨Nmod,hm2,hmod⟩ := proposition141_uniform_support_modulus_bound
  obtain ⟨NT,hT2,hT⟩ := proposition141_uniform_fourth_lt_T
  obtain ⟨NM,hM⟩ := lemma56_uniform_actual_prime_mass_lower
  let D₀ := max 2 (max Nt (max Nmod (max NT (max NM ⌈Real.exp 2000⌉₊))))
  refine ⟨D₀,by dsimp [D₀]; omega,?_⟩
  intro D χ hlarge hA β hβ B hB κ hκ D₁ d h hD₁ hd hh R hR hcut Q hQ1 hQ
  have hNt : Nt≤D := by dsimp [D₀] at hlarge; omega
  have hNm : Nmod≤D := by dsimp [D₀] at hlarge; omega
  have hNT : NT≤D := by dsimp [D₀] at hlarge; omega
  have hNM : NM≤D := by dsimp [D₀] at hlarge; omega
  have hNe : ⌈Real.exp 2000⌉₊≤D := by dsimp [D₀] at hlarge; omega
  have hD : 1<D := by dsimp [D₀] at hlarge; omega
  have hL : 2000≤lemma23PaperL D := by
    have he : Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  exact proposition141_actual_localized_large_mean_saving χ hD hL (ht D hNt) (hT D hNT).le
    (hmod D hNm) (hM χ hNM hD hA) hβ hB hκ hD₁ hd hh hR hcut Q hQ1 hQ

end ZhangLS.Spec
