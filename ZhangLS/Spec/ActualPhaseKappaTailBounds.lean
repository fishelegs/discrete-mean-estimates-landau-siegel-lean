import ZhangLS.Spec.ActualPhaseSafeSeries
import ZhangLS.Spec.Lemma32SeriesConvergence

/-! Coarse but uniform outward tail estimates for the actual kappa series.
The fixed three-halves mass is independent of all source parameters. Its
extra fixed power of the cutoff is used only where the original Gaussian
or a fixed power-of-P contour gap gives exponential suppression.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Real Classical
set_option maxHeartbeats 2000000

noncomputable def actualPhaseTauFourThreeHalvesMass : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun m => (lemma34Tau 4 m : ℂ)) (3/2 : ℂ) n‖

theorem actualPhase_tau_four_three_halves_summable :
    Summable (fun n : ℕ => ‖LSeries.term (fun m => (lemma34Tau 4 m : ℂ)) (3/2 : ℂ) n‖) :=
  summable_norm_iff.mpr (lemma32_tau_lseries_summable 3 (3/2 : ℂ) (by norm_num))

theorem actualPhase_tau_four_three_halves_mass_pos : 0 < actualPhaseTauFourThreeHalvesMass := by
  have hh := actualPhase_tau_four_three_halves_summable.le_tsum 1 (fun n hn => norm_nonneg _)
  have h1 : lemma34Tau 4 1 = 1 := (lemma34_tau_multiplicative 4).map_one
  have hb : (1 : ℝ) ≤ actualPhaseTauFourThreeHalvesMass := by
    simpa [LSeries.term,actualPhaseTauFourThreeHalvesMass,h1] using hh
  linarith

/-- The actual omitted terms keep their strict finite-cutoff convention.
The bound is uniform for every sigma at least three halves, including the
far sigma=one half plus L^9 contour. -/
theorem actualPhase_imaginary_kappa_tail_term_bound {p : ℕ} {R : ℝ}
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (ψ : DirichletCharacter ℂ p) (hR : 0 < R) {s : ℂ}
    (hs : 3/2 ≤ s.re) (n : ℕ) (hn : n ∉ actualPhaseStrictIndices R) :
    ‖LSeries.term (fun m => ψ (m : ZMod p)*lemma83Kappa β m) s n‖ ≤
      R^(3/2-s.re)*‖LSeries.term (fun m => (lemma34Tau 4 m : ℂ)) (3/2 : ℂ) n‖ := by
  by_cases hn0 : n = 0
  · subst n
    simp
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnR : R ≤ (n : ℝ) := by
    by_contra hh
    exact hn (actualPhase_mem_strict_indices.mpr ⟨Nat.pos_of_ne_zero hn0,lt_of_not_ge hh⟩)
  have hpow := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hR hnR (sub_nonpos.mpr hs))
    (Real.rpow_nonneg hnp.le (-(3/2 : ℝ)))
  have hpow' : (n : ℝ)^(-s.re) ≤ R^(3/2-s.re)*(n : ℝ)^(-(3/2 : ℝ)) := by
    convert hpow using 1
    rw [←Real.rpow_add hnp]
    congr 1
    ring
  have hk : ‖ψ (n : ZMod p)*lemma83Kappa β n‖ ≤ (lemma34Tau 4 n : ℝ) := by
    rw [norm_mul]
    apply (mul_le_mul (ψ.norm_le_one _) (proposition71_actual_kappa_le_tau_four
      β hβ n) (norm_nonneg _) zero_le_one).trans_eq
    rw [one_mul]
  rw [LSeries.norm_term_eq,LSeries.norm_term_eq,if_neg hn0,if_neg hn0,Complex.norm_natCast]
  have hre : (3/2 : ℂ).re = (3/2 : ℝ) := by norm_num
  rw [hre]
  calc
    _ ≤ (lemma34Tau 4 n : ℝ)/(n : ℝ)^s.re :=
      div_le_div_of_nonneg_right hk (Real.rpow_nonneg hnp.le _)
    _ = (lemma34Tau 4 n : ℝ)*(n : ℝ)^(-s.re) := by
      rw [Real.rpow_neg hnp.le,div_eq_mul_inv]
    _ ≤ (lemma34Tau 4 n : ℝ)*(R^(3/2-s.re)*(n : ℝ)^(-(3/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hpow' (Nat.cast_nonneg _)
    _ = _ := by rw [Real.rpow_neg hnp.le,div_eq_mul_inv]; ring

/-- A proved uniform bound for the genuine omitted series, with no finite
polynomial identified with the continued quotient. -/
theorem actualPhase_imaginary_kappa_tail_norm_bound {p : ℕ} {R : ℝ}
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (ψ : DirichletCharacter ℂ p) (hR : 0 < R) {s : ℂ}
    (hs : 3/2 ≤ s.re) :
    ‖∑' n : {n : ℕ // n ∉ actualPhaseStrictIndices R},
      LSeries.term (fun m => ψ (m : ZMod p)*lemma83Kappa β m) s n‖ ≤
      R^(3/2-s.re)*actualPhaseTauFourThreeHalvesMass := by
  have hsafe : 1 < s.re := by linarith
  have hseries := proposition71_kappa_twist_summable ψ β hβ hsafe
  have htail : Summable (fun n : {n : ℕ // n ∉ actualPhaseStrictIndices R} =>
      LSeries.term (fun m => ψ (m : ZMod p)*lemma83Kappa β m) s n) := hseries.subtype _
  have ht (n : {n : ℕ // n ∉ actualPhaseStrictIndices R}) :=
    actualPhase_imaginary_kappa_tail_term_bound β hβ ψ hR hs n n.property
  have hnorm := Summable.tsum_le_tsum ht htail.norm
    ((actualPhase_tau_four_three_halves_summable.subtype
      (fun n => n ∉ actualPhaseStrictIndices R)).mul_left (R^(3/2-s.re)))
  have hmass : (∑' n : {n : ℕ // n ∉ actualPhaseStrictIndices R},
      ‖LSeries.term (fun m => (lemma34Tau 4 m : ℂ)) (3/2 : ℂ) n‖) ≤
        actualPhaseTauFourThreeHalvesMass :=
    Summable.tsum_subtype_le _ _ (fun n => norm_nonneg _)
      actualPhase_tau_four_three_halves_summable
  apply (norm_tsum_le_tsum_norm htail.norm).trans
  apply hnorm.trans
  simpa only [tsum_mul_left] using
    mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hR.le _)

/-- The right tail uses the literal original kappa coefficient. -/
theorem actualPhase_kappa_tail_norm_bound {D p : ℕ} {R : ℝ}
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hR : 0 < R) {s : ℂ}
    (hs : 3/2 ≤ s.re) :
    ‖actualPhaseKappaTail D c R ψ s‖ ≤
      R^(3/2-s.re)*actualPhaseTauFourThreeHalvesMass := by
  exact actualPhase_imaginary_kappa_tail_norm_bound (lemma83PaperBeta D c)
    (lemma83_beta_re D c) ψ hR hs

/-- The left tail retains the conjugated original coefficient and inverse
character. Its exponent is the true dual real coordinate. -/
theorem actualPhase_dual_kappa_tail_norm_bound {D p : ℕ} {R : ℝ}
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hR : 0 < R) {s : ℂ}
    (hs : s.re ≤ -(1/2)) :
    ‖actualPhaseDualKappaTail D c R ψ s‖ ≤
      R^(1/2+s.re)*actualPhaseTauFourThreeHalvesMass := by
  have hβ (i : Fin 3) : (-lemma83PaperBeta D c i).re = 0 := by
    simp only [Complex.neg_re,lemma83_beta_re,neg_zero]
  have hsafe : 3/2 ≤ (1-s).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  have he := actualPhase_imaginary_kappa_tail_norm_bound
    (fun i => -lemma83PaperBeta D c i) hβ ψ⁻¹ hR hsafe
  have hexp : (3/2 : ℝ)-(1-s).re = 1/2+s.re := by
    simp only [Complex.sub_re,Complex.one_re]
    ring
  simpa only [actualPhase_negative_shift_kappa,actualPhaseDualKappaTail,hexp] using he

end ZhangLS.Spec
