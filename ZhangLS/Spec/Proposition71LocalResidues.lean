import ZhangLS.Spec.Section15PaperBridge

/-! Actual local residues in Proposition 7.1. The integrand is the three shifted
zeta factors divided by the unshifted zeta factor, times the original Mellin
transform from Lemma 5.4. Residues are defined by punctured-neighborhood limits. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Metric Set
open scoped Topology
set_option maxHeartbeats 2000000

/-- The actual meromorphic integrand defining the source residues. -/
noncomputable def proposition71ResidueIntegrand (D : ℕ) (β : Fin 3 → ℂ) (s : ℂ) : ℂ :=
  riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s *
    lemma54PaperDeltaMellin D s

/-- The genuine local pole numerator, with only the distinguished pole removed. -/
noncomputable def proposition71PoleNumerator (D : ℕ) (β : Fin 3 → ℂ)
    (j : Fin 3) (s : ℂ) : ℂ :=
  zetaPoleRemoved (s+β j)*riemannZeta (s+β (j+1))*riemannZeta (s+β (j+2)) /
    riemannZeta s * lemma54PaperDeltaMellin D s

/-- Source residue, defined from the original integrand and original shifts. -/
noncomputable def proposition71ActualR (D : ℕ) (c : ℝ) (j : Fin 3) : ℂ :=
  limUnder (𝓝[≠] (1-lemma83PaperBeta D c j))
    (fun s => (s-(1-lemma83PaperBeta D c j))*
      proposition71ResidueIntegrand D (lemma83PaperBeta D c) s)

lemma proposition71_cyclic_zeta_product (β : Fin 3 → ℂ) (s : ℂ) (j : Fin 3) :
    riemannZeta (s+β j)*riemannZeta (s+β (j+1))*riemannZeta (s+β (j+2)) =
      riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2) := by
  fin_cases j
  · rfl
  · change riemannZeta (s+β 1)*riemannZeta (s+β 2)*riemannZeta (s+β 0)=_; ring
  · change riemannZeta (s+β 2)*riemannZeta (s+β 0)*riemannZeta (s+β 1)=_; ring

lemma proposition71_zeta_analyticAt {s : ℂ} (hs : s≠1) : AnalyticAt ℂ riemannZeta s := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  exact (continuousAt_id.eventually_ne hs).mono fun z hz => differentiableAt_riemannZeta hz

lemma proposition71_pole_numerator_analytic {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (β : Fin 3 → ℂ) (hβ : ∀ k, (β k).re=0)
    (j : Fin 3) (hb : β j≠0) (hinj : Function.Injective β)
    (hZ : riemannZeta (1-β j)≠0) :
    AnalyticAt ℂ (proposition71PoleNumerator D β j) (1-β j) := by
  have harg (k : Fin 3) : AnalyticAt ℂ (fun s : ℂ => s+β k) (1-β j) := by fun_prop
  have hne (k : Fin 3) (hk : k≠j) : 1-β j+β k≠1 := by
    intro he
    apply hk
    apply hinj
    linear_combination he
  have hj1 : j+1≠j := by fin_cases j <;> decide
  have hj2 : j+2≠j := by fin_cases j <;> decide
  have hz := (lemma55_actual_zeta_pole_removed_analyticAt
    (show 0<(1-β j+β j).re by simp)).comp (f := fun s : ℂ => s+β j) (x := 1-β j) (harg j)
  have hz1 := (proposition71_zeta_analyticAt (hne _ hj1)).comp (f := fun s : ℂ => s+β (j+1)) (x := 1-β j) (harg (j+1))
  have hz2 := (proposition71_zeta_analyticAt (hne _ hj2)).comp (f := fun s : ℂ => s+β (j+2)) (x := 1-β j) (harg (j+2))
  have hz0 := proposition71_zeta_analyticAt (show 1-β j≠1 by intro h; apply hb; linear_combination -h)
  have hd := lemma54_mellin_analyticOnNhd hD hL (1-β j) (by simp [hβ])
  exact (((hz.mul hz1).mul hz2).div hz0 hZ).mul hd

lemma proposition71_integrand_regularization (D : ℕ) (β : Fin 3 → ℂ) (j : Fin 3)
    {s : ℂ} (hs0 : s+β j≠0) (hs1 : s+β j≠1) :
    proposition71ResidueIntegrand D β s =
      proposition71PoleNumerator D β j s/(s-(1-β j)) := by
  have hs : s-(1-β j)≠0 := by intro h; apply hs1; linear_combination h
  unfold proposition71ResidueIntegrand proposition71PoleNumerator
  rw [zetaPoleRemoved_eq_mul_riemannZeta hs0 hs1]
  rw [show (s+β j-1)*riemannZeta (s+β j)*riemannZeta (s+β (j+1))*
      riemannZeta (s+β (j+2)) = (s-(1-β j))*(riemannZeta (s+β j)*
      riemannZeta (s+β (j+1))*riemannZeta (s+β (j+2))) by ring,
    proposition71_cyclic_zeta_product]
  field_simp

lemma proposition71_actual_local_factorization (D : ℕ) (β : Fin 3 → ℂ) (j : Fin 3) :
    proposition71ResidueIntegrand D β =ᶠ[𝓝[≠] (1-β j)]
      (fun s => proposition71PoleNumerator D β j s/(s-(1-β j))) := by
  have h0 : ∀ᶠ s : ℂ in 𝓝 (1-β j), s+β j≠0 :=
    (by fun_prop : ContinuousAt (fun s : ℂ => s+β j) (1-β j)).eventually_ne (by simp)
  filter_upwards [h0.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs0 hs
  have hs' : s≠1-β j := by simpa using hs
  have hs1 : s+β j≠1 := by intro he; apply hs'; linear_combination he
  exact proposition71_integrand_regularization D β j hs0 hs1

lemma proposition71_residue_limit {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (β : Fin 3 → ℂ) (hβ : ∀ k, (β k).re=0)
    (j : Fin 3) (hb : β j≠0) (hinj : Function.Injective β)
    (hZ : riemannZeta (1-β j)≠0) :
    Tendsto (fun s => (s-(1-β j))*proposition71ResidueIntegrand D β s)
      (𝓝[≠] (1-β j)) (𝓝 (proposition71PoleNumerator D β j (1-β j))) := by
  have ht := (proposition71_pole_numerator_analytic hD hL β hβ j hb hinj hZ).continuousAt.tendsto
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [proposition71_actual_local_factorization D β j,self_mem_nhdsWithin] with s hs hn
  have hsn : s-(1-β j)≠0 := sub_ne_zero.mpr (by simpa using hn)
  rw [hs]
  exact (mul_div_cancel₀ _ hsn).symm

lemma proposition71_actual_zeta_denominator_nonzero {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    zetaPoleRemoved (1-lemma83PaperBeta D c j)≠0 ∧
      riemannZeta (1-lemma83PaperBeta D c j)≠0 := by
  have hb := (section15_actual_shift_data hL hc hsmall).1 j
  have hbre := lemma83_beta_re D c j
  have hα := lemma152_alpha_le_hundredth hL
  have hn : ‖(1-lemma83PaperBeta D c j)-1‖≤3*lemma44PaperAlpha D := by
    simpa using lemma83_paper_beta_norm hL hc hsmall j
  have hz := section15_ne_zero_of_near_one
    (section15_zeta_regular_error (hn.trans (by linarith))) (by linarith : 5*‖(1-lemma83PaperBeta D c j)-1‖<1)
  refine ⟨hz,?_⟩
  have h0 : 1-lemma83PaperBeta D c j≠0 := by intro he; have := congrArg Complex.re he; simp [hbre] at this
  have h1 : 1-lemma83PaperBeta D c j≠1 := by intro he; apply hb; linear_combination -he
  rw [zetaPoleRemoved_eq_mul_riemannZeta h0 h1] at hz
  exact (mul_ne_zero_iff.mp hz).2

/-- Exact source residue formula, retaining the actual Mellin transform. -/
theorem proposition71_actual_residue_formula {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    proposition71ActualR D c j =
      lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j) *
        riemannZeta (1+lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j) *
        riemannZeta (1+lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j) /
        riemannZeta (1-lemma83PaperBeta D c j) := by
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hd := section15_actual_shift_data hL3 hc hsmall
  have hz := (proposition71_actual_zeta_denominator_nonzero hL3 hc hsmall j).2
  have ht := proposition71_residue_limit hD hL (lemma83PaperBeta D c)
    (lemma83_beta_re D c) j (hd.1 j) hd.2 hz
  rw [proposition71ActualR,ht.limUnder_eq]
  unfold proposition71PoleNumerator
  rw [sub_add_cancel,lemma55_actual_zeta_pole_removed_at_one]
  rw [show 1-lemma83PaperBeta D c j+lemma83PaperBeta D c (j+1)=
    1+lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j by ring]
  rw [show 1-lemma83PaperBeta D c j+lemma83PaperBeta D c (j+2)=
    1+lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j by ring]
  ring

/-- All genuine local analytic data at the original three shifts. No
nonvanishing, injectivity, or residue-value hypothesis is required. -/
theorem proposition71_actual_residue_local_data {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    AnalyticAt ℂ (proposition71PoleNumerator D (lemma83PaperBeta D c) j)
      (1-lemma83PaperBeta D c j) ∧
    (proposition71ResidueIntegrand D (lemma83PaperBeta D c) =ᶠ[𝓝[≠] (1-lemma83PaperBeta D c j)]
      (fun s => proposition71PoleNumerator D (lemma83PaperBeta D c) j s/
        (s-(1-lemma83PaperBeta D c j)))) ∧
    Tendsto (fun s => (s-(1-lemma83PaperBeta D c j))*
      proposition71ResidueIntegrand D (lemma83PaperBeta D c) s)
      (𝓝[≠] (1-lemma83PaperBeta D c j)) (𝓝 (proposition71ActualR D c j)) := by
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hd := section15_actual_shift_data hL3 hc hsmall
  have hz := (proposition71_actual_zeta_denominator_nonzero hL3 hc hsmall j).2
  have ht := proposition71_residue_limit hD hL (lemma83PaperBeta D c)
    (lemma83_beta_re D c) j (hd.1 j) hd.2 hz
  refine ⟨proposition71_pole_numerator_analytic hD hL (lemma83PaperBeta D c)
    (lemma83_beta_re D c) j (hd.1 j) hd.2 hz,
    proposition71_actual_local_factorization D (lemma83PaperBeta D c) j,?_⟩
  rw [proposition71ActualR,ht.limUnder_eq]
  exact ht

end ZhangLS.Spec
