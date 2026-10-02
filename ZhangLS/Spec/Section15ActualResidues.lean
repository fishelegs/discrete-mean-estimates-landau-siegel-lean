import ZhangLS.Spec.Section15AnalyticFactorBounds

/-! Actual source (15.16), with its poles defined by a punctured-neighborhood
residue limit. The local regular numerator and its analyticity are proved;
no residue oracle, L(1)=0 replacement, or downstream sum identity is used. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Metric Set
open scoped Topology
set_option maxHeartbeats 2000000

/-- Source (15.16), before any Taylor approximation. -/
noncomputable def section15ActualIntegrand {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (B : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (1+s+β 0)*riemannZeta (1+s+β 1) /
    (riemannZeta (1+s)*dirichletLFunction χ (1+s)) *
    ((B:ℂ)^(s+β 2)*lemma57OmegaOne D (s+β 2))/(s+β 2)

noncomputable def section15RegularFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (B : ℝ) (s : ℂ) : ℂ :=
  zetaPoleRemoved (1+s+β 0)*zetaPoleRemoved (1+s+β 1)*s /
    (zetaPoleRemoved (1+s)*dirichletLFunction χ (1+s)) *
    ((B:ℂ)^(s+β 2)*lemma57OmegaOne D (s+β 2))

noncomputable def section15PoleNumerator {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (B : ℝ) (j : Fin 3) (s : ℂ) : ℂ :=
  section15RegularFactor χ β B s / ((s+β (j+1))*(s+β (j+2)))

/-- The residue is defined from the original meromorphic function, not from
its asserted leading term. -/
noncomputable def section15ActualR {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (B : ℝ) (j : Fin 3) : ℂ :=
  limUnder (𝓝[≠] (-β j)) (fun s => (s+β j)*section15ActualIntegrand χ β B s)

/-- Source line 4136. This keeps the actual Mellin transform δ(1). -/
noncomputable def section15ActualRStar {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) : ℂ :=
  dirichletLFunction χ (1+β 0)*dirichletLFunction χ (1+β 1)/LDerivAtOne χ *
    lemma54PaperDeltaMellin D 1

lemma section15_cyclic_product (β : Fin 3 → ℂ) (s : ℂ) (j : Fin 3) :
    ((s+β (j+1))*(s+β (j+2)))*(s+β j)=
      (s+β 0)*(s+β 1)*(s+β 2) := by
  fin_cases j
  · change ((s+β 1)*(s+β 2))*(s+β 0)=_; ring
  · change ((s+β 2)*(s+β 0))*(s+β 1)=_; ring
  · change ((s+β 0)*(s+β 1))*(s+β 2)=_; ring

lemma section15_integrand_regularization {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (B : ℝ) (j : Fin 3) {s : ℂ}
    (hs : 0<(1+s).re) (hb : ∀ k, 0<(1+s+β k).re)
    (h0 : s≠0) (hn : ∀ k, s+β k≠0) :
    section15ActualIntegrand χ β B s = section15PoleNumerator χ β B j s/(s+β j) := by
  have hz0 : 1+s≠0 := by intro h; simp [h] at hs
  have hz1 : 1+s≠1 := by simpa using h0
  have hbi0 (k : Fin 3) : 1+s+β k≠0 := by intro h; have := hb k; simp [h] at this
  have hbi1 (k : Fin 3) : 1+s+β k≠1 := by
    intro h; apply hn k; linear_combination h
  unfold section15PoleNumerator section15RegularFactor section15ActualIntegrand
  rw [zetaPoleRemoved_eq_mul_riemannZeta hz0 hz1,
    zetaPoleRemoved_eq_mul_riemannZeta (hbi0 0) (hbi1 0),
    zetaPoleRemoved_eq_mul_riemannZeta (hbi0 1) (hbi1 1)]
  simp only [add_sub_cancel_left,show (1+s+β 0)-1=s+β 0 by ring,
    show (1+s+β 1)-1=s+β 1 by ring]
  rw [div_div,section15_cyclic_product]
  field_simp [h0,hn 0,hn 1,hn 2]

lemma section15_regular_factor_analytic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : Fin 3 → ℂ) (hβ : ∀ k, (β k).re=0)
    {B : ℝ} (hB : 0<B) (j : Fin 3)
    (hZ : zetaPoleRemoved (1-β j)≠0) (hL : dirichletLFunction χ (1-β j)≠0) :
    AnalyticAt ℂ (section15RegularFactor χ β B) (-β j) := by
  have had : AnalyticAt ℂ (fun s : ℂ => 1+s) (-β j) := by fun_prop
  have harg (k : Fin 3) : AnalyticAt ℂ (fun s : ℂ => 1+s+β k) (-β j) := by fun_prop
  have hz (k : Fin 3) := (lemma55_actual_zeta_pole_removed_analyticAt
    (show 0<(1+-β j+β k).re by simp [hβ])).comp (f := fun s : ℂ => 1+s+β k) (x := -β j) (harg k)
  have hz0 := (lemma55_actual_zeta_pole_removed_analyticAt
    (show 0<(1+-β j).re by simp [hβ])).comp (f := fun s : ℂ => 1+s) (x := -β j) had
  have hl := ((differentiable_dirichletLFunction_of_one_lt_modulus χ hD).analyticAt (1+-β j)).comp (f := fun s : ℂ => 1+s) (x := -β j) had
  have hd : Differentiable ℂ (fun s : ℂ => (B:ℂ)^(s+β 2)) :=
    (by fun_prop : Differentiable ℂ (fun s : ℂ => s+β 2)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hB.ne'))
  have ho : Differentiable ℂ (fun s : ℂ => lemma57OmegaOne D (s+β 2)) := by
    unfold lemma57OmegaOne
    fun_prop
  unfold section15RegularFactor
  exact (((hz 0).mul (hz 1)).mul (by fun_prop)).div (hz0.mul hl)
    (by simpa only [sub_eq_add_neg] using mul_ne_zero hZ hL) |>.mul
      ((hd.analyticAt _).mul (ho.analyticAt _))

lemma section15_pole_numerator_analytic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : Fin 3 → ℂ) (hβ : ∀ k, (β k).re=0)
    {B : ℝ} (hB : 0<B) (j : Fin 3)
    (hZ : zetaPoleRemoved (1-β j)≠0) (hL : dirichletLFunction χ (1-β j)≠0)
    (hg1 : β (j+1)-β j≠0) (hg2 : β (j+2)-β j≠0) :
    AnalyticAt ℂ (section15PoleNumerator χ β B j) (-β j) := by
  unfold section15PoleNumerator
  exact (section15_regular_factor_analytic χ hD β hβ hB j hZ hL).div (by fun_prop)
    (by convert mul_ne_zero hg1 hg2 using 1; ring)

lemma section15_actual_local_factorization {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ k, (β k).re=0)
    (B : ℝ) (j : Fin 3) (hβ0 : β j≠0) (hinj : Function.Injective β) :
    section15ActualIntegrand χ β B =ᶠ[𝓝[≠] (-β j)]
      (fun s => section15PoleNumerator χ β B j s/(s+β j)) := by
  have hs0 : ∀ᶠ s : ℂ in 𝓝 (-β j), s≠0 :=
    continuousAt_id.eventually_ne (neg_ne_zero.mpr hβ0)
  have hsre : ∀ᶠ s : ℂ in 𝓝 (-β j), 0<(1+s).re := by
    exact (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simp [hβ])
  have hsbre : ∀ᶠ s : ℂ in 𝓝 (-β j), ∀ k, 0<(1+s+β k).re := by
    rw [eventually_all]
    intro k
    exact (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simp [hβ])
  have hsbn : ∀ᶠ s : ℂ in 𝓝 (-β j), ∀ k, k≠j → s+β k≠0 := by
    rw [eventually_all]
    intro k
    by_cases hk : k=j
    · simp [hk]
    · have hn : -β j+β k≠0 := by
        intro he
        exact hk (hinj (by linear_combination he))
      filter_upwards [(by fun_prop : ContinuousAt (fun s : ℂ => s+β k) (-β j)).eventually_ne hn] with s hs
      exact fun _ => hs
  filter_upwards [hs0.filter_mono nhdsWithin_le_nhds,hsre.filter_mono nhdsWithin_le_nhds,
    hsbre.filter_mono nhdsWithin_le_nhds,hsbn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs0 hsre hsbre hsbn hs
  have hsj : s+β j≠0 := by
    have hs' : s≠-β j := by simpa using hs
    simpa [add_eq_zero_iff_eq_neg] using hs'
  have hn (k : Fin 3) : s+β k≠0 := by by_cases hk : k=j; simpa [hk] using hsj; exact hsbn k hk
  exact section15_integrand_regularization χ β B j hsre hsbre hs0 hn

lemma section15_actual_residue_limit {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : Fin 3 → ℂ) (hβ : ∀ k, (β k).re=0)
    {B : ℝ} (hB : 0<B) (j : Fin 3) (hβ0 : β j≠0)
    (hinj : Function.Injective β)
    (hZ : zetaPoleRemoved (1-β j)≠0) (hL : dirichletLFunction χ (1-β j)≠0) :
    Tendsto (fun s => (s+β j)*section15ActualIntegrand χ β B s)
      (𝓝[≠] (-β j)) (𝓝 (section15PoleNumerator χ β B j (-β j))) := by
  have hg1 : β (j+1)-β j≠0 := sub_ne_zero.mpr (by
    intro he; have he' := hinj he; fin_cases j <;> simp at he')
  have hg2 : β (j+2)-β j≠0 := sub_ne_zero.mpr (by
    intro he; have he' := hinj he; fin_cases j <;> simp at he')
  have hcont := (section15_pole_numerator_analytic χ hD β hβ hB j hZ hL hg1 hg2).continuousAt
  apply (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr'
  have hs0 : ∀ᶠ s : ℂ in 𝓝 (-β j), s≠0 :=
    continuousAt_id.eventually_ne (neg_ne_zero.mpr hβ0)
  have hsre : ∀ᶠ s : ℂ in 𝓝 (-β j), 0<(1+s).re := by
    exact (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simp [hβ])
  have hsbre : ∀ᶠ s : ℂ in 𝓝 (-β j), ∀ k, 0<(1+s+β k).re := by
    rw [eventually_all]
    intro k
    exact (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simp [hβ])
  have hsbn : ∀ᶠ s : ℂ in 𝓝 (-β j), ∀ k, k≠j → s+β k≠0 := by
    rw [eventually_all]
    intro k
    by_cases hk : k=j
    · simp [hk]
    · have hn : -β j+β k≠0 := by
        intro he
        exact hk (hinj (by linear_combination he))
      filter_upwards [(by fun_prop : ContinuousAt (fun s : ℂ => s+β k) (-β j)).eventually_ne hn] with s hs
      exact fun _ => hs
  filter_upwards [hs0.filter_mono nhdsWithin_le_nhds,hsre.filter_mono nhdsWithin_le_nhds,
    hsbre.filter_mono nhdsWithin_le_nhds,hsbn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs0 hsre hsbre hsbn hs
  have hsj : s+β j≠0 := by
    have hs' : s≠-β j := by simpa using hs
    simpa [add_eq_zero_iff_eq_neg] using hs'
  have hn (k : Fin 3) : s+β k≠0 := by by_cases hk : k=j; simpa [hk] using hsj; exact hsbn k hk
  rw [section15_integrand_regularization χ β B j hsre hsbre hs0 hn]
  exact (mul_div_cancel₀ _ hsj).symm

/-- Exact source (15.16) simple-pole coefficient, keeping L(1−βⱼ), both
pole-removed zeta factors and the original Gaussian. -/
theorem section15_actual_residue_formula {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : Fin 3 → ℂ) (hβ : ∀ k, (β k).re=0)
    {B : ℝ} (hB : 0<B) (j : Fin 3) (hβ0 : β j≠0)
    (hinj : Function.Injective β)
    (hZ : zetaPoleRemoved (1-β j)≠0) (hL : dirichletLFunction χ (1-β j)≠0) :
    section15ActualR χ β B j =
      (zetaPoleRemoved (1-β j+β 0)*zetaPoleRemoved (1-β j+β 1)*(-β j) /
        (zetaPoleRemoved (1-β j)*dirichletLFunction χ (1-β j)) *
        ((B:ℂ)^(β 2-β j)*lemma57OmegaOne D (β 2-β j))) /
          ((β (j+1)-β j)*(β (j+2)-β j)) := by
  have ht := section15_actual_residue_limit χ hD β hβ hB j hβ0 hinj hZ hL
  rw [section15ActualR,ht.limUnder_eq]
  unfold section15PoleNumerator section15RegularFactor
  simp only [sub_eq_add_neg,neg_add_eq_sub]

end ZhangLS.Spec
