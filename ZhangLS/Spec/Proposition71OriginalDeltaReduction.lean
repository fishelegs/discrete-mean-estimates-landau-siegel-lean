import ZhangLS.Spec.Proposition71OriginalFamilyExtension

/-! # The actual Θ₁ to primitive Gauss/Δ₁ mean reduction

The original C integrand, both strict coefficient supports, original Ψ and
prime-dependent phase are retained. The infinite Δ₁ series is proved
summable. Primitive Gauss sums are not yet averaged or simplified, so every
nonunit branch remains present for the following arithmetic step.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

noncomputable def proposition71OriginalDeltaOneMean (D : ℕ) (c : ℝ)
    (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑ψ∈lemma33ActualFamily D,
    (-I*(((ψ.1.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)*
      ((gaussSum ψ.2⁻¹ ZMod.stdAddChar/(ψ.1.val : ℂ))*
        (∑'m, proposition71DeltaOneDoubleTerm D
          (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*
            ψ.2 (m : ZMod ψ.1.val)) (lemma81PolynomialIndices D)
          (fun n => a₂ n*ψ.2⁻¹ (n : ZMod ψ.1.val)) (ψ.1.val : ℝ) m))

lemma proposition71_original_short_shifted_power {D p : ℕ}
    (a : ℕ → ℂ) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma81Polynomial D a ψ (1-s)=
      ∑n∈lemma81PolynomialIndices D, (a n*ψ (n : ZMod p))*(n : ℂ)^(s-1) := by
  unfold lemma81Polynomial
  apply sum_congr rfl
  intro n hn
  rw [show 1-s=-(s-1) by ring,Complex.cpow_neg,div_inv_eq_mul]

lemma proposition71_actual_C_strict_front_kernel {D p : ℕ} [NeZero p]
    {B₁ : ℝ} (c : ℝ) (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 1<s.re) :
    lemma81CIntegrand D c ψ a₁ a₂ s=
      (-I*(((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)*
        proposition71FrontActualKernel D ψ
          (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*ψ (m : ZMod p))
          (lemma81PolynomialIndices D) (fun n => a₂ n*ψ⁻¹ (n : ZMod p)) s := by
  unfold lemma81CIntegrand proposition71FrontActualKernel
  rw [←proposition71_actual_ratio_convolution ψ c a₁ ha₁ hs,
    proposition71_original_short_shifted_power]
  unfold lemma81ActualC
  ring

lemma proposition71_actual_C_strict_front_contour {D p : ℕ} [NeZero p]
    {B₁ : ℝ} (c : ℝ) (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (ψ : DirichletCharacter ℂ p) :
    lemma81NormalizedSegmentIntegral D 1 (lemma81CIntegrand D c ψ a₁ a₂)=
      (-I*(((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)*
        lemma81NormalizedSegmentIntegral D 1
          (proposition71FrontActualKernel D ψ
            (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*ψ (m : ZMod p))
            (lemma81PolynomialIndices D) (fun n => a₂ n*ψ⁻¹ (n : ZMod p))) := by
  have hp (t : ℝ) := proposition71_actual_C_strict_front_kernel c a₁ a₂ ha₁ ψ
    (s := lemma81SegmentPoint D 1 t) (by norm_num [lemma81SegmentPoint,lemma23PaperCenter])
  unfold lemma81NormalizedSegmentIntegral
  simp_rw [hp]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Every actual character's infinite Δ₁ series converges absolutely before
any finite character averaging or gcd reindexing is performed. -/
theorem proposition71_original_delta_one_series_summable {D p : ℕ} [NeZero p]
    (hD : 1<D) {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) (ψ : DirichletCharacter ℂ p) :
    Summable (proposition71DeltaOneDoubleTerm D
      (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*ψ (m : ZMod p))
      (lemma81PolynomialIndices D) (fun n => a₂ n*ψ⁻¹ (n : ZMod p)) (p : ℝ)) := by
  have hc (m : ℕ) (hm : 0<m) :
      ‖(lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*ψ (m : ZMod p)‖≤
        B₁*(lemma34Tau 5 m : ℝ) :=
    proposition71_twisted_coefficient_majorant _
      (fun m hm => proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB₁ a₁ ha₁.1 m) ψ m hm
  have hs := proposition71_front_coefficient_summable hB₁ _ hc (by norm_num : (1 : ℝ)<(3/2 : ℂ).re)
  exact (proposition71_actual_delta_one_double_series hD _ hs (lemma81PolynomialIndices D)
    (fun n hn => ((proposition71_mem_indices D n).mp hn).1) _
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p))).2.1

/-- The fully attached original analytic reduction to the true primitive Gauss
mean. This precedes Gauss averaging, conductor splitting and residue evaluation. -/
theorem proposition71_original_delta_one_reduction :
    ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖lemma81ThetaOne χ c a₁ a₂-proposition71OriginalDeltaOneMean D c a₁ a₂‖≤ε*lemma33ActualPrimeMass D := by
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨Nr,hNr,hreduce⟩ := proposition71_original_full_family_C_reduction B₁ B₂ hB₁ hB₂ (ε/2) (by positivity)
  let K := proposition71FrontErrorConstant*B₁*B₂
  have hK : 0<K := mul_pos (mul_pos proposition71_front_error_constant_pos hB₁) hB₂
  obtain ⟨Nl,hNl⟩ := exists_nat_gt (Real.exp 20000)
  obtain ⟨Ne,hNe⟩ := exists_nat_gt (2*K/ε)
  refine ⟨max Nr (max Nl Ne),hNr.trans (le_max_left _ _),?_⟩
  intro D hD χ hA c a₁ a₂ ha₁ ha₂
  have hDr := (le_max_left _ _).trans hD
  have hDl := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDe := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hD2 : 2≤D := hNr.trans hDr
  have hDpos : 1<D := by omega
  have hDp : 0<(D : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hDpos
  have hL : 20000≤lemma23PaperL D := by
    have hh : Real.exp 20000≤(D : ℝ) := hNl.le.trans (by exact_mod_cast hDl)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 20000) hh
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hLp : 0< lemma23PaperL D := by linarith
  have hrate : K/(D : ℝ)≤ε/2 := by
    have hh : 2*K/ε≤(D : ℝ) := hNe.le.trans (by exact_mod_cast hDe)
    have hh' := (div_le_iff₀ hε).mp hh
    apply (div_le_iff₀ hDp).mpr
    nlinarith
  letI : ∀ψ : lemma33CharacterIndex D, NeZero ψ.1.val := fun ψ =>
    ⟨(lemma33_mem_prime_window.mp ψ.1.property).1.ne_zero⟩
  have hΨ (ψ : lemma33CharacterIndex D) (hψ : ψ∈lemma33ActualFamily D) :
      Lemma23InPsi (D := D) ψ.2 := (lemma33_actual_family_mem ψ.1 ψ.2).mp hψ
  have hNP (ψ : lemma33CharacterIndex D) (_hψ : ψ∈lemma33ActualFamily D) :
      (ψ.1.val : ℝ)≤2*lemma23PaperP D^2 := by
    have hp : ψ.1.val∈lemma56PaperPrimes D := by simpa only [lemma35_prime_windows_eq] using ψ.1.property
    have hpp := proposition71_paper_prime_le_three_halves_P hL3 hp
    have hP1 : 1≤lemma23PaperP D := Real.one_le_exp (pow_nonneg hLp.le _)
    nlinarith
  let cl := fun (ψ : lemma33CharacterIndex D) (m : ℕ) =>
    (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*ψ.2 (m : ZMod ψ.1.val)
  let ar := fun (ψ : lemma33CharacterIndex D) (n : ℕ) => a₂ n*ψ.2⁻¹ (n : ZMod ψ.1.val)
  let w := fun ψ : lemma33CharacterIndex D => -I*
    (((ψ.1.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c
  have hc (ψ : lemma33CharacterIndex D) (_hψ : ψ∈lemma33ActualFamily D) (m : ℕ) (hm : 0<m) :
      ‖cl ψ m‖≤B₁*(lemma34Tau 5 m : ℝ) :=
    proposition71_twisted_coefficient_majorant _
      (fun m hm => proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB₁.le a₁ ha₁.1 m) ψ.2 m hm
  have hS (ψ : lemma33CharacterIndex D) (_hψ : ψ∈lemma33ActualFamily D) (n : ℕ)
      (hn : n∈lemma81PolynomialIndices D) : 0<n ∧ (n : ℝ)≤lemma23PaperP D := by
    have hh := (proposition71_mem_indices D n).mp hn
    exact ⟨hh.1,hh.2.le.trans (lemma81_cutoff_le_P hL3)⟩
  have har (ψ : lemma33CharacterIndex D) (_hψ : ψ∈lemma33ActualFamily D) (n : ℕ)
      (_hn : n∈lemma81PolynomialIndices D) : ‖ar ψ n‖≤B₂ := by
    dsimp [ar]
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (ψ.2⁻¹.norm_le_one _)).trans (ha₂.1 n)
  have hw (ψ : lemma33CharacterIndex D) (_hψ : ψ∈lemma33ActualFamily D) : ‖w ψ‖≤1 := by
    dsimp [w]
    rw [norm_mul,norm_neg,norm_I,lemma81_actual_phase_norm_one c hLp,one_mul]
  have hfront := proposition71_front_actual_family_rate hDpos hL (lemma33ActualFamily D) (fun _ h => h)
    (fun ψ => ψ.1.val) (fun ψ => ψ.2) (fun ψ hψ => (hΨ ψ hψ).2.1)
    (fun ψ hψ => (hΨ ψ hψ).1.ne_one) hNP hB₁.le hB₂.le (by norm_num : (0 : ℝ)≤1)
    cl ar hc (fun _ => lemma81PolynomialIndices D) hS har w hw
  let Cfull := ∑ψ∈lemma33ActualFamily D, lemma81NormalizedSegmentIntegral D 1 (lemma81CIntegrand D c ψ.2 a₁ a₂)
  have hdiff : ‖Cfull-proposition71OriginalDeltaOneMean D c a₁ a₂‖≤(K/(D : ℝ))*lemma33ActualPrimeMass D := by
    convert hfront using 1
    · dsimp [Cfull,proposition71OriginalDeltaOneMean]
      rw [←sum_sub_distrib]
      congr 1
      apply sum_congr rfl
      intro ψ hψ
      rw [proposition71_actual_C_strict_front_contour c a₁ a₂ ha₁ ψ.2]
      dsimp [cl,ar,w]
      ring
    · dsimp [K]
      ring
  have hM : 0≤lemma33ActualPrimeMass D := by unfold lemma33ActualPrimeMass; exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_right hrate hM)
  have hred := hreduce D hDr χ hA c a₁ a₂ ha₁ ha₂
  have htri := dist_triangle (lemma81ThetaOne χ c a₁ a₂) Cfull (proposition71OriginalDeltaOneMean D c a₁ a₂)
  simp only [dist_eq_norm] at htri
  exact htri.trans ((add_le_add hred hdiff').trans_eq (by ring))

end ZhangLS.Spec
