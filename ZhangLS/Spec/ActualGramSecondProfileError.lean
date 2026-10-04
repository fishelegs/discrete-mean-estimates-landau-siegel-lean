import ZhangLS.Spec.ActualGramFirstProfileError

/-! Actual xi-profile error, with the genuine Pi(d,r) and the negative mu=6
smoothing shift. Boundary and interior errors are taken from proved original
arbitrary-real-x inputs. No division by Pi or character value occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical Interval

theorem actualGram_second_profile_error_uniform (c : ℝ) (hc : 0<c) :
    ∃ N : ℕ, 2≤N ∧ ∀ D : ℕ, N≤D → ∀ χ : RealPrimitiveCharacter D,
    NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ d r : ℕ, 0<d → 0<r →
    (d*r : ℝ)<lemma23PaperP D*lemma56PaperT D^(-2 : ℤ) →
    ∀ g g' g'' : ℝ → ℂ, ∀ b C : ℝ, 0≤C →
    (∀ x, HasDerivAt g (g' x) x) → (∀ x, HasDerivAt g' (g'' x) x) → Continuous g'' →
    (∀ v, b≤v → g v=0) → g' b=0 →
    let B := Real.log (lemma23PaperP D)
    let t := Real.log (d*r : ℕ)/B
    let ell : ℂ := -(3*I*(Real.pi : ℂ)/2)
    t≤b →
    (∀ v ∈ Icc t b, ‖actualGramRampDensity ell g g' g'' v‖≤C) →
    (∀ v ∈ Icc t b, Real.exp (B*v)/(d*r : ℕ)<lemma81Cutoff D) →
    let G := -g' t+
      ((B : ℂ)*lemma83PaperBeta D c (j+1)+(B : ℂ)*lemma83PaperBeta D c (j+2))*g t+
      ((B : ℂ)*lemma83PaperBeta D c (j+1))*((B : ℂ)*lemma83PaperBeta D c (j+2))*
        (∫ u in t..b, g u)
    ‖actualGramSecond χ c j (fun n => g (Real.log n/B)) d r-
      (LDerivAtOne χ*lemma83Pi χ d r/(B : ℂ))*G‖ ≤
      (C*actualGramSecondBoundaryBudget χ d r*(Real.log (lemma56PaperT D)/B)+
        (C*3*lemma23PaperL D^(-5 : ℤ))*(b-t))/B := by
  obtain ⟨Ns,hNs,hs⟩ := actualGram_smoothing_errors_uniform c hc
  obtain ⟨Np,hNp,hp⟩ := lemma82_uniform_threshold c hc
  refine ⟨max Ns Np,hNs.trans (le_max_left _ _),?_⟩
  intro D hDN χ hA j d r hd hr hprod g g' g'' b C hC hg hg' hg'' hz hgpb
  dsimp only
  let B : ℝ := Real.log (lemma23PaperP D)
  let t : ℝ := Real.log (d*r : ℕ)/B
  let ell : ℂ := -(3*I*(Real.pi : ℂ)/2)
  let h := actualGramRampDensity ell g g' g''
  let K : ℝ → ℂ := fun v => lemma84XiSum χ c j 6 d r (Real.exp (B*v)/(d*r : ℕ))
  let M : ℝ → ℂ := fun v => lemma84MainTerm D c j 6 (Real.exp (B*v)/(d*r : ℕ))
  let A : ℂ := LDerivAtOne χ*lemma83Pi χ d r
  intro htb hbound hcut
  have hDs : Ns≤D := (le_max_left _ _).trans hDN
  have hDp : Np≤D := (le_max_right _ _).trans hDN
  have hparams := hp D hDp
  have hD : 1<D := by omega
  have hL : 2000≤lemma23PaperL D := hparams.2.1
  have hLp : 0<lemma23PaperL D := by linarith
  have hB : 0<B := actualGram_original_log_scale_pos hD
  have hqR : (0 : ℝ)<(d*r : ℕ) := by exact_mod_cast Nat.mul_pos hd hr
  have hell : (B : ℂ)*(-lemma84SmoothingBeta D 6)=ell := actualGram_original_mu6_negative_scaled hD
  have hT : 0≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    exact Real.rpow_nonneg (by linarith) _
  have hδ : 0≤Real.log (lemma56PaperT D)/B := div_nonneg hT hB.le
  have hcden : Continuous h := actualGram_ramp_density_continuous ell g g' g'' hg hg' hg''
  have hkc : ContinuousOn K (Icc t b) := by
    have hh := actualGram_log_smoothed_continuousOn D
      (fun n => χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r/(n : ℂ))
      (-lemma84SmoothingBeta D 6) hB hqR (fun v hv => (hcut v hv).le)
    simpa only [actualGram_log_kernel_second] using hh
  have hmc : Continuous M := by
    dsimp [M]
    simp_rw [actualGram_second_main_kernel D c j 6 (actualGram_mu6_nonzero hD) hB hqR]
    fun_prop
  have hie : IntervalIntegrable (fun v => h v*(K v-A*M v)) volume t b :=
    (hcden.continuousOn.mul (hkc.sub (continuous_const.mul hmc).continuousOn)).intervalIntegrable_of_Icc htb
  have hiK : IntervalIntegrable (fun v => h v*K v) volume t b :=
    (hcden.continuousOn.mul hkc).intervalIntegrable_of_Icc htb
  have hiM : IntervalIntegrable (fun v => h v*(A*M v)) volume t b :=
    (hcden.mul (continuous_const.mul hmc)).intervalIntegrable t b
  have hactual : actualGramSecond χ c j (fun n => g (Real.log n/B)) d r =
      (B : ℂ)⁻¹*(∫ v in t..b, h v*K v) := by
    have hh := actualGram_log_superposition_from_product D
      (fun n => χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r/(n : ℂ))
      (-lemma84SmoothingBeta D 6) g g' g'' hB hqR htb hg hg' hg'' hz hgpb
      (fun v hv => (hcut v hv).le)
    simpa only [actualGramSecond,t,h,K,Nat.cast_mul,actualGram_log_kernel_second,hell] using hh
  let G : ℂ := -g' t+
    ((B : ℂ)*lemma83PaperBeta D c (j+1)+(B : ℂ)*lemma83PaperBeta D c (j+2))*g t+
    ((B : ℂ)*lemma83PaperBeta D c (j+1))*((B : ℂ)*lemma83PaperBeta D c (j+2))*
      (∫ u in t..b, g u)
  have hmain : (∫ v in t..b, h v*M v)=G := by
    have hh := actualGram_second_main_superposition hD c j g g' g'' hB hqR
      hg hg' hg'' (hz b le_rfl) hgpb
    simpa only [hell] using hh
  have her : actualGramSecond χ c j (fun n => g (Real.log n/B)) d r-(A/(B : ℂ))*G =
      (B : ℂ)⁻¹*(∫ v in t..b, h v*(K v-A*M v)) := by
    have he : (fun v => h v*(K v-A*M v))=(fun v => h v*K v-h v*(A*M v)) := by funext v; ring
    rw [hactual,he,intervalIntegral.integral_sub hiK hiM]
    have hm : (∫ v in t..b, h v*(A*M v))=A*(∫ v in t..b, h v*M v) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v hv
      ring
    rw [hm,hmain]
    ring
  change ‖actualGramSecond χ c j (fun n => g (Real.log n/B)) d r-(A/(B : ℂ))*G‖≤_
  rw [her]
  have hbase : 0≤1+9*Real.log (lemma23PaperL D) := by
    have hh := Real.log_nonneg (by linarith : 1≤lemma23PaperL D)
    linarith
  have hE₀ : 0≤C*actualGramSecondBoundaryBudget χ d r := by
    apply mul_nonneg hC
    unfold actualGramSecondBoundaryBudget
    have := lemma84_boundary_xi_constant_pos
    positivity
  have hE₁ : 0≤C*3*lemma23PaperL D^(-5 : ℤ) := by positivity
  apply actualGram_scaled_moving_layer_bound _ htb hδ hE₀ hE₁ hB hie
  · intro v hv hsmallv
    have hb := (actualGram_log_moving_band hB hqR (show 0 < lemma56PaperT D from Real.exp_pos _) v).mpr ⟨hv.1,hsmallv⟩
    have hxP := (hcut v hv).trans_le (proposition71_cutoff_le_P D)
    have he := (hs D hDs χ hA j 6 d r (Or.inl rfl) hd hr hprod _ hb.1 hxP).2
    rw [if_pos hb.2] at he
    rw [norm_mul]
    exact mul_le_mul (hbound v hv) he (norm_nonneg _) hC
  · intro v hv hlargev
    have hx1 : 1≤Real.exp (B*v)/((d*r : ℕ) : ℝ) := by
      apply (le_div_iff₀ hqR).mpr
      have he : Real.log ((d*r : ℕ) : ℝ)≤B*v := by
        have hh := (div_le_iff₀ hB).mp hv.1
        simpa only [mul_comm] using hh
      simpa only [one_mul,Real.exp_log hqR] using Real.exp_le_exp.mpr he
    have hxT : ¬Real.exp (B*v)/((d*r : ℕ) : ℝ)≤lemma56PaperT D := by
      intro hn
      have hb := (actualGram_log_moving_band hB hqR (show 0 < lemma56PaperT D from Real.exp_pos _) v).mp ⟨hx1,hn⟩
      exact (not_le_of_gt hlargev) hb.2
    have hxP := (hcut v hv).trans_le (proposition71_cutoff_le_P D)
    have he := (hs D hDs χ hA j 6 d r (Or.inl rfl) hd hr hprod _ hx1 hxP).2
    rw [if_neg hxT] at he
    rw [norm_mul]
    exact (mul_le_mul (hbound v hv) he (norm_nonneg _) hC).trans_eq (by ring)

/-- A genuine main-profile norm bound at the unchanged original beta shifts.
The Volterra integral is bounded using the actual interval inside [0,1].
Pi(d,r) is retained as its norm and is never divided out. -/
theorem actualGram_second_profile_main_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) (d r : ℕ) (g g' : ℝ → ℂ) {t b C : ℝ}
    (ht : 0≤t) (htb : t≤b) (hb : b≤1) (hC : 0≤C)
    (hg : ∀ u ∈ Icc t b, ‖g u‖≤C) (hgp : ‖g' t‖≤C) :
    let B := Real.log (lemma23PaperP D)
    ‖(LDerivAtOne χ*lemma83Pi χ d r/(B : ℂ))*
      (-g' t+((B : ℂ)*lemma83PaperBeta D c (j+1)+(B : ℂ)*lemma83PaperBeta D c (j+2))*g t+
        ((B : ℂ)*lemma83PaperBeta D c (j+1))*((B : ℂ)*lemma83PaperBeta D c (j+2))*
          (∫ u in t..b, g u))‖ ≤
      ((16*Real.exp 1*lemma23PaperL D^2)*‖lemma83Pi χ d r‖/B)*
        (C*(1+8*Real.pi+16*Real.pi^2)) := by
  dsimp only
  let B : ℝ := Real.log (lemma23PaperP D)
  have hB : 0<B := actualGram_original_log_scale_pos hD
  have hbetas := lemma83_paper_beta_norm (by linarith : 3≤lemma23PaperL D) hc hsmall
  have halpha : 0≤lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha
    exact div_nonneg Real.pi_pos.le hB.le
  have hscaled (k : Fin 3) : ‖(B : ℂ)*lemma83PaperBeta D c k‖≤4*Real.pi := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
    calc
      _ ≤ B*(4*lemma44PaperAlpha D) := mul_le_mul_of_nonneg_left ((hbetas k).trans (by linarith)) hB.le
      _ = 4*Real.pi := by
        change B*(4*(Real.pi/B))=4*Real.pi
        field_simp [hB.ne'] <;> ring
  let a₁ := (B : ℂ)*lemma83PaperBeta D c (j+1)
  let a₂ := (B : ℂ)*lemma83PaperBeta D c (j+2)
  have hsum : ‖a₁+a₂‖≤8*Real.pi :=
    (norm_add_le _ _).trans ((add_le_add (hscaled (j+1)) (hscaled (j+2))).trans_eq (by ring))
  have hprod : ‖a₁*a₂‖≤16*Real.pi^2 := by
    rw [norm_mul]
    exact (mul_le_mul (hscaled (j+1)) (hscaled (j+2)) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hgt : ‖g t‖≤C := hg t ⟨le_rfl,htb⟩
  have hvolterra : ‖∫ u in t..b, g u‖≤C := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := b) (C := C) (f := g) (by
        intro u hu
        have hu' : u ∈ Ioc t b := by simpa only [Set.uIoc_of_le htb] using hu
        exact hg u ⟨hu'.1.le,hu'.2⟩)
    have hbound' : ‖∫ u in t..b, g u‖≤C*(b-t) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr htb)] using hbound
    exact hbound'.trans ((mul_le_mul_of_nonneg_left (by linarith : b-t≤1) hC).trans_eq (by ring))
  have hmain : ‖-g' t+(a₁+a₂)*g t+a₁*a₂*(∫ u in t..b, g u)‖≤
      C*(1+8*Real.pi+16*Real.pi^2) := by
    calc
      _ ≤ ‖-g' t‖+‖(a₁+a₂)*g t‖+‖a₁*a₂*(∫ u in t..b, g u)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C+(8*Real.pi)*C+(16*Real.pi^2)*C := by
        rw [norm_neg,norm_mul,norm_mul]
        exact add_le_add (add_le_add hgp
          (mul_le_mul hsum hgt (norm_nonneg _) (by positivity)))
          (mul_le_mul hprod hvolterra (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hder : ‖LDerivAtOne χ‖≤16*Real.exp 1*lemma23PaperL D^2 :=
    lemma32_actual_first_derivative_bound χ hD (by change 2≤lemma23PaperL D; linarith)
      (by simp; positivity)
  have hpref : ‖LDerivAtOne χ*lemma83Pi χ d r/(B : ℂ)‖≤
      (16*Real.exp 1*lemma23PaperL D^2)*‖lemma83Pi χ d r‖/B := by
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hder (norm_nonneg _)) hB.le
  rw [norm_mul]
  exact mul_le_mul hpref hmain (norm_nonneg _) (by positivity)

end ZhangLS.Spec
