import ZhangLS.Spec.Section15AnalyticFactorBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
set_option maxHeartbeats 2000000

lemma section15_alpha_le_L6 {D : ℕ} (hL : 1≤lemma23PaperL D) :
    lemma44PaperAlpha D≤Real.pi*lemma23PaperL D^(-6:ℤ) := by
  rw [paper_alpha_eq_L9]
  exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hL (by norm_num)) Real.pi_pos.le

lemma section15_alpha_logL_le_L6 {D : ℕ} (hL : 1≤lemma23PaperL D) :
    lemma44PaperAlpha D*Real.log (lemma23PaperL D)≤Real.pi*lemma23PaperL D^(-6:ℤ) := by
  have hL0 : 0<lemma23PaperL D := by linarith
  have hlog : Real.log (lemma23PaperL D)≤lemma23PaperL D := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  rw [paper_alpha_eq_L9]
  calc
    _ ≤ Real.pi*lemma23PaperL D^(-9:ℤ)*lemma23PaperL D := by gcongr
    _ = Real.pi*lemma23PaperL D^(-8:ℤ) := by
      rw [mul_assoc]
      congr 1
      simpa using (zpow_add₀ hL0.ne' (-9) 1).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hL (by norm_num)) Real.pi_pos.le

lemma section15_actual_delta_error_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → 3≤lemma23PaperL D ∧
      ‖lemma54PaperDeltaMellin D 1-1‖≤
        (lemma54Constant*Real.pi)*lemma23PaperL D^(-6:ℤ) := by
  obtain ⟨D₁,hD₁⟩ := lemma54_uniform_constants
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨D₂,hD₂⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (3:ℝ)))
  refine ⟨max D₁ D₂,?_⟩
  intro D hD
  have hL := hD₂ D ((le_max_right _ _).trans hD)
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hd := (hD₁ D ((le_max_left _ _).trans hD)).2.2 1 (by simpa using (show 0<10*lemma44PaperAlpha D by positivity))
  refine ⟨hL,hd.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left (section15_alpha_logL_le_L6 (by linarith : 1≤lemma23PaperL D)) lemma54_constant_pos.le
  simpa only [mul_assoc] using hh

lemma section15_omega_small_error {D : ℕ} (hL : 1≤lemma23PaperL D)
    {z : ℂ} (hz : ‖z‖≤1) : ‖lemma57OmegaOne D z-1‖≤‖z‖^2/2 := by
  have hL0 : 0≤lemma23PaperL D := by linarith
  have hp : 1≤lemma23PaperL D^30 := one_le_pow₀ hL
  have hnorm : ‖z^2/(4*(Real.log (D:ℝ):ℂ)^30)‖=‖z‖^2/(4*lemma23PaperL D^30) := by
    simp only [norm_div,norm_mul,norm_pow,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (show 0≤Real.log (D:ℝ) from hL0)]
    rfl
  have he : ‖z^2/(4*(Real.log (D:ℝ):ℂ)^30)‖≤‖z‖^2/4 := by
    rw [hnorm]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
    nlinarith
  have he1 : ‖z^2/(4*(Real.log (D:ℝ):ℂ)^30)‖≤1 := by
    have hh : ‖z‖^2≤1 := by nlinarith [norm_nonneg z]
    linarith
  exact (Complex.norm_exp_sub_one_le he1).trans (by linarith)

lemma section15_actual_omega_error {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖lemma57OmegaOne D (lemma83PaperBeta D c 2-lemma83PaperBeta D c j)-1‖≤
      (18*Real.pi^2)*lemma23PaperL D^(-6:ℤ) := by
  have ha := (lemma44_alpha_pos_le_one hL).1
  have has := lemma152_alpha_le_hundredth hL
  have hb := lemma83_paper_beta_norm hL hc hsmall j
  have hb2 := lemma83_paper_beta_norm hL hc hsmall 2
  have hz : ‖lemma83PaperBeta D c 2-lemma83PaperBeta D c j‖≤6*lemma44PaperAlpha D :=
    (norm_sub_le _ _).trans (by linarith)
  have he := section15_omega_small_error (by linarith : 1≤lemma23PaperL D) (hz.trans (by linarith))
  have hLp : 0<lemma23PaperL D := by linarith
  calc
    _ ≤ ‖lemma83PaperBeta D c 2-lemma83PaperBeta D c j‖^2/2 := he
    _ ≤ (6*lemma44PaperAlpha D)^2/2 := by gcongr
    _ = (18*Real.pi^2)*lemma23PaperL D^(-18:ℤ) := by
      rw [paper_alpha_eq_L9]
      rw [show (6*(Real.pi*lemma23PaperL D^(-9:ℤ)))^2/2 =
        (18*Real.pi^2)*(lemma23PaperL D^(-9:ℤ)*lemma23PaperL D^(-9:ℤ)) by ring,
        ←zpow_add₀ hLp.ne']
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by linarith : 1≤lemma23PaperL D) (by norm_num)) (by positivity)

lemma section15_actual_zeta_factor_errors {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j k : Fin 3) :
    ‖zetaPoleRemoved (1-lemma83PaperBeta D c j+lemma83PaperBeta D c k)-1‖≤
      (30*Real.pi)*lemma23PaperL D^(-6:ℤ) ∧
    ‖zetaPoleRemoved (1-lemma83PaperBeta D c j)-1‖≤
      (15*Real.pi)*lemma23PaperL D^(-6:ℤ) := by
  have ha := (lemma44_alpha_pos_le_one hL).1
  have has := lemma152_alpha_le_hundredth hL
  have hj := lemma83_paper_beta_norm hL hc hsmall j
  have hk := lemma83_paper_beta_norm hL hc hsmall k
  have hdiff : ‖(1-lemma83PaperBeta D c j+lemma83PaperBeta D c k)-1‖≤6*lemma44PaperAlpha D := by
    rw [show (1-lemma83PaperBeta D c j+lemma83PaperBeta D c k)-1=lemma83PaperBeta D c k-lemma83PaperBeta D c j by ring]
    exact (norm_sub_le _ _).trans (by linarith)
  have hb : ‖(1-lemma83PaperBeta D c j)-1‖≤3*lemma44PaperAlpha D := by simpa using hj
  have hal := section15_alpha_le_L6 (by linarith : 1≤lemma23PaperL D)
  constructor
  · calc
      _ ≤ 5*‖(1-lemma83PaperBeta D c j+lemma83PaperBeta D c k)-1‖ := section15_zeta_regular_error (hdiff.trans (by linarith))
      _ ≤ 5*(6*lemma44PaperAlpha D) := by gcongr
      _ ≤ _ := by nlinarith only [hal]
  · calc
      _ ≤ 5*‖(1-lemma83PaperBeta D c j)-1‖ := section15_zeta_regular_error (hb.trans (by linarith))
      _ ≤ 5*(3*lemma44PaperAlpha D) := by gcongr
      _ ≤ _ := by nlinarith only [hal]

lemma section15_mul_error {x y : ℂ} {a e : ℝ}
    (hx : ‖x-1‖≤a*e) (hy : ‖y-1‖≤e) (he : e≤1) :
    ‖x*y-1‖≤(2*a+1)*e := by
  have he0 : 0≤e := (norm_nonneg _).trans hy
  have hay : 0≤a*e := (norm_nonneg _).trans hx
  have hn : ‖y‖≤2 := by
    calc
      _ = ‖(y-1)+1‖ := by simp
      _ ≤ ‖y-1‖+‖(1:ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  rw [show x*y-1=(x-1)*y+(y-1) by ring]
  calc
    _ ≤ ‖(x-1)*y‖+‖y-1‖ := norm_add_le _ _
    _ = ‖x-1‖*‖y‖+‖y-1‖ := by rw [norm_mul]
    _ ≤ (a*e)*2+e := add_le_add (mul_le_mul hx hn (norm_nonneg _) hay) hy
    _ = _ := by ring

lemma section15_eight_factor_error (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : ℂ) {e : ℝ}
    (h₁ : ‖x₁-1‖≤e) (h₂ : ‖x₂-1‖≤e) (h₃ : ‖x₃-1‖≤e) (h₄ : ‖x₄-1‖≤e)
    (h₅ : ‖x₅-1‖≤e) (h₆ : ‖x₆-1‖≤e) (h₇ : ‖x₇-1‖≤e) (h₈ : ‖x₈-1‖≤e)
    (he : e≤1) :
    ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈-1‖≤255*e := by
  have h12 := section15_mul_error (a := 1) (by simpa using h₁) h₂ he
  have h123 := section15_mul_error h12 h₃ he
  have h1234 := section15_mul_error h123 h₄ he
  have h12345 := section15_mul_error h1234 h₅ he
  have h123456 := section15_mul_error h12345 h₆ he
  have h1234567 := section15_mul_error h123456 h₇ he
  have h12345678 := section15_mul_error h1234567 h₈ he
  norm_num at h12345678
  exact h12345678

end ZhangLS.Spec
