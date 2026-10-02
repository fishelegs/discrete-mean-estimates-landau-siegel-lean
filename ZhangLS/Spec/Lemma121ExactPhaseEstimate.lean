import ZhangLS.Spec.Lemma121FiniteBridge

/-! Actual finite-sum error bound retaining the exact oscillatory phase.
No assumed character-sum estimate or result-shaped hypothesis is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

lemma lemma121_kernel_sum_analytic_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) {A B Q d : ℝ} (hA : 0<A) (hB : 0<B) (hd : A<d)
    (hQ : 0<Q) (hAB : A≤B) (hx : 1≤B/d) (a b : ℂ)
    (ha : a.re=0) (hb : b.re=0) (hsn : ‖1+b-a‖≤2) :
    ‖(∑ n ∈ lemma82StrictCutoff (B/d),
        χ.evalNat n*lemma121Kernel A B Q b (d*(n:ℝ))/(n:ℂ)^(1-a)) -
      (((d/A:ℝ):ℂ)^(-b)/(Q:ℂ))*
        ((Real.log (d/A):ℂ)*dirichletLFunction χ (1+b-a)-
          deriv (dirichletLFunction χ) (1+b-a))‖ ≤
      (4*Real.log (B/A)+16)*(D:ℝ)/(Q*(B/d)) := by
  have hdp : 0<d := hA.trans hd
  have hxp : 0<B/d := div_pos hB hdp
  have hlog : 0≤Real.log (B/A) := Real.log_nonneg ((one_le_div hA).mpr hAB)
  have hs : (1+b-a).re=1 := by simp [ha,hb]
  have hf := lemma121_strict_polynomial_error χ hD hx hs hsn
  have hw := lemma82_weighted_abel_error χ hD hx hs hsn
  have hlogeq : Real.log (B/A)-Real.log (B/d)=Real.log (d/A) := by
    rw [Real.log_div hB.ne' hA.ne',Real.log_div hB.ne' hdp.ne',Real.log_div hdp.ne' hA.ne']
    ring
  have hlogeqC : (Real.log (B/A):ℂ)-(Real.log (B/d):ℂ)=(Real.log (d/A):ℂ) := by
    exact_mod_cast hlogeq
  rw [lemma121_kernel_sum_exact χ hA hB hd a b,← mul_sub,norm_mul,norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hdp hA),Complex.neg_re,hb,
    neg_zero,Real.rpow_zero,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ]
  have he : (Real.log (B/A):ℂ)*lemma121StrictPolynomial χ (B/d) (1+b-a)-
      lemma82WeightedPolynomial χ (B/d) (1+b-a)-
      ((Real.log (d/A):ℂ)*dirichletLFunction χ (1+b-a)-deriv (dirichletLFunction χ) (1+b-a)) =
      (Real.log (B/A):ℂ)*(lemma121StrictPolynomial χ (B/d) (1+b-a)-dirichletLFunction χ (1+b-a))-
      (lemma82WeightedPolynomial χ (B/d) (1+b-a)-
        ((Real.log (B/d):ℂ)*dirichletLFunction χ (1+b-a)+deriv (dirichletLFunction χ) (1+b-a))) := by
    rw [← hlogeqC]
    ring
  rw [he]
  have hf' : ‖(Real.log (B/A):ℂ)*(lemma121StrictPolynomial χ (B/d) (1+b-a)-dirichletLFunction χ (1+b-a))‖≤
      Real.log (B/A)*(4*(D:ℝ)/(B/d)) := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog] using
      mul_le_mul_of_nonneg_left hf hlog
  have hh := (norm_sub_le _ _).trans (add_le_add hf' hw)
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤1/Q)).trans_eq
  field_simp

lemma lemma121_local_negative_derivative_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {y : ℝ} (hy : 1≤y) (hyP : y<lemma23PaperP D) {s : ℂ}
    (hs : ‖s-1‖≤10*lemma44PaperAlpha D) :
    ‖(Real.log y:ℂ)*dirichletLFunction χ s-deriv (dirichletLFunction χ) s-
      LDerivAtOne χ*(-1+(s-1)*(Real.log y:ℂ))‖≤
      lemma82LocalErrorConstant*lemma23PaperL D^(-6:ℤ) := by
  let L := lemma23PaperL D
  have hLp : 0<L := by dsimp [L]; linarith
  have hl : 0≤Real.log y := Real.log_nonneg hy
  have hlu : Real.log y≤L^9 := by
    have hh := Real.log_lt_log (zero_lt_one.trans_le hy) hyP
    simpa [lemma23PaperP,L] using hh.le
  have hv := lemma58_actual_full_disk_linear_error χ hD hL hA hs
  have hd := lemma55_actual_first_derivative_variation χ hD (by change 2≤lemma23PaperL D; linarith)
    (hs.trans (lemma58_original_radius_in_taylor_disk hL))
  have hs' : ‖s-1‖≤(10*Real.pi)*L^(-9:ℤ) := by
    simpa [lemma58_alpha_eq_log_power,L,lemma23PaperL,mul_assoc] using hs
  have hp1 : L^9*L^(-15:ℤ)=L^(-6:ℤ) := by
    rw [← zpow_natCast L 9,← zpow_add₀ hLp.ne']; norm_num
  have hp2 : L^3*L^(-9:ℤ)=L^(-6:ℤ) := by
    rw [← zpow_natCast L 3,← zpow_add₀ hLp.ne']; norm_num
  have hv' : Real.log y*‖dirichletLFunction χ s-LDerivAtOne χ*(s-1)‖≤
      lemma58ErrorConstant*L^(-6:ℤ) := by
    calc
      _ ≤ L^9*(lemma58ErrorConstant*L^(-15:ℤ)) :=
        mul_le_mul hlu hv (norm_nonneg _) (by positivity [lemma58_error_constant_pos])
      _ = _ := by rw [← mul_assoc,mul_comm (L^9) lemma58ErrorConstant,mul_assoc,hp1]
  have hd' : ‖deriv (dirichletLFunction χ) s-LDerivAtOne χ‖≤
      (128*Real.exp 1*(10*Real.pi))*L^(-6:ℤ) := by
    apply hd.trans
    calc
      _ ≤ (128*Real.exp 1*L^3)*((10*Real.pi)*L^(-9:ℤ)) :=
        mul_le_mul_of_nonneg_left hs' (by positivity)
      _ = _ := by rw [show (128*Real.exp 1*L^3)*((10*Real.pi)*L^(-9:ℤ))=
          (128*Real.exp 1*(10*Real.pi))*(L^3*L^(-9:ℤ)) by ring,hp2]
  rw [show (Real.log y:ℂ)*dirichletLFunction χ s-deriv (dirichletLFunction χ) s-
      LDerivAtOne χ*(-1+(s-1)*(Real.log y:ℂ)) =
      (Real.log y:ℂ)*(dirichletLFunction χ s-LDerivAtOne χ*(s-1))-
        (deriv (dirichletLFunction χ) s-LDerivAtOne χ) by ring]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl]
  apply (add_le_add hv' hd').trans_eq
  unfold lemma82LocalErrorConstant
  ring

/-- Honest exact-phase high-range estimate with explicit endpoint geometry.
This is a theorem about the actual κ13 sum, not an abstract error model. -/
theorem lemma121_actual_exact_phase_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) {d : ℝ}
    (hlo : 0<lemma121PDoublePrimeOne D)
    (hhi : 0<lemma121PDoublePrimeTwo D)
    (hd : lemma121PDoublePrimeOne D<d)
    (hQ : 0<Real.log (lemma121P1 D))
    (hAB : lemma121PDoublePrimeOne D≤lemma121PDoublePrimeTwo D)
    (hx : 1≤lemma121PDoublePrimeTwo D/d)
    (hyP : d/lemma121PDoublePrimeOne D<lemma23PaperP D) :
    ‖lemma121Sum χ c j d-lemma121ExactMain χ c j d‖≤
      (4*Real.log (lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D)+16)*(D:ℝ)/
        (Real.log (lemma121P1 D)*(lemma121PDoublePrimeTwo D/d)) +
      lemma82LocalErrorConstant*lemma23PaperL D^(-6:ℤ)/Real.log (lemma121P1 D) := by
  let A := lemma121PDoublePrimeOne D
  let B := lemma121PDoublePrimeTwo D
  let Q := Real.log (lemma121P1 D)
  let a := lemma82PaperBeta D c j
  let b := lemma82SmoothingBeta D 6
  let F := ((d/A:ℝ):ℂ)^(-b)/(Q:ℂ)
  let s := 1+b-a
  have hdp : 0<d := hlo.trans hd
  have hy : 1≤d/A := (one_le_div hlo).mpr hd.le
  have hshift := lemma82_shift_in_disk hL hc hsmall j 6
  have hh := lemma121_kernel_sum_analytic_error χ hD hlo hhi hd hQ hAB hx a b
    (lemma82_beta_re D c j) (lemma82_smoothing_beta_re D 6) hshift.2
  have hl := lemma121_local_negative_derivative_error χ hD hL hA hy hyP hshift.1
  have hF : ‖F‖=1/Q := by
    dsimp [F,b]
    rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hdp hlo),Complex.neg_re,
      lemma82_smoothing_beta_re,neg_zero,Real.rpow_zero,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ]
  have hp : lemma121ExactMain χ c j d =
      F*(LDerivAtOne χ*(-1+(s-1)*(Real.log (d/A):ℂ))) := by
    unfold lemma121ExactMain lemma121Phase
    have he : ((d/A:ℝ):ℂ)^(-b)=Complex.exp (-b*(Real.log (d/A):ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hdp hlo).ne'),
        ← Complex.ofReal_log (div_pos hdp hlo).le]
      congr 1
      ring
    dsimp [F,s]
    rw [he]
    dsimp [A,Q,a,b]
    ring
  have hferr : ‖F*((Real.log (d/A):ℂ)*dirichletLFunction χ s-deriv (dirichletLFunction χ) s)-
      lemma121ExactMain χ c j d‖≤lemma82LocalErrorConstant*lemma23PaperL D^(-6:ℤ)/Q := by
    rw [hp,← mul_sub,norm_mul,hF]
    apply (mul_le_mul_of_nonneg_left hl (by positivity : 0≤1/Q)).trans_eq
    ring
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (F*((Real.log (d/A):ℂ)*dirichletLFunction χ s-deriv (dirichletLFunction χ) s)) _).trans
      (add_le_add hh hferr)

end ZhangLS.Spec
