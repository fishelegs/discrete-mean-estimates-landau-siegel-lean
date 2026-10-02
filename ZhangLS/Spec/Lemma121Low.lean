import ZhangLS.Spec.Lemma121LowBridge

/-! The original low-range exponential branch of Lemma 12.1. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Real

lemma lemma121_kernel_sum_low_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) {A B Q d : ℝ} (hA : 0<A) (hB : 0<B) (hd : 0<d)
    (hAB : A≤B) (hQ : 1≤Q) (hlogQ : Real.log (B/A)≤Q) (hx : 1≤A/d)
    (a b : ℂ) (ha : a.re=0) (hb : b.re=0) (hsn : ‖1+b-a‖≤2) :
    ‖∑ n ∈ lemma82StrictCutoff (B/d),
      χ.evalNat n*lemma121Kernel A B Q b (d*(n:ℝ))/(n:ℂ)^(1-a)‖≤36*(D:ℝ)/(A/d) := by
  have hxp : 0<A/d := div_pos hA hd
  have hxB : 0<B/d := div_pos hB hd
  have hxy : A/d≤B/d := div_le_div_of_nonneg_right hAB hd.le
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  have hl0 : 0≤Real.log (B/A) := Real.log_nonneg ((one_le_div hA).mpr hAB)
  have hs : (1+b-a).re=1 := by simp [ha,hb]
  have ht : (D:ℝ)/(B/d)≤(D:ℝ)/(A/d) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg D) hxp hxy
  have hf : ‖lemma121StrictPolynomial χ (B/d) (1+b-a)-dirichletLFunction χ (1+b-a)‖≤
      4*((D:ℝ)/(A/d)) := by
    apply (lemma121_strict_polynomial_error χ hD (hx.trans hxy) hs hsn).trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ht (by norm_num)
  have hwB : ‖lemma82WeightedPolynomial χ (B/d) (1+b-a)-
      ((Real.log (B/d):ℂ)*dirichletLFunction χ (1+b-a)+deriv (dirichletLFunction χ) (1+b-a))‖≤
      16*((D:ℝ)/(A/d)) := by
    apply (lemma82_weighted_abel_error χ hD (hx.trans hxy) hs hsn).trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ht (by norm_num)
  have hwA : ‖lemma82WeightedPolynomial χ (A/d) (1+b-a)-
      ((Real.log (A/d):ℂ)*dirichletLFunction χ (1+b-a)+deriv (dirichletLFunction χ) (1+b-a))‖≤
      16*((D:ℝ)/(A/d)) := by
    simpa [mul_div_assoc] using lemma82_weighted_abel_error χ hD hx hs hsn
  have hlog : Real.log (B/A)-Real.log (B/d)+Real.log (A/d)=0 := by
    rw [Real.log_div hB.ne' hA.ne',Real.log_div hB.ne' hd.ne',Real.log_div hA.ne' hd.ne']
    ring
  have hlogC : (Real.log (B/A):ℂ)-(Real.log (B/d):ℂ)+(Real.log (A/d):ℂ)=0 := by
    exact_mod_cast hlog
  rw [lemma121_kernel_sum_all_ranges χ hA hB hAB hd a b,norm_mul,norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hd hA),Complex.neg_re,hb,
    neg_zero,Real.rpow_zero,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQp]
  have he : (Real.log (B/A):ℂ)*lemma121StrictPolynomial χ (B/d) (1+b-a)-
      lemma82WeightedPolynomial χ (B/d) (1+b-a)+lemma82WeightedPolynomial χ (A/d) (1+b-a) =
      (Real.log (B/A):ℂ)*(lemma121StrictPolynomial χ (B/d) (1+b-a)-dirichletLFunction χ (1+b-a))-
      (lemma82WeightedPolynomial χ (B/d) (1+b-a)-
        ((Real.log (B/d):ℂ)*dirichletLFunction χ (1+b-a)+deriv (dirichletLFunction χ) (1+b-a)))+
      (lemma82WeightedPolynomial χ (A/d) (1+b-a)-
        ((Real.log (A/d):ℂ)*dirichletLFunction χ (1+b-a)+deriv (dirichletLFunction χ) (1+b-a))) := by
    linear_combination dirichletLFunction χ (1+b-a)*hlogC
  rw [he]
  have hf' : ‖(Real.log (B/A):ℂ)*(lemma121StrictPolynomial χ (B/d) (1+b-a)-dirichletLFunction χ (1+b-a))‖≤
      Real.log (B/A)*(4*((D:ℝ)/(A/d))) := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl0] using
      mul_le_mul_of_nonneg_left hf hl0
  have hh := (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add hf' hwB)) hwA)
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤1/Q)).trans
  have hc : (4*Real.log (B/A)+32)/Q≤36 := by
    apply (div_le_iff₀ hQp).mpr
    linarith only [hlogQ,hQ]
  calc
    _ = ((4*Real.log (B/A)+32)/Q)*((D:ℝ)/(A/d)) := by ring
    _ ≤ 36*((D:ℝ)/(A/d)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

lemma lemma121_low_exponential_estimate {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (htail : (D:ℝ)/lemma56PaperT D≤lemma56PaperT D^(-(1/2:ℝ)))
    (j : Fin 3) {d : ℝ} (hd : 0<d)
    (hcut : d≤lemma121PDoublePrimeOne D/lemma56PaperT D) :
    ‖lemma121Sum χ c j d‖≤36*lemma56PaperT D^(-(1/2:ℝ)) := by
  have hg := lemma121_endpoint_geometry hD hL
  have hLp : 0<lemma23PaperL D := by linarith
  have hT : 1<lemma56PaperT D := Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hLp _)
  have hTp : 0<lemma56PaperT D := zero_lt_one.trans hT
  have hx : lemma56PaperT D≤lemma121PDoublePrimeOne D/d := by
    apply (le_div_iff₀ hd).mpr
    have hh := (le_div_iff₀ hTp).mp hcut
    simpa only [mul_comm] using hh
  have hs := lemma82_shift_in_disk hL hc hsmall j 6
  have he := lemma121_kernel_sum_low_error χ hD hg.1 hg.2.1 hd hg.2.2.1 hg.2.2.2.2.1
    hg.2.2.2.2.2.2 (hT.le.trans hx) (lemma82PaperBeta D c j) (lemma82SmoothingBeta D 6)
    (lemma82_beta_re D c j) (lemma82_smoothing_beta_re D 6) hs.2
  change ‖lemma121Sum χ c j d‖≤36*(D:ℝ)/(lemma121PDoublePrimeOne D/d) at he
  apply he.trans
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (div_le_div_of_nonneg_left (Nat.cast_nonneg D) hTp hx).trans htail

lemma lemma121_exponential_absorption_eventually :
    ∀ᶠ D : ℕ in atTop, (D:ℝ)/lemma56PaperT D≤lemma56PaperT D^(-(1/2:ℝ)) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp ht).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (2:ℕ),ht.eventually_ge_atTop 1,hr] with D hD hL hr
  have hLp : 0<lemma23PaperL D := by linarith
  have hTp : 0<lemma56PaperT D := Real.exp_pos _
  have hp : lemma23PaperL D≤lemma23PaperL D^(11/10:ℝ)*(1/2) := by
    change 2≤lemma23PaperL D^(1/10:ℝ) at hr
    rw [show (11/10:ℝ)=1+1/10 by norm_num,Real.rpow_add hLp,Real.rpow_one]
    nlinarith only [hr,mul_le_mul_of_nonneg_left hr hLp.le]
  have hDp : (0:ℝ)<D := by exact_mod_cast (by omega : 0<D)
  have hd : (D:ℝ)≤lemma56PaperT D^(1/2:ℝ) := by
    rw [lemma56PaperT,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    conv_lhs => rw [← Real.exp_log hDp]
    exact Real.exp_le_exp.mpr hp
  calc
    (D:ℝ)/lemma56PaperT D≤lemma56PaperT D^(1/2:ℝ)/lemma56PaperT D :=
      div_le_div_of_nonneg_right hd hTp.le
    _ = lemma56PaperT D^(-(1/2:ℝ)) := by
      calc
        _ = lemma56PaperT D^(1/2:ℝ)/lemma56PaperT D^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hTp]; norm_num

/-- Original low branch, with explicit positive absolute constants. -/
def Lemma121LowTarget : Prop :=
  ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      ∀ j : Fin 3, ∀ d : ℕ, 1≤d → (d:ℝ)≤lemma121PDoublePrimeOne D/lemma56PaperT D →
      ‖lemma121Sum χ c j d‖≤C*lemma56PaperT D^(-κ)

/-- This branch needs no Assumption (A); it follows from actual periodic
character cancellation and the exact finite kernel identity. -/
theorem lemma121_low_proved : Lemma121LowTarget := by
  refine ⟨36,1/2,by norm_num,by norm_num,?_⟩
  intro c hc
  obtain ⟨N,hN,hh⟩ := lemma82_uniform_threshold c hc
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp lemma121_exponential_absorption_eventually
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hDN χ j d hd hdhi
  have hn := hh D ((le_max_left N M).trans hDN)
  have hm := hM D ((le_max_right N M).trans hDN)
  exact lemma121_low_exponential_estimate χ (by omega) hn.2.1 hc hn.2.2.1 hm j
    (by exact_mod_cast (show 0<d by omega)) hdhi

end ZhangLS.Spec
