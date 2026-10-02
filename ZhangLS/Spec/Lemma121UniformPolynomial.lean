import ZhangLS.Spec.Lemma121Low
import Mathlib.NumberTheory.Harmonic.Bounds
import ZhangLS.Spec.Lemma32LocalL

/-! General actual shifted polynomial bounds used by the transition branch. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

lemma lemma121_weighted_trivial {D : ℕ} (χ : RealPrimitiveCharacter D)
    {x : ℝ} (hx : 1≤x) {s : ℂ} (hs : s.re=1) :
    ‖lemma82WeightedPolynomial χ x s‖≤Real.log x*(1+Real.log x) := by
  have hxp : 0<x := zero_lt_one.trans_le hx
  have hlog : 0≤Real.log x := Real.log_nonneg hx
  have hh : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n:ℝ)⁻¹)≤1+Real.log x := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using
      harmonic_floor_le_one_add_log x hx
  calc
    ‖lemma82WeightedPolynomial χ x s‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ‖χ.evalNat n*(n:ℂ)^(-s)*(Real.log (x/(n:ℝ)):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x*(n:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn1 : (1:ℝ)≤n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnx : (n:ℝ)≤x := (Nat.le_floor_iff hxp.le).mp (Finset.mem_Icc.mp hn).2
      have hnl : 0≤Real.log (x/(n:ℝ)) := Real.log_nonneg ((le_div_iff₀ hn0).mpr (by simpa using hnx))
      have hnl' : Real.log (x/(n:ℝ))≤Real.log x := by
        rw [Real.log_div hxp.ne' hn0.ne']
        linarith [Real.log_nonneg hn1]
      rw [norm_mul,norm_mul,← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hn0,
        Complex.neg_re,hs,Real.rpow_neg_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnl]
      calc
        _ ≤ 1*(n:ℝ)⁻¹*Real.log x := by gcongr; exact χ.evalNat_norm_le_one n
        _ = _ := by ring
    _ = Real.log x*(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n:ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh hlog

noncomputable def lemma121WeightedConstant : ℝ :=
  18+lemma82LocalErrorConstant+16*Real.exp 1*(1+10*Real.pi)

lemma lemma121_weighted_constant_pos : 0<lemma121WeightedConstant := by
  unfold lemma121WeightedConstant
  positivity [lemma82_local_error_constant_pos]

lemma lemma121_weighted_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {x : ℝ} (hx : 1≤x) (hxp : x<lemma23PaperP D) {s : ℂ}
    (hs : s.re=1) (hsn : ‖s‖≤2) (hshift : ‖s-1‖≤10*lemma44PaperAlpha D) :
    ‖lemma82WeightedPolynomial χ x s‖≤lemma121WeightedConstant*lemma23PaperL D^2 := by
  let L := lemma23PaperL D
  have hLp : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have hxx : 0<x := zero_lt_one.trans_le hx
  by_cases hDx : x≤(D:ℝ)
  · have hh := lemma121_weighted_trivial χ hx hs
    have hlx : Real.log x≤L := Real.log_le_log hxx hDx
    have hlog : 0≤Real.log x := Real.log_nonneg hx
    have hC2 : 2≤lemma121WeightedConstant := by
      unfold lemma121WeightedConstant
      have hp : 0≤16*Real.exp 1*(1+10*Real.pi) := by positivity
      have hc := lemma82_local_error_constant_pos
      linarith
    calc
      _ ≤ Real.log x*(1+Real.log x) := hh
      _ ≤ L*(1+L) := by gcongr
      _ ≤ 2*L^2 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2 (sq_nonneg L)
  have hDx' : (D:ℝ)≤x := (lt_of_not_ge hDx).le
  have he := (norm_sub_le_norm_sub_add_norm_sub (lemma82WeightedPolynomial χ x s)
    ((Real.log x:ℂ)*dirichletLFunction χ s+deriv (dirichletLFunction χ) s)
    (LDerivAtOne χ*(1+(s-1)*(Real.log x:ℂ)))).trans
    (add_le_add (lemma82_weighted_abel_error χ hD hx hs hsn)
      (lemma82_local_analytic_error χ hD hL hA hx hxp hshift))
  have htail : 16*(D:ℝ)/x≤16 := by
    rw [mul_div_assoc]
    exact mul_le_of_le_one_right (by norm_num) ((div_le_one hxx).mpr hDx')
  have hpow : L^(-6:ℤ)≤L^2 := by
    rw [← zpow_natCast L 2]
    exact zpow_le_zpow_right₀ hL1 (by norm_num)
  have hder : ‖LDerivAtOne χ‖≤16*Real.exp 1*L^2 :=
    lemma32_actual_first_derivative_bound χ hD (by change 2≤lemma23PaperL D; linarith)
      (by simp; positivity)
  have hlog : 0≤Real.log x := Real.log_nonneg hx
  have hlog' : Real.log x≤L^9 := by
    have hh := Real.log_lt_log hxx hxp
    simpa [lemma23PaperP,L] using hh.le
  have hprod : ‖s-1‖*Real.log x≤10*Real.pi := by
    calc
      _ ≤ (10*lemma44PaperAlpha D)*L^9 := mul_le_mul hshift hlog' hlog ((norm_nonneg _).trans hshift)
      _ = _ := by
        rw [lemma58_alpha_eq_log_power]
        change (10*(Real.pi*L^(-9:ℤ)))*L^9=10*Real.pi
        rw [zpow_neg,zpow_ofNat]
        field_simp
  have hm : ‖LDerivAtOne χ*(1+(s-1)*(Real.log x:ℂ))‖≤
      (16*Real.exp 1*(1+10*Real.pi))*L^2 := by
    rw [norm_mul]
    have hh : ‖1+(s-1)*(Real.log x:ℂ)‖≤1+10*Real.pi := by
      apply (norm_add_le _ _).trans
      rw [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
      linarith
    calc
      _ ≤ (16*Real.exp 1*L^2)*(1+10*Real.pi) := mul_le_mul hder hh (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ‖lemma82WeightedPolynomial χ x s-LDerivAtOne χ*(1+(s-1)*(Real.log x:ℂ))‖+
        ‖LDerivAtOne χ*(1+(s-1)*(Real.log x:ℂ))‖ := norm_le_norm_sub_add _ _
    _ ≤ 16+lemma82LocalErrorConstant*L^2+(16*Real.exp 1*(1+10*Real.pi))*L^2 :=
      add_le_add (he.trans (add_le_add htail
        (mul_le_mul_of_nonneg_left hpow lemma82_local_error_constant_pos.le))) hm
    _ ≤ lemma121WeightedConstant*L^2 := by
      unfold lemma121WeightedConstant
      have hL2 : 1≤L^2 := one_le_pow₀ hL1
      nlinarith

noncomputable def lemma121UnweightedConstant : ℝ :=
  4+lemma58ErrorConstant+160*Real.exp 1*Real.pi

lemma lemma121_unweighted_constant_pos : 0<lemma121UnweightedConstant := by
  unfold lemma121UnweightedConstant
  positivity [lemma58_error_constant_pos]

lemma lemma121_strict_unweighted_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {x : ℝ} (hx : 1≤x) (htail : (D:ℝ)/x≤lemma23PaperL D^(-15:ℤ))
    {s : ℂ} (hs : s.re=1) (hsn : ‖s‖≤2) (hshift : ‖s-1‖≤10*lemma44PaperAlpha D) :
    ‖lemma121StrictPolynomial χ x s‖≤lemma121UnweightedConstant*lemma23PaperL D^(-7:ℤ) := by
  let L := lemma23PaperL D
  have hLp : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have he := lemma121_strict_polynomial_error χ hD hx hs hsn
  have hv := lemma58_actual_full_disk_linear_error χ hD hL hA hshift
  have hd : ‖LDerivAtOne χ‖≤16*Real.exp 1*L^2 :=
    lemma32_actual_first_derivative_bound χ hD (by change 2≤lemma23PaperL D; linarith)
      (by simp; positivity)
  have hp : L^(-15:ℤ)≤L^(-7:ℤ) := zpow_le_zpow_right₀ hL1 (by norm_num)
  have hprod : ‖LDerivAtOne χ*(s-1)‖≤(160*Real.exp 1*Real.pi)*L^(-7:ℤ) := by
    rw [norm_mul]
    calc
      _ ≤ (16*Real.exp 1*L^2)*(10*lemma44PaperAlpha D) :=
        mul_le_mul hd hshift (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [lemma58_alpha_eq_log_power]
        change (16*Real.exp 1*L^2)*(10*(Real.pi*L^(-9:ℤ)))=(160*Real.exp 1*Real.pi)*L^(-7:ℤ)
        rw [zpow_neg,zpow_neg,zpow_ofNat,zpow_ofNat]
        field_simp
        norm_num
  have hLv : ‖dirichletLFunction χ s‖≤
      lemma58ErrorConstant*L^(-7:ℤ)+(160*Real.exp 1*Real.pi)*L^(-7:ℤ) := by
    exact (norm_le_norm_sub_add _ (LDerivAtOne χ*(s-1))).trans
      (add_le_add (hv.trans (mul_le_mul_of_nonneg_left hp lemma58_error_constant_pos.le)) hprod)
  apply (norm_le_norm_sub_add _ (dirichletLFunction χ s)).trans
  have hf : ‖lemma121StrictPolynomial χ x s-dirichletLFunction χ s‖≤4*L^(-7:ℤ) := by
    apply he.trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (htail.trans hp) (by norm_num)
  apply (add_le_add hf hLv).trans_eq
  unfold lemma121UnweightedConstant
  ring

end ZhangLS.Spec
