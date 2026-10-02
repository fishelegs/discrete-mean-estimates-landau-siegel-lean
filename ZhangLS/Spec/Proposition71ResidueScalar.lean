import ZhangLS.Spec.Lemma153ActualShiftRatio
import ZhangLS.Spec.Lemma56
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 4000000

noncomputable def proposition71ResidueGeometric (D : ℕ) (c : ℝ) (j : Fin 3) : ℂ :=
  I * (-lemma83PaperBeta D c j) /
    ((lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j) *
      (lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j))

noncomputable def proposition71ResidueCoefficient (δ : ℝ) (j : Fin 3) : ℝ :=
  if j=0 then -(1-5*δ)/(2*(1+7*δ)*(1+δ)) else
  if j=1 then 2*(1+δ)/((1-5*δ)*(1+7*δ)) else
    -(3*(1-δ))/(2*(1-5*δ)*(1+δ))

noncomputable def proposition71ResidueSignedWeight (j : Fin 3) : ℝ :=
  if j=0 then -(1/2) else if j=1 then 2 else -(3/2)

noncomputable def proposition71ResidueWeight (j : Fin 3) : ℂ :=
  if j=0 then 1/2 else if j=1 then 2 else 3/2

noncomputable def proposition71ResiduePhaseSign (j : Fin 3) : ℂ :=
  if j=1 then 1 else -1

lemma proposition71_residue_real_bounds {δ : ℝ} (hδ : 0≤δ) (hsmall : δ≤1/10)
    (j : Fin 3) :
    |proposition71ResidueCoefficient δ j| ≤ 10 ∧
      |proposition71ResidueCoefficient δ j-proposition71ResidueSignedWeight j| ≤ 100*δ := by
  have h1 : 1/2≤1-5*δ := by linarith
  have h7 : 1≤1+7*δ := by linarith
  have hp : 1≤1+δ := by linarith
  have hA : 2≤2*(1+7*δ)*(1+δ) := by nlinarith
  have hB : 1/2≤(1-5*δ)*(1+7*δ) := by
    exact (by norm_num : (1:ℝ)/2=(1/2)*1).le.trans (mul_le_mul h1 h7 (by norm_num) (by linarith))
  have hC : 1≤2*(1-5*δ)*(1+δ) := by
    nlinarith [mul_le_mul h1 hp (by norm_num : (0:ℝ)≤1) (by linarith : (0:ℝ)≤1-5*δ)]
  have hA0 : 0<2*(1+7*δ)*(1+δ) := by linarith
  have hB0 : 0<(1-5*δ)*(1+7*δ) := by linarith
  have hC0 : 0<2*(1-5*δ)*(1+δ) := by linarith
  have h1ne : 1-5*δ≠0 := by linarith
  have hδ2 : δ^2≤δ/10 := by nlinarith
  fin_cases j
  · change |-(1-5*δ)/(2*(1+7*δ)*(1+δ))|≤10 ∧
      |-(1-5*δ)/(2*(1+7*δ)*(1+δ))-(-(1/2))|≤100*δ
    constructor
    · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hA0.le)]
      rw [neg_div,neg_neg]
      exact (div_le_iff₀ hA0).mpr (by nlinarith)
    · have he : -(1-5*δ)/(2*(1+7*δ)*(1+δ))-(-(1/2)) =
          (13*δ+7*δ^2)/(2*(1+7*δ)*(1+δ)) := by field_simp [h1ne, show 1-δ*5≠0 by nlinarith]; ring
      rw [he,abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ hA0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hA hδ]
  · change |2*(1+δ)/((1-5*δ)*(1+7*δ))|≤10 ∧
      |2*(1+δ)/((1-5*δ)*(1+7*δ))-2|≤100*δ
    constructor
    · rw [abs_of_nonneg (by positivity)]
      exact (div_le_iff₀ hB0).mpr (by nlinarith)
    · have he : 2*(1+δ)/((1-5*δ)*(1+7*δ))-2 =
          (-2*δ+70*δ^2)/((1-5*δ)*(1+7*δ)) := by field_simp [h1ne, show 1-δ*5≠0 by nlinarith]; ring
      rw [he,abs_div,abs_of_pos hB0]
      apply (div_le_iff₀ hB0).mpr
      rw [abs_le]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left hB hδ]
  · change |-(3*(1-δ))/(2*(1-5*δ)*(1+δ))|≤10 ∧
      |-(3*(1-δ))/(2*(1-5*δ)*(1+δ))-(-(3/2))|≤100*δ
    constructor
    · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by nlinarith) hC0.le),neg_div,neg_neg]
      exact (div_le_iff₀ hC0).mpr (by nlinarith)
    · have he : -(3*(1-δ))/(2*(1-5*δ)*(1+δ))-(-(3/2)) =
          -(9*δ+15*δ^2)/(2*(1-5*δ)*(1+δ)) := by field_simp [h1ne, show 1-δ*5≠0 by nlinarith]; ring
      rw [he,abs_div,abs_neg,abs_of_nonneg (by positivity),abs_of_pos hC0]
      apply (div_le_iff₀ hC0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hC hδ]

lemma proposition71_residue_geometric_formula {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    proposition71ResidueGeometric D c j =
      (proposition71ResidueCoefficient (c*lemma44PaperAlpha D*lemma23PaperL D) j : ℂ) /
        (lemma44PaperAlpha D : ℂ) := by
  let δ := c*lemma44PaperAlpha D*lemma23PaperL D
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1/10 := hsmall
  have h1 : (1:ℂ)-5*(δ:ℂ)≠0 := by
    have : 0<1-5*δ := by linarith
    exact_mod_cast this.ne'
  have hp : (1:ℂ)+(δ:ℂ)≠0 := by
    have : 0<1+δ := by linarith
    exact_mod_cast this.ne'
  have h7 : (1:ℂ)+7*(δ:ℂ)≠0 := by
    have : 0<1+7*δ := by linarith
    exact_mod_cast this.ne'
  have ha' : (lemma44PaperAlpha D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hf := lemma153_actual_beta_factorization D c
  have hg1 := lemma153_beta_gap_one D c
  have hg2 := lemma153_beta_gap_two D c
  have hg : lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c =
      I*(lemma44PaperAlpha D:ℂ)*(1+7*(δ:ℂ)) := by
    rw [hf.1,hf.2.1]; dsimp [δ]; ring
  fin_cases j
  · change I * (-lemma52PaperBetaOne D c) /
      ((lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c)*
        (lemma52PaperBetaThree D c-lemma52PaperBetaOne D c)) =
      ((-(1-5*δ)/(2*(1+7*δ)*(1+δ)) : ℝ) : ℂ)/(lemma44PaperAlpha D:ℂ)
    rw [hg,hg1,hf.1,hf.2.1]
    change I * (-(I*(lemma44PaperAlpha D:ℂ)*(1-5*(δ:ℂ)))) /
      ((I*(lemma44PaperAlpha D:ℂ)*(1+7*(δ:ℂ))) *
        (I*(lemma44PaperAlpha D:ℂ)*(2*(1+(δ:ℂ))))) = _
    push_cast
    field_simp
  · change I * (-lemma52PaperBetaTwo D c) /
      ((lemma52PaperBetaThree D c-lemma52PaperBetaTwo D c)*
        (lemma52PaperBetaOne D c-lemma52PaperBetaTwo D c)) =
      ((2*(1+δ)/((1-5*δ)*(1+7*δ)) : ℝ) : ℂ)/(lemma44PaperAlpha D:ℂ)
    rw [hg2,show lemma52PaperBetaOne D c-lemma52PaperBetaTwo D c =
      -(lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c) by ring,hg,hf.1,hf.2.1]
    change I * (-(I*(lemma44PaperAlpha D:ℂ)*(2*(1+(δ:ℂ)))))/
      ((I*(lemma44PaperAlpha D:ℂ)*(1-5*(δ:ℂ)))*
        (-(I*(lemma44PaperAlpha D:ℂ)*(1+7*(δ:ℂ))))) = _
    push_cast
    field_simp
  · change I * (-lemma52PaperBetaThree D c) /
      ((lemma52PaperBetaOne D c-lemma52PaperBetaThree D c)*
        (lemma52PaperBetaTwo D c-lemma52PaperBetaThree D c)) =
      ((-(3*(1-δ))/(2*(1-5*δ)*(1+δ)) : ℝ) : ℂ)/(lemma44PaperAlpha D:ℂ)
    rw [show lemma52PaperBetaOne D c-lemma52PaperBetaThree D c =
      -(lemma52PaperBetaThree D c-lemma52PaperBetaOne D c) by ring,
      show lemma52PaperBetaTwo D c-lemma52PaperBetaThree D c =
      -(lemma52PaperBetaThree D c-lemma52PaperBetaTwo D c) by ring,hg1,hg2,hf.1,hf.2.1,hf.2.2]
    change I * (-(I*(lemma44PaperAlpha D:ℂ)*(3*(1-(δ:ℂ)))))/
      ((-(I*(lemma44PaperAlpha D:ℂ)*(2*(1+(δ:ℂ)))))*
        (-(I*(lemma44PaperAlpha D:ℂ)*(1-5*(δ:ℂ))))) = _
    push_cast
    field_simp

lemma proposition71_residue_geometric_norm {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖proposition71ResidueGeometric D c j‖ ≤ 10/lemma44PaperAlpha D := by
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hδ : 0≤c*lemma44PaperAlpha D*lemma23PaperL D := by positivity
  rw [proposition71_residue_geometric_formula hL hc hsmall,norm_div,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos ha]
  exact div_le_div_of_nonneg_right (proposition71_residue_real_bounds hδ hsmall j).1 ha.le

lemma proposition71_residue_geometric_error {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖proposition71ResidueGeometric D c j -
      (proposition71ResidueSignedWeight j:ℂ)/(lemma44PaperAlpha D:ℂ)‖ ≤
      100*c*lemma23PaperL D := by
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hδ : 0≤c*lemma44PaperAlpha D*lemma23PaperL D := by positivity
  rw [proposition71_residue_geometric_formula hL hc hsmall,←sub_div,←Complex.ofReal_sub,
    norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos ha]
  calc
    _ ≤ (100*(c*lemma44PaperAlpha D*lemma23PaperL D))/lemma44PaperAlpha D :=
      div_le_div_of_nonneg_right (proposition71_residue_real_bounds hδ hsmall j).2 ha.le
    _ = _ := by field_simp

noncomputable def proposition71ResiduePhaseConstant (c : ℝ) : ℝ := 3+5*Real.pi*c

lemma proposition71_residue_prime_log_error {D p : ℕ}
    (hpwin : p ∈ lemma56PaperPrimes D) :
    0 ≤ Real.log (p : ℝ)-Real.log (lemma23PaperP D) ∧
      Real.log (p : ℝ)-Real.log (lemma23PaperP D) ≤ lemma23PaperL D^(-68 : ℤ) := by
  have hpwin := (lemma56_mem_paper_primes D p).mp hpwin
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hp : 0 < (p : ℝ) := hP.trans hpwin.2.1
  have hlo := Real.log_le_log hP hpwin.2.1.le
  have hratio : (p : ℝ)/lemma23PaperP D ≤ 1+lemma23PaperL D^(-68 : ℤ) :=
    (div_le_iff₀ hP).mpr (by simpa [lemma56PrimeUpper,mul_comm] using hpwin.2.2.le)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp hP)
  rw [Real.log_div hp.ne' hP.ne'] at hlog
  exact ⟨by linarith,by linarith⟩

lemma proposition71_residue_prime_offset_errors {D p : ℕ}
    (hpwin : p∈lemma56PaperPrimes D) {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) :
    |lemma23PaperOffsetOne D c*Real.log (p:ℝ)-Real.pi| ≤
      proposition71ResiduePhaseConstant c*lemma44PaperAlpha D*lemma23PaperL D ∧
    |lemma23PaperOffsetTwo D c*Real.log (p:ℝ)-2*Real.pi| ≤
      proposition71ResiduePhaseConstant c*lemma44PaperAlpha D*lemma23PaperL D ∧
    |lemma23PaperOffsetThree D c*Real.log (p:ℝ)-3*Real.pi| ≤
      proposition71ResiduePhaseConstant c*lemma44PaperAlpha D*lemma23PaperL D := by
  let α := lemma44PaperAlpha D
  let L := lemma23PaperL D
  let δ := c*α*L
  let θ := Real.log (p:ℝ)-Real.log (lemma23PaperP D)
  have hα : 0<α := (lemma44_alpha_pos_le_one hL).1
  have hL0 : 0<L := by dsimp [L]; linarith
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have hlogP := lemma153_alpha_logP hL0
  have hoff := lemma52_offset_bounds hL hc hsmall
  have hθraw := proposition71_residue_prime_log_error hpwin
  have hθ : |θ|≤L := by
    rw [abs_of_nonneg hθraw.1]
    exact hθraw.2.trans ((zpow_le_one_of_nonpos₀ (by linarith : 1≤lemma23PaperL D)
      (by norm_num : (-68:ℤ)≤0)).trans (by dsimp [L]; linarith))
  have hcommon (b : ℝ) (hb : 0≤b) (hb' : b≤3*α) : |b*θ|≤3*α*L := by
    rw [abs_mul,abs_of_nonneg hb]
    exact mul_le_mul hb' hθ (abs_nonneg _) (by positivity)
  have he1 : lemma23PaperOffsetOne D c*Real.log (p:ℝ)-Real.pi =
      -5*Real.pi*δ+lemma23PaperOffsetOne D c*θ := by
    dsimp [δ,θ,lemma23PaperOffsetOne]
    dsimp [α,L] at *
    linear_combination -5*c*lemma44PaperAlpha D*lemma23PaperL D*hlogP + hlogP
  have he2 : lemma23PaperOffsetTwo D c*Real.log (p:ℝ)-2*Real.pi =
      2*Real.pi*δ+lemma23PaperOffsetTwo D c*θ := by
    dsimp [δ,θ,lemma23PaperOffsetTwo]
    dsimp [α,L] at *
    linear_combination 2*c*lemma44PaperAlpha D*lemma23PaperL D*hlogP + 2*hlogP
  have he3 : lemma23PaperOffsetThree D c*Real.log (p:ℝ)-3*Real.pi =
      -3*Real.pi*δ+lemma23PaperOffsetThree D c*θ := by
    dsimp [δ,θ,lemma23PaperOffsetThree]
    dsimp [α,L] at *
    linear_combination -3*c*lemma44PaperAlpha D*lemma23PaperL D*hlogP + 3*hlogP
  have hfinish (x b k : ℝ) (hk : |k|≤5) (hb : |b*θ|≤3*α*L)
      (he : x=k*Real.pi*δ+b*θ) : |x|≤proposition71ResiduePhaseConstant c*α*L := by
    rw [he]
    calc
      _ ≤ |k*Real.pi*δ|+|b*θ| := abs_add_le _ _
      _ ≤ 5*Real.pi*δ+3*α*L := by
        apply add_le_add _ hb
        rw [abs_mul,abs_mul,abs_of_pos Real.pi_pos,abs_of_nonneg hδ]
        gcongr
      _ = _ := by dsimp [δ,proposition71ResiduePhaseConstant]; ring
  exact ⟨hfinish _ _ (-5) (by norm_num) (hcommon _ hoff.1.1 hoff.1.2) he1,
    hfinish _ _ 2 (by norm_num) (hcommon _ hoff.2.1.1 hoff.2.1.2) he2,
    hfinish _ _ (-3) (by norm_num) (hcommon _ hoff.2.2.1 hoff.2.2.2) he3⟩

lemma proposition71_residue_prime_phase_norm {D p : ℕ}
    (hpwin : p∈lemma56PaperPrimes D) (c : ℝ) (j : Fin 3) :
    ‖(p:ℂ)^(-lemma83PaperBeta D c j)‖=1 := by
  have hp : 0<(p:ℝ) := (Real.exp_pos _).trans
    ((lemma56_mem_paper_primes D p).mp hpwin).2.1
  rw [show (p:ℂ)=((p:ℝ):ℂ) by norm_cast,Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp [lemma83_beta_re]

lemma proposition71_residue_prime_phase {D p : ℕ}
    (hpwin : p∈lemma56PaperPrimes D) {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖(p:ℂ)^(-lemma83PaperBeta D c j)-proposition71ResiduePhaseSign j‖ ≤
      proposition71ResiduePhaseConstant c*lemma44PaperAlpha D*lemma23PaperL D := by
  have hp : 0<(p:ℝ) := (Real.exp_pos _).trans
    ((lemma56_mem_paper_primes D p).mp hpwin).2.1
  have hpow (b : ℝ) : (p:ℂ)^(-(I*(b:ℂ))) =
      Complex.exp (I*((-(b*Real.log (p:ℝ)):ℝ):ℂ)) := by
    have hp' : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
    rw [Complex.cpow_def_of_ne_zero hp']
    rw [show (p:ℂ)=((p:ℝ):ℂ) by norm_cast,←Complex.ofReal_log hp.le]
    congr 1
    push_cast
    ring
  have he1 : Complex.exp (I*((-Real.pi:ℝ):ℂ)) = -1 := by
    rw [ofReal_neg,mul_neg,Complex.exp_neg]
    simpa [mul_comm] using congrArg Inv.inv Complex.exp_pi_mul_I
  have he2 : Complex.exp (I*((-(2*Real.pi):ℝ):ℂ)) = 1 := by
    rw [ofReal_neg,mul_neg,Complex.exp_neg]
    have hh : Complex.exp (I*((2*Real.pi:ℝ):ℂ))=1 := by
      convert Complex.exp_two_pi_mul_I using 1 <;> push_cast <;> ring
    rw [hh]; norm_num
  have he3 : Complex.exp (I*((-(3*Real.pi):ℝ):ℂ)) = -1 := by
    have hh : I*((-(3*Real.pi):ℝ):ℂ)=
        I*((-Real.pi:ℝ):ℂ)+I*((-(2*Real.pi):ℝ):ℂ) := by push_cast; ring
    rw [hh,Complex.exp_add,he1,he2,mul_one]
  have hneg (x y : ℝ) : |-x - -y|=|x-y| := by
    rw [show -x - -y=-(x-y) by ring,abs_neg]
  have herr := proposition71_residue_prime_offset_errors hpwin hL hc hsmall
  fin_cases j
  · change ‖(p:ℂ)^(-lemma52PaperBetaOne D c)-(-1)‖≤_
    rw [lemma52PaperBetaOne,hpow,←he1]
    exact (lemma153_exp_imaginary_difference _ _).trans (by rw [hneg]; exact herr.1)
  · change ‖(p:ℂ)^(-lemma52PaperBetaTwo D c)-1‖≤_
    rw [lemma52PaperBetaTwo,hpow,←he2]
    exact (lemma153_exp_imaginary_difference _ _).trans (by rw [hneg]; exact herr.2.1)
  · change ‖(p:ℂ)^(-lemma52PaperBetaThree D c)-(-1)‖≤_
    rw [lemma52PaperBetaThree,hpow,←he3]
    exact (lemma153_exp_imaginary_difference _ _).trans (by rw [hneg]; exact herr.2.2)

lemma proposition71_residue_phase_sign_norm (j : Fin 3) :
    ‖proposition71ResiduePhaseSign j‖=1 := by
  unfold proposition71ResiduePhaseSign
  split_ifs <;> simp

lemma proposition71_residue_signed_weight_identity (j : Fin 3) :
    (proposition71ResidueSignedWeight j:ℂ)*proposition71ResiduePhaseSign j =
      proposition71ResidueWeight j := by
  fin_cases j <;> norm_num [proposition71ResidueSignedWeight,
    proposition71ResiduePhaseSign,proposition71ResidueWeight]

noncomputable def proposition71ResidueScalarConstant (c : ℝ) : ℝ :=
  100*c+10*proposition71ResiduePhaseConstant c

lemma proposition71_residue_scalar_constant_pos {c : ℝ} (hc : 0<c) :
    0<proposition71ResidueScalarConstant c := by
  unfold proposition71ResidueScalarConstant proposition71ResiduePhaseConstant
  positivity

/-- The genuine original prime-dependent scalar, with c fixed and explicit uniform error. -/
theorem proposition71_residue_scalar_normalization {D p : ℕ}
    (hpwin : p∈lemma56PaperPrimes D) {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖proposition71ResidueGeometric D c j*(p:ℂ)^(-lemma83PaperBeta D c j)-
      proposition71ResidueWeight j/(lemma44PaperAlpha D:ℂ)‖ ≤
      proposition71ResidueScalarConstant c*lemma23PaperL D := by
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hg := proposition71_residue_geometric_norm hL hc hsmall j
  have he := proposition71_residue_geometric_error hL hc hsmall j
  have hp := proposition71_residue_prime_phase hpwin hL hc hsmall j
  have hC : 0≤proposition71ResiduePhaseConstant c := by
    unfold proposition71ResiduePhaseConstant; positivity
  rw [←proposition71_residue_signed_weight_identity j]
  rw [show proposition71ResidueGeometric D c j*(p:ℂ)^(-lemma83PaperBeta D c j)-
      (proposition71ResidueSignedWeight j:ℂ)*proposition71ResiduePhaseSign j/(lemma44PaperAlpha D:ℂ) =
      proposition71ResidueGeometric D c j*((p:ℂ)^(-lemma83PaperBeta D c j)-proposition71ResiduePhaseSign j)+
      (proposition71ResidueGeometric D c j-(proposition71ResidueSignedWeight j:ℂ)/(lemma44PaperAlpha D:ℂ))*
        proposition71ResiduePhaseSign j by ring]
  calc
    _ ≤ ‖proposition71ResidueGeometric D c j*((p:ℂ)^(-lemma83PaperBeta D c j)-proposition71ResiduePhaseSign j)‖+
      ‖(proposition71ResidueGeometric D c j-(proposition71ResidueSignedWeight j:ℂ)/(lemma44PaperAlpha D:ℂ))*
        proposition71ResiduePhaseSign j‖ := norm_add_le _ _
    _ ≤ (10/lemma44PaperAlpha D)*
        (proposition71ResiduePhaseConstant c*lemma44PaperAlpha D*lemma23PaperL D)+
        100*c*lemma23PaperL D := by
      rw [norm_mul,norm_mul,proposition71_residue_phase_sign_norm,mul_one]
      exact add_le_add (mul_le_mul hg hp (norm_nonneg _) (by positivity)) he
    _ = _ := by unfold proposition71ResidueScalarConstant; field_simp; ring

/-- Uniform in every actual paper prime and all three poles, after choosing c. -/
theorem proposition71_eventual_residue_scalar_normalization {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D →
      (∀ j : Fin 3, ‖proposition71ResidueGeometric D c j‖≤10/lemma44PaperAlpha D) ∧
      ∀ p∈lemma56PaperPrimes D, ∀ j : Fin 3,
        ‖proposition71ResidueGeometric D c j*(p:ℂ)^(-lemma83PaperBeta D c j)-
          proposition71ResidueWeight j/(lemma44PaperAlpha D:ℂ)‖ ≤
          proposition71ResidueScalarConstant c*lemma23PaperL D := by
  obtain ⟨D₀,hD₀,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨D₀,?_⟩
  intro D hD
  have hL : 3≤lemma23PaperL D := by
    have := (lemma44_parameters_at_explicit_threshold (hD₀.trans hD)).1
    linarith
  exact ⟨fun j => proposition71_residue_geometric_norm hL hc (hsmall D hD) j,
    fun p hp j => proposition71_residue_scalar_normalization hp hL hc (hsmall D hD) j⟩

end ZhangLS.Spec
