import ZhangLS.Spec.AppendixBTailSourceUnsmoothing
import ZhangLS.Spec.AppendixBTailBudgetDecay

/-! The genuine sharp-cutoff error is of order L^-14. The boundary interval
uses the proved constant rho bound; no divisor or logarithmic loss is inserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Filter Topology

noncomputable def appendixBUnsmoothingDecayConstant : ℝ :=
  2*Real.exp (3*Real.pi)*Real.exp 1+
  2*(Real.sqrt Real.pi)⁻¹*Real.exp (3*Real.pi)+lemma44InverseSquareMass+1

lemma appendixB_unsmoothing_decay_constant_pos : 0<appendixBUnsmoothingDecayConstant := by
  have hi : 0≤lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  unfold appendixBUnsmoothingDecayConstant
  positivity

lemma appendixB_unsmoothing_budget_polynomial {D : ℕ} (hL : 3≤lemma23PaperL D) :
    appendixBSingleUnsmoothingBudget D≤
      4*Real.exp (3*Real.pi)/lemma23PaperL D^14+
        appendixBUnsmoothingDecayConstant*lemma23PaperL D^9*
          Real.exp (-(lemma23PaperL D^(1/10 : ℝ))) := by
  let L := lemma23PaperL D
  let M := Real.exp (3*Real.pi)
  let E := Real.exp (-(L^(1/10 : ℝ)))
  let q := (Real.sqrt Real.pi)⁻¹
  have hLp : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have h9 : 1≤L^9 := one_le_pow₀ hL1
  have h14 := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤3) hL 14
  have hd : L/L^15=1/L^14 := by field_simp [hLp.ne']
  have hd0 : 0≤L/L^15 := by positivity
  have hd1' : 2*(L/L^15)≤1 := by
    rw [hd]
    norm_num at h14
    have ht : 2≤L^14 := by dsimp [L]; linarith
    calc
      2*(1/L^14)=2/L^14 := by ring
      _ ≤ 1 := (div_le_iff₀ (pow_pos hLp 14)).mpr (by simpa only [one_mul] using ht)
  have hsmall := Real.abs_exp_sub_one_le (x := 2*(L/L^15)) (by
    rw [abs_of_nonneg (by positivity : 0≤2*(L/L^15))]
    exact hd1')
  have hnear : Real.exp (2*(L/L^15))-1≤4/L^14 := by
    have hh := (le_abs_self (Real.exp (2*(L/L^15))-1)).trans hsmall
    rw [abs_of_nonneg (by positivity : 0≤2*(L/L^15)),hd] at hh
    rw [hd]
    exact hh.trans_eq (by ring)
  have hdelta : Real.exp (L/L^15)≤Real.exp 1 :=
    Real.exp_le_exp.mpr (by linarith)
  have hT : (lemma56PaperT D)⁻¹≤E := by
    unfold lemma56PaperT
    rw [←Real.exp_neg]
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have h2 : Real.exp (-(L^2))≤E := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show (1/10 : ℝ)≤(2 : ℕ) by norm_num)
  have h10 : Real.exp (-(L^10))≤E := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show (1/10 : ℝ)≤(10 : ℕ) by norm_num)
  have hi : 0≤lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hE : 0≤E := (Real.exp_pos _).le
  have hq : 0≤q := by dsimp [q]; positivity
  have hM : 0≤M := (Real.exp_pos _).le
  have hcut : M*(Real.exp (2*(L/L^15))-1+2*Real.exp (L/L^15)/lemma56PaperT D)
      ≤4*M/L^14+(2*M*Real.exp 1)*L^9*E := by
    have hnear' := mul_le_mul_of_nonneg_left hnear hM
    have ht := mul_le_mul hdelta hT (inv_nonneg.mpr (lemma56_paper_T_pos D).le)
      (Real.exp_pos 1).le
    have ht' := mul_le_mul_of_nonneg_left ht (show 0≤2*M by positivity)
    have hp := mul_le_mul_of_nonneg_left h9 (show 0≤2*M*Real.exp 1*E by positivity)
    simp only [div_eq_mul_inv] at hnear' ht' hp ⊢
    nlinarith only [hnear',ht',hp]
  have hfar : (q*Real.exp (-(L^2))/L)*M*(1+L^9)≤(2*q*M)*L^9*E := by
    have hdiv : q*Real.exp (-(L^2))/L≤q*E := by
      calc
        _ ≤ q*Real.exp (-(L^2)) := div_le_self (by positivity) hL1
        _ ≤ q*E := mul_le_mul_of_nonneg_left h2 hq
    have hh := mul_le_mul hdiv (show 1+L^9≤2*L^9 by linarith)
      (by positivity : 0≤1+L^9) (mul_nonneg hq hE)
    have hm := mul_le_mul_of_nonneg_left hh hM
    nlinarith only [hm]
  have htail : lemma44InverseSquareMass*Real.exp (-(L^10))≤
      lemma44InverseSquareMass*L^9*E := by
    have hh := mul_le_mul_of_nonneg_left h9 (mul_nonneg hi hE)
    exact (mul_le_mul_of_nonneg_left h10 hi).trans (by nlinarith only [hh])
  unfold appendixBSingleUnsmoothingBudget appendixBCutoffUnsmoothingBudget
  change _≤4*M/L^14+appendixBUnsmoothingDecayConstant*L^9*E
  dsimp [L,M,q] at hcut hfar htail ⊢
  unfold appendixBUnsmoothingDecayConstant
  nlinarith only [hcut,hfar,htail,mul_nonneg (pow_nonneg hLp.le 9) hE]

/-- Uniform Gaussian unsmoothing with the strict boundary retained. -/
theorem appendixB_unsmoothing_budget_eventual_power :
    ∀ᶠ D : ℕ in atTop, appendixBSingleUnsmoothingBudget D≤
      (4*Real.exp (3*Real.pi)+1)*lemma23PaperL D^(-(14 : ℤ)) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := ht.eventually (lemma84_stretched_exponential_absorption
    appendixBUnsmoothingDecayConstant appendixB_unsmoothing_decay_constant_pos 9 14)
  filter_upwards [ht.eventually_ge_atTop 3,he] with D hL he
  have hh := (appendixB_unsmoothing_budget_polynomial hL).trans (add_le_add le_rfl he)
  exact hh.trans_eq (by
    simp only [zpow_neg,zpow_natCast,zpow_ofNat,div_eq_mul_inv,add_mul,one_mul])

end ZhangLS.Spec
