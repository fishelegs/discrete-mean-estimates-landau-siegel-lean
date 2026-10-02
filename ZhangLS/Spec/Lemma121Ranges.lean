import ZhangLS.Spec.Lemma121ExactPhaseEstimate
import ZhangLS.Spec.Lemma82UniformThreshold

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Real

lemma lemma121_log_P1 (D : ℕ) :
    Real.log (lemma121P1 D)=(63/125:ℝ)*lemma23PaperL D^9 := by
  unfold lemma121P1 lemma23PaperP
  rw [Real.log_rpow (Real.exp_pos _),Real.log_exp]

lemma lemma121_endpoint_geometry {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) :
    0<lemma121PDoublePrimeOne D ∧ 0<lemma121PDoublePrimeTwo D ∧
    lemma121PDoublePrimeOne D≤lemma121PDoublePrimeTwo D ∧
    1≤lemma121PDoublePrimeOne D ∧ 1≤Real.log (lemma121P1 D) ∧
    Real.log (lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D)=
      (1/250:ℝ)*lemma23PaperL D^9 ∧
    Real.log (lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D)≤Real.log (lemma121P1 D) := by
  have hDp : (0:ℝ)<D := by exact_mod_cast (by omega : 0<D)
  have hD1 : (1:ℝ)≤D := by exact_mod_cast hD.le
  have hLp : 0<lemma23PaperL D := by linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have ht0 : 0<lemma51PaperT0 D := pow_pos hLp _
  have ht1 : 1≤lemma51PaperT0 D := one_le_pow₀ hL1
  have hP : 1<lemma23PaperP D := by
    unfold lemma23PaperP
    exact Real.one_lt_exp_iff.mpr (pow_pos hLp _)
  have hPp : 0<lemma23PaperP D := zero_lt_one.trans hP
  have ha : 0<lemma121PDoublePrimeOne D := by
    unfold lemma121PDoublePrimeOne
    positivity
  have hb : 0<lemma121PDoublePrimeTwo D := by
    unfold lemma121PDoublePrimeTwo
    positivity
  have hab : lemma121PDoublePrimeOne D≤lemma121PDoublePrimeTwo D := by
    apply mul_le_mul_of_nonneg_right _ ht0.le
    apply mul_le_mul_of_nonneg_right _ hDp.le
    exact Real.rpow_le_rpow_of_exponent_le hP.le (by norm_num)
  have ha1 : 1≤lemma121PDoublePrimeOne D := by
    unfold lemma121PDoublePrimeOne
    have hh : 1≤lemma23PaperP D^(62/125:ℝ) := Real.one_le_rpow hP.le (by norm_num)
    calc
      (1:ℝ) = 1*1*1 := by norm_num
      _ ≤ lemma23PaperP D^(62/125:ℝ)*(D:ℝ)*lemma51PaperT0 D := by gcongr
  have h9 : 2000≤lemma23PaperL D^9 := hL.trans (by
    simpa using pow_le_pow_right₀ hL1 (show 1≤9 by norm_num))
  have hQ : 1≤Real.log (lemma121P1 D) := by rw [lemma121_log_P1]; nlinarith
  have hlogs : Real.log (lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D)=
      (1/250:ℝ)*lemma23PaperL D^9 := by
    rw [Real.log_div hb.ne' ha.ne']
    unfold lemma121PDoublePrimeOne lemma121PDoublePrimeTwo
    rw [Real.log_mul (mul_pos (Real.rpow_pos_of_pos hPp _) hDp).ne' ht0.ne',
      Real.log_mul (Real.rpow_pos_of_pos hPp _).ne' hDp.ne',
      Real.log_mul (mul_pos (Real.rpow_pos_of_pos hPp _) hDp).ne' ht0.ne',
      Real.log_mul (Real.rpow_pos_of_pos hPp _).ne' hDp.ne',
      Real.log_rpow hPp,Real.log_rpow hPp]
    simp only [lemma23PaperP,Real.log_exp]
    ring
  refine ⟨ha,hb,hab,ha1,hQ,hlogs,?_⟩
  rw [hlogs,lemma121_log_P1]
  nlinarith [pow_nonneg hLp.le 9]

lemma lemma121_high_range_geometry {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {d : ℝ} (hdlo : lemma121PDoublePrimeOne D<d) (hdhi : d<lemma121P2 D) :
    lemma56PaperT D<lemma121PDoublePrimeTwo D/d ∧
    1≤lemma121PDoublePrimeTwo D/d ∧ d/lemma121PDoublePrimeOne D<lemma23PaperP D := by
  have hg := lemma121_endpoint_geometry hD hL
  have hdp : 0<d := hg.1.trans hdlo
  have hLp : 0<lemma23PaperL D := by linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hT : 1<lemma56PaperT D := Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hLp _)
  have hTp : 0<lemma56PaperT D := zero_lt_one.trans hT
  have hD1 : (1:ℝ)≤D := by exact_mod_cast hD.le
  have ht1 : 1≤lemma51PaperT0 D := one_le_pow₀ hL1
  have hP : 1<lemma23PaperP D := Real.one_lt_exp_iff.mpr (pow_pos hLp _)
  have hPp : 0<lemma23PaperP D := zero_lt_one.trans hP
  have hB : lemma23PaperP D^(1/2:ℝ)≤lemma121PDoublePrimeTwo D := by
    unfold lemma121PDoublePrimeTwo
    exact (le_mul_of_one_le_right (Real.rpow_nonneg hPp.le _) hD1).trans
      (le_mul_of_one_le_right (by positivity) ht1)
  have hdT : d*lemma56PaperT D^10<lemma23PaperP D^(1/2:ℝ) := by
    have hh : d<lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D^10 := by
      simpa [lemma121P2,zpow_neg,zpow_ofNat,div_eq_mul_inv] using hdhi
    exact (lt_div_iff₀ (pow_pos hTp _)).mp hh
  have hTT : lemma56PaperT D≤lemma56PaperT D^10 := by
    simpa using pow_le_pow_right₀ hT.le (show 1≤10 by norm_num)
  have htail : lemma56PaperT D<lemma121PDoublePrimeTwo D/d := by
    apply (lt_div_iff₀ hdp).mpr
    calc
      lemma56PaperT D*d ≤ lemma56PaperT D^10*d := mul_le_mul_of_nonneg_right hTT hdp.le
      _ < lemma23PaperP D^(1/2:ℝ) := by simpa [mul_comm] using hdT
      _ ≤ _ := hB
  refine ⟨htail,hT.le.trans htail.le,?_⟩
  have hdhalf : d<lemma23PaperP D^(1/2:ℝ) :=
    (le_mul_of_one_le_right hdp.le (one_le_pow₀ hT.le)).trans_lt hdT
  calc
    d/lemma121PDoublePrimeOne D≤d := div_le_self hdp.le hg.2.2.2.1
    _ < lemma23PaperP D^(1/2:ℝ) := hdhalf
    _ < lemma23PaperP D^1 := Real.rpow_lt_rpow_of_exponent_lt hP (by norm_num)
    _ = _ := Real.rpow_one _

/-- The same elementary actual tail absorption as Lemma 8.2, at power 15. -/
lemma lemma121_tail_absorption_eventually :
    ∀ᶠ D : ℕ in atTop, ∀ x : ℝ, lemma56PaperT D<x →
      (D:ℝ)/x≤lemma23PaperL D^(-15:ℤ) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp ht).eventually_ge_atTop 2
  have he := ht.eventually ((Real.isLittleO_pow_exp_atTop (n := 15)).bound (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop (2:ℕ),ht.eventually_ge_atTop 1,hr,he]
    with D hD hL hr he
  intro x hx
  have hDp : (0:ℝ)<D := by exact_mod_cast (by omega : 0<D)
  have hLp : 0<lemma23PaperL D := by linarith
  have heD : Real.exp (lemma23PaperL D)=(D:ℝ) := Real.exp_log hDp
  change 2≤lemma23PaperL D^(1/10:ℝ) at hr
  have hpow : lemma23PaperL D^15≤(D:ℝ) := by
    simpa only [heD,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hLp.le 15),
      abs_of_pos hDp,one_mul] using he
  have hpower : 2*lemma23PaperL D≤lemma23PaperL D^(11/10:ℝ) := by
    rw [show (11/10:ℝ)=1+1/10 by norm_num,Real.rpow_add hLp,Real.rpow_one]
    nlinarith
  have hTsq : (D:ℝ)^2≤lemma56PaperT D := by
    have hh := Real.exp_le_exp.mpr hpower
    rw [two_mul,Real.exp_add,heD] at hh
    simpa only [pow_two,lemma56PaperT] using hh
  have hTp : 0<lemma56PaperT D := Real.exp_pos _
  have hxp : 0<x := hTp.trans hx
  rw [zpow_neg,← one_div]
  norm_num only [zpow_ofNat]
  apply (div_le_div_iff₀ hxp (pow_pos hLp 15)).mpr
  have hm := mul_le_mul_of_nonneg_left hpow hDp.le
  nlinarith

end ZhangLS.Spec
