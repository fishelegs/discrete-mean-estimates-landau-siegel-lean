import ZhangLS.Spec.Lemma121UniformPolynomial

/-! A concrete L^-7 estimate for the original transition range. The source
symbol α1 is undefined, so this theorem does not assign it a meaning. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Real

lemma lemma121_transition_geometry {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {d : ℝ} (hdlo : lemma121PDoublePrimeOne D/lemma56PaperT D<d)
    (hdhi : d≤lemma121PDoublePrimeOne D) :
    0<d ∧ 1≤lemma121PDoublePrimeOne D/d ∧
    lemma121PDoublePrimeOne D/d<lemma23PaperP D ∧
    lemma56PaperT D<lemma121PDoublePrimeTwo D/d ∧
    1≤lemma121PDoublePrimeTwo D/d ∧ lemma121PDoublePrimeTwo D/d<lemma23PaperP D := by
  let L := lemma23PaperL D
  have hg := lemma121_endpoint_geometry hD hL
  have hLp : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have hTp : 0<lemma56PaperT D := Real.exp_pos _
  have hT : 1<lemma56PaperT D := Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hLp _)
  have hPp : 0<lemma23PaperP D := Real.exp_pos _
  have hdp : 0<d := (div_pos hg.1 hTp).trans hdlo
  have hxA : 0<lemma121PDoublePrimeOne D/d := div_pos hg.1 hdp
  have hxB : 0<lemma121PDoublePrimeTwo D/d := div_pos hg.2.1 hdp
  have hx1 : 1≤lemma121PDoublePrimeOne D/d := (one_le_div hdp).mpr hdhi
  have hratio : 0<lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D := div_pos hg.2.1 hg.1
  have hxy : lemma121PDoublePrimeOne D/d≤lemma121PDoublePrimeTwo D/d :=
    div_le_div_of_nonneg_right hg.2.2.1 hdp.le
  have hTexp : L^(11/10:ℝ)≤L^2 := by
    rw [← Real.rpow_natCast L 2]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h7 : 250<L^7 := by
    have hh : L≤L^7 := by simpa using pow_le_pow_right₀ hL1 (show 1≤7 by norm_num)
    dsimp [L] at *
    linarith
  have h250 : 250*L^2<L^9 := by
    have hh := mul_lt_mul_of_pos_right h7 (pow_pos hLp 2)
    nlinarith only [hh]
  have hTratio : lemma56PaperT D<lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D := by
    apply (Real.log_lt_log_iff hTp hratio).mp
    rw [hg.2.2.2.2.2.1,lemma56PaperT,Real.log_exp]
    change L^(11/10:ℝ)<(1/250:ℝ)*L^9
    linarith only [hTexp,h250]
  have hrB : lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D≤lemma121PDoublePrimeTwo D/d :=
    div_le_div_of_nonneg_left hg.2.1.le hdp hdhi
  have hxT : lemma121PDoublePrimeOne D/d<lemma56PaperT D := by
    apply (div_lt_iff₀ hdp).mpr
    have hh := (div_lt_iff₀ hTp).mp hdlo
    simpa only [mul_comm] using hh
  have hlogA : Real.log (lemma121PDoublePrimeOne D/d)<L^2 := by
    have hh := Real.log_lt_log hxA hxT
    rw [lemma56PaperT,Real.log_exp] at hh
    exact hh.trans_le hTexp
  have hlogB : Real.log (lemma121PDoublePrimeTwo D/d)=
      (1/250:ℝ)*L^9+Real.log (lemma121PDoublePrimeOne D/d) := by
    rw [← hg.2.2.2.2.2.1,Real.log_div hg.2.1.ne' hdp.ne',
      Real.log_div hg.2.1.ne' hg.1.ne',Real.log_div hg.1.ne' hdp.ne']
    ring
  have hxP : lemma121PDoublePrimeTwo D/d<lemma23PaperP D := by
    apply (Real.log_lt_log_iff hxB hPp).mp
    rw [hlogB,lemma23PaperP,Real.log_exp]
    change (1/250:ℝ)*L^9+Real.log (lemma121PDoublePrimeOne D/d)<L^9
    have hp : 0<L^9 := pow_pos hLp 9
    linarith only [hlogA,h250,hp]
  exact ⟨hdp,hx1,hxy.trans_lt hxP,hTratio.trans_le hrB,hx1.trans hxy,hxP⟩

noncomputable def lemma121TransitionConstant : ℝ :=
  lemma121UnweightedConstant+4*lemma121WeightedConstant

lemma lemma121_transition_constant_pos : 0<lemma121TransitionConstant := by
  unfold lemma121TransitionConstant
  positivity [lemma121_unweighted_constant_pos,lemma121_weighted_constant_pos]

lemma lemma121_transition_estimate {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (htail : ∀ x : ℝ, lemma56PaperT D<x → (D:ℝ)/x≤lemma23PaperL D^(-15:ℤ))
    (j : Fin 3) {d : ℝ} (hdlo : lemma121PDoublePrimeOne D/lemma56PaperT D<d)
    (hdhi : d≤lemma121PDoublePrimeOne D) :
    ‖lemma121Sum χ c j d‖≤lemma121TransitionConstant*lemma23PaperL D^(-7:ℤ) := by
  let A := lemma121PDoublePrimeOne D
  let B := lemma121PDoublePrimeTwo D
  let Q := Real.log (lemma121P1 D)
  let L := lemma23PaperL D
  let a := lemma82PaperBeta D c j
  let b := lemma82SmoothingBeta D 6
  let s := 1+b-a
  have hg := lemma121_endpoint_geometry hD hL
  have hr := lemma121_transition_geometry hD hL hdlo hdhi
  have hLp : 0<L := by dsimp [L]; linarith
  have hQ : 0<Q := zero_lt_one.trans_le hg.2.2.2.2.1
  have hs : s.re=1 := by simp [s,a,b,lemma82_beta_re,lemma82_smoothing_beta_re]
  have hshift := lemma82_shift_in_disk hL hc hsmall j 6
  have hF := lemma121_strict_unweighted_uniform χ hD hL hA hr.2.2.2.2.1 (htail _ hr.2.2.2.1)
    hs hshift.2 hshift.1
  have hWB := lemma121_weighted_uniform χ hD hL hA hr.2.2.2.2.1 hr.2.2.2.2.2 hs hshift.2 hshift.1
  have hWA := lemma121_weighted_uniform χ hD hL hA hr.2.1 hr.2.2.1 hs hshift.2 hshift.1
  have hlog0 : 0≤Real.log (B/A) := Real.log_nonneg ((one_le_div hg.1).mpr hg.2.2.1)
  have hF' : ‖(Real.log (B/A):ℂ)*lemma121StrictPolynomial χ (B/d) s‖≤
      Real.log (B/A)*(lemma121UnweightedConstant*L^(-7:ℤ)) := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog0] using
      mul_le_mul_of_nonneg_left hF hlog0
  have hsum := (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add hF' hWB)) hWA)
  change ‖∑ n ∈ lemma82StrictCutoff (B/d), χ.evalNat n*lemma121Kernel A B Q b (d*(n:ℝ))/(n:ℂ)^(1-a)‖≤_
  rw [lemma121_kernel_sum_all_ranges χ hg.1 hg.2.1 hg.2.2.1 hr.1 a b,norm_mul,norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hr.1 hg.1),Complex.neg_re,
    lemma82_smoothing_beta_re,neg_zero,Real.rpow_zero,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤1/Q)).trans
  have hcoef : Real.log (B/A)/Q≤1 := (div_le_one hQ).mpr hg.2.2.2.2.2.2
  have hterm : (2*lemma121WeightedConstant*L^2)/Q≤4*lemma121WeightedConstant*L^(-7:ℤ) := by
    have hqe : Q=(63/125:ℝ)*L^9 := lemma121_log_P1 D
    rw [hqe]
    have heq : (2*lemma121WeightedConstant*L^2)/((63/125:ℝ)*L^9)=
        (250/63:ℝ)*lemma121WeightedConstant*L^(-7:ℤ) := by
      rw [zpow_neg,zpow_ofNat]
      field_simp
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (250/63:ℝ)≤4)
        lemma121_weighted_constant_pos.le) (by positivity)
  calc
    _ = (Real.log (B/A)/Q)*(lemma121UnweightedConstant*L^(-7:ℤ))+
        (2*lemma121WeightedConstant*L^2)/Q := by ring
    _ ≤ 1*(lemma121UnweightedConstant*L^(-7:ℤ))+4*lemma121WeightedConstant*L^(-7:ℤ) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (by positivity [lemma121_unweighted_constant_pos])) hterm
    _ = _ := by unfold lemma121TransitionConstant; ring

/-- A concrete transition bound with absolute constant chosen before c′.
This is deliberately not phrased as a definition of the paper's α1. -/
def Lemma121TransitionTarget : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ d : ℕ,
      lemma121PDoublePrimeOne D/lemma56PaperT D<(d:ℝ) → (d:ℝ)≤lemma121PDoublePrimeOne D →
      ‖lemma121Sum χ c j d‖≤C*lemma23PaperL D^(-7:ℤ)

theorem lemma121_transition_proved : Lemma121TransitionTarget := by
  refine ⟨lemma121TransitionConstant,lemma121_transition_constant_pos,?_⟩
  intro c hc
  obtain ⟨N,hN,hh⟩ := lemma82_uniform_threshold c hc
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp lemma121_tail_absorption_eventually
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hDN χ hA j d hdlo hdhi
  have hn := hh D ((le_max_left N M).trans hDN)
  have hm := hM D ((le_max_right N M).trans hDN)
  exact lemma121_transition_estimate χ (by omega) hn.2.1 hA hc hn.2.2.1 hm j hdlo hdhi

end ZhangLS.Spec
