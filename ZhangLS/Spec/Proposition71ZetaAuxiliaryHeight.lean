import ZhangLS.Spec.Lemma81ZetaPerronBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # An unconditional auxiliary-height zeta strip for Section7

The integer M is an auxiliary height parameter, not a character modulus.
The zero-free input has no character or Assumption (A). Its actual width and
all logarithmic-derivative constants remain explicit.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Set
open scoped Topology
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

noncomputable def proposition71ZetaAuxHeight (D : ℕ) : ℝ :=
  Real.exp ((Real.log (D : ℝ))^(1/10 : ℝ))

noncomputable def proposition71ZetaAuxInteger (D : ℕ) : ℕ :=
  ⌈4*proposition71ZetaAuxHeight D⌉₊+2

lemma proposition71_zeta_aux_height_pos (D : ℕ) : 0<proposition71ZetaAuxHeight D := Real.exp_pos _

lemma proposition71_zeta_aux_integer_bounds (D : ℕ) :
    4*proposition71ZetaAuxHeight D≤(proposition71ZetaAuxInteger D : ℝ) ∧
      (proposition71ZetaAuxInteger D : ℝ)≤4*proposition71ZetaAuxHeight D+3 := by
  have hlo := Nat.le_ceil (4*proposition71ZetaAuxHeight D)
  have hhi := Nat.ceil_lt_add_one (show 0≤4*proposition71ZetaAuxHeight D from mul_nonneg (by norm_num) (proposition71_zeta_aux_height_pos D).le)
  simp only [proposition71ZetaAuxInteger,Nat.cast_add,Nat.cast_ofNat]
  constructor <;> linarith

lemma proposition71_zeta_aux_log_bounds {D : ℕ}
    (hL : 0≤Real.log (D : ℝ)) (hroot : Real.log 7≤(Real.log (D : ℝ))^(1/10 : ℝ)) :
    (Real.log (D : ℝ))^(1/10 : ℝ)≤Real.log (proposition71ZetaAuxInteger D : ℝ) ∧
      Real.log (proposition71ZetaAuxInteger D : ℝ)≤2*(Real.log (D : ℝ))^(1/10 : ℝ) := by
  have hH := proposition71_zeta_aux_height_pos D
  have hH1 : 1≤proposition71ZetaAuxHeight D := Real.one_le_exp (Real.rpow_nonneg hL _)
  have hb := proposition71_zeta_aux_integer_bounds D
  have hMp : 0<(proposition71ZetaAuxInteger D : ℝ) := by linarith
  have hlo : proposition71ZetaAuxHeight D≤(proposition71ZetaAuxInteger D : ℝ) := by linarith
  have hhi : (proposition71ZetaAuxInteger D : ℝ)≤7*proposition71ZetaAuxHeight D := by linarith
  constructor
  · have hh := Real.log_le_log hH hlo
    simpa only [proposition71ZetaAuxHeight,Real.log_exp] using hh
  · calc
      _≤Real.log (7*proposition71ZetaAuxHeight D) := Real.log_le_log hMp hhi
      _=Real.log 7+(Real.log (D : ℝ))^(1/10 : ℝ) := by
        rw [Real.log_mul (by norm_num : (7 : ℝ)≠0) hH.ne',proposition71ZetaAuxHeight,Real.log_exp]
      _≤_ := by linarith

lemma proposition71_zeta_aux_root_tendsto :
    Tendsto (fun D : ℕ => (Real.log (D : ℝ))^(1/10 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/10)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma proposition71_zeta_aux_height_tendsto :
    Tendsto proposition71ZetaAuxHeight atTop atTop :=
  Real.tendsto_exp_atTop.comp proposition71_zeta_aux_root_tendsto

/-- All inclusions needed by the auxiliary Perron estimate, including its
actual zero-free radius and a bounded horizontal logarithmic transport cost. -/
theorem proposition71_zeta_auxiliary_geometry (M₀ : ℕ) :
    ∀ᶠ D : ℕ in atTop,
      1<D ∧ 3≤Real.log (D : ℝ) ∧
      M₀≤proposition71ZetaAuxInteger D ∧ 4≤proposition71ZetaAuxInteger D ∧
      2000≤Real.log (proposition71ZetaAuxInteger D : ℝ) ∧
      1/Real.log (D : ℝ)≤lemma81ZetaContourDelta (proposition71ZetaAuxInteger D) ∧
      proposition71ZetaAuxHeight D≤(proposition71ZetaAuxInteger D : ℝ)/2 ∧
      (2/Real.log (D : ℝ))*(360000000*Real.log (proposition71ZetaAuxInteger D : ℝ)^2+
        21600*Real.log (proposition71ZetaAuxInteger D : ℝ))≤1 := by
  have hlog : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h09 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<9/10)).comp hlog).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/40000000))
  have h08 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<4/5)).comp hlog).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2880172800))
  filter_upwards [eventually_ge_atTop 2,hlog.eventually (eventually_ge_atTop 3),
    proposition71_zeta_aux_root_tendsto.eventually (eventually_ge_atTop (max 2000 (Real.log 7))),
    proposition71_zeta_aux_height_tendsto.eventually (eventually_ge_atTop (M₀ : ℝ)),h09,h08]
    with D hD hL hroot hH h09 h08
  have hLp : 0<Real.log (D : ℝ) := by linarith
  have hlogb := proposition71_zeta_aux_log_bounds hLp.le ((le_max_right _ _).trans hroot)
  have hb := proposition71_zeta_aux_integer_bounds D
  have hHp := proposition71_zeta_aux_height_pos D
  have hH1 : 1≤proposition71ZetaAuxHeight D := Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hM0 : M₀≤proposition71ZetaAuxInteger D := by
    have hh : (M₀ : ℝ)≤(proposition71ZetaAuxInteger D : ℝ) := by linarith only [hH,hb.1,hHp]
    exact_mod_cast hh
  have hM4 : 4≤proposition71ZetaAuxInteger D := by
    have hh : (4 : ℝ)≤(proposition71ZetaAuxInteger D : ℝ) := by linarith only [hH1,hb.1]
    exact_mod_cast hh
  have hML : 2000≤Real.log (proposition71ZetaAuxInteger D : ℝ) :=
    ((le_max_left _ _).trans hroot).trans hlogb.1
  have hMLp : 0<Real.log (proposition71ZetaAuxInteger D : ℝ) := by linarith
  have he09 : (Real.log (D : ℝ))^(-(9/10 : ℝ))=
      (Real.log (D : ℝ))^(1/10 : ℝ)/Real.log (D : ℝ) := by
    rw [show -(9/10 : ℝ)=(1/10 : ℝ)-1 by norm_num,Real.rpow_sub hLp,Real.rpow_one]
  have he08 : (Real.log (D : ℝ))^(-(4/5 : ℝ))=
      ((Real.log (D : ℝ))^(1/10 : ℝ))^2/Real.log (D : ℝ) := by
    rw [show -(4/5 : ℝ)=((1/10 : ℝ)*2)-1 by norm_num,Real.rpow_sub hLp,
      Real.rpow_one,Real.rpow_mul hLp.le,Real.rpow_two]
  dsimp only [Function.comp_apply] at h09 h08
  rw [he09] at h09
  rw [he08] at h08
  have hwidth : 1/Real.log (D : ℝ)≤lemma81ZetaContourDelta (proposition71ZetaAuxInteger D) := by
    unfold lemma81ZetaContourDelta
    apply (div_le_div_iff₀ hLp (by positivity : 0<20000000*Real.log (proposition71ZetaAuxInteger D : ℝ))).mpr
    have hh := (div_lt_iff₀ hLp).mp h09
    nlinarith only [hh,hlogb.2]
  have hB : 360000000*Real.log (proposition71ZetaAuxInteger D : ℝ)^2+
      21600*Real.log (proposition71ZetaAuxInteger D : ℝ)≤
        1440086400*((Real.log (D : ℝ))^(1/10 : ℝ))^2 := by
    have hsq : Real.log (proposition71ZetaAuxInteger D : ℝ)^2≤
        (2*(Real.log (D : ℝ))^(1/10 : ℝ))^2 :=
      pow_le_pow_left₀ hMLp.le hlogb.2 2
    nlinarith only [hsq,hML]
  have hcost : (2/Real.log (D : ℝ))*(360000000*Real.log (proposition71ZetaAuxInteger D : ℝ)^2+
      21600*Real.log (proposition71ZetaAuxInteger D : ℝ))≤1 := by
    have hh := (div_lt_iff₀ hLp).mp h08
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLp).mpr
    nlinarith only [hh,hB]
  exact ⟨by omega,hL,hM0,hM4,hML,hwidth,by linarith only [hb.1,hHp],hcost⟩

end ZhangLS.Spec
