import ZhangLS.Spec.Lemma151ActualPointwiseAssembly

/-! Quantitative decay of the proved pointwise error. No alpha1 is defined. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex Filter
open scoped Classical Topology

noncomputable def actual151Rate (D : ℕ) : ℝ := lemma23PaperL D^(-79/10 : ℝ)
noncomputable def actual151FullErrorConstant (c : ℝ) : ℝ :=
  4*(1+275*Real.exp (5*Real.pi))+(5*Real.pi+40)*c+(412+960/Real.pi+132*Real.pi)
noncomputable def actual151FirstErrorConstant (c : ℝ) : ℝ :=
  (1+‖lemma151Iota2‖)*(actual151FullErrorConstant c+appendixBRoughRemovalConstant)+
    appendixBTerminalTailErrorConstant c
noncomputable def actual151SecondErrorConstant (c : ℝ) : ℝ :=
  (‖lemma151Iota3‖+‖lemma151Iota4‖)*(actual151FullErrorConstant c+appendixBRoughRemovalConstant)
noncomputable def actual151PointwiseConstant (c : ℝ) : ℝ :=
  25920*bCoefficientConstant+roughCollisionNormalizedConstant*Real.pi+
    actual151FirstErrorConstant c*actual151SecondErrorConstant c+
    actual151SecondConstantBound*actual151FirstErrorConstant c+
    actual151FirstConstantBound*actual151SecondErrorConstant c

lemma actual151_rate_nonneg (D : ℕ) : 0≤actual151Rate D := Real.rpow_nonneg (Real.log_natCast_nonneg D) _
lemma actual151_rate_le_one {D : ℕ} (hL : 1≤lemma23PaperL D) : actual151Rate D≤1 := by
  unfold actual151Rate
  simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL
    (by norm_num : (-79/10 : ℝ)≤0)
lemma actual151_zpow_le_rate {D : ℕ} (hL : 1≤lemma23PaperL D) {k : ℤ} (hk : k≤ -8) :
    lemma23PaperL D^k≤actual151Rate D := by
  rw [←Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le hL
  have : (k : ℝ)≤ -8 := by exact_mod_cast hk
  linarith

lemma actual151_collision_le_rate {D : ℕ} (hD : 0<D) (hL : 1≤lemma23PaperL D) :
    roughCollisionUniformBudget D≤roughCollisionNormalizedConstant*Real.pi*actual151Rate D := by
  have ha : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity
  have hC : 0≤roughCollisionNormalizedConstant := by
    unfold roughCollisionNormalizedConstant
    positivity [b_coefficient_constant_nonneg,Real.pi_pos]
  have hDr : (1 : ℝ)≤D := by exact_mod_cast hD
  have hbound : roughCollisionUniformBudget D/lemma44PaperAlpha D≤
      roughCollisionNormalizedConstant :=
    (roughCollision_normalized_budget hD hL).trans
      (div_le_self hC (one_le_pow₀ hDr))
  have hb := (div_le_iff₀ ha).mp hbound
  have he : lemma44PaperAlpha D=Real.pi*lemma23PaperL D^(-9 : ℤ) := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv]
  rw [he,←mul_assoc] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (actual151_zpow_le_rate hL (by norm_num : (-9 : ℤ)≤ -8)) (mul_nonneg hC Real.pi_pos.le))

lemma actual151_factor_error_rates {c : ℝ} (hc : 0<c) :
    ∀ᶠ D : ℕ in atTop,
      0≤actual151FirstError D c ∧
      actual151FirstError D c≤actual151FirstErrorConstant c*actual151Rate D ∧
      0≤actual151SecondError D c ∧
      actual151SecondError D c≤actual151SecondErrorConstant c*actual151Rate D := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [appendixB_original_error_eventual_bound hc,ht.eventually_ge_atTop 1]
    with D hE hL
  have hR := appendixB_rough_removal_constant_pos.le
  have hT : 0≤appendixBTerminalTailErrorConstant c := by
    unfold appendixBTerminalTailErrorConstant
    positivity [Real.pi_pos]
  have hpow : 0≤lemma23PaperL D^(-8 : ℤ) := zpow_nonneg (zero_le_one.trans hL) _
  have hpowle := actual151_zpow_le_rate hL (le_refl (-8 : ℤ))
  have hK0 : 0≤actual151KernelError D c :=
    add_nonneg hE.1 (mul_nonneg hR hpow)
  have hE' : appendixBOriginalError D c≤actual151FullErrorConstant c*actual151Rate D := hE.2
  have hK : actual151KernelError D c≤
      (actual151FullErrorConstant c+appendixBRoughRemovalConstant)*actual151Rate D := by
    exact (add_le_add hE' (mul_le_mul_of_nonneg_left hpowle hR)).trans_eq (by ring)
  refine ⟨add_nonneg (mul_nonneg (by positivity) hK0) (mul_nonneg hT hpow),?_,
    mul_nonneg (by positivity) hK0,?_⟩
  · exact (add_le_add (mul_le_mul_of_nonneg_left hK (by positivity))
      (mul_le_mul_of_nonneg_left hpowle hT)).trans_eq (by
        unfold actual151FirstErrorConstant; ring)
  · exact (mul_le_mul_of_nonneg_left hK (by positivity)).trans_eq (by
      unfold actual151SecondErrorConstant; ring)

/-- An explicit c-dependent constant gives the original logT/logP rate. -/
theorem actual151_pointwise_error_rate {c : ℝ} (hc : 0<c) :
    ∀ᶠ D : ℕ in atTop,0≤actual151PointwiseError D c ∧
      actual151PointwiseError D c≤actual151PointwiseConstant c*actual151Rate D := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [actual151_factor_error_rates hc,ht.eventually_ge_atTop 1,
    eventually_gt_atTop 0] with D hF hL hD
  have hF1 : 0≤actual151FirstErrorConstant c := by
    unfold actual151FirstErrorConstant actual151FullErrorConstant appendixBTerminalTailErrorConstant
    positivity [Real.pi_pos,appendixB_rough_removal_constant_pos]
  have hF2 : 0≤actual151SecondErrorConstant c := by
    unfold actual151SecondErrorConstant actual151FullErrorConstant
    positivity [Real.pi_pos,appendixB_rough_removal_constant_pos]
  have hC1 : 0≤actual151FirstConstantBound := by
    unfold actual151FirstConstantBound
    exact sum_nonneg (fun (i : Fin 3) _ => norm_nonneg (actual151FirstConstant (i.val+1)))
  have hC2 : 0≤actual151SecondConstantBound := by
    unfold actual151SecondConstantBound
    exact sum_nonneg (fun (i : Fin 3) _ => norm_nonneg (actual151SecondConstant (i.val+1)))
  have hp := actual151_rate_nonneg D
  have hp1 := actual151_rate_le_one hL
  have hNu : actual151NuError D≤25920*bCoefficientConstant*actual151Rate D :=
    mul_le_mul_of_nonneg_left (actual151_zpow_le_rate hL (by norm_num : (-951 : ℤ)≤ -8))
      (by positivity [b_coefficient_constant_nonneg])
  have hColl := actual151_collision_le_rate hD hL
  have hProd : actual151FirstError D c*actual151SecondError D c≤
      (actual151FirstErrorConstant c*actual151SecondErrorConstant c)*actual151Rate D := by
    calc
      _ ≤ (actual151FirstErrorConstant c*actual151Rate D)*
          (actual151SecondErrorConstant c*actual151Rate D) :=
        mul_le_mul hF.2.1 hF.2.2.2 hF.2.2.1 (mul_nonneg hF1 hp)
      _ = (actual151FirstErrorConstant c*actual151SecondErrorConstant c)*
          (actual151Rate D*actual151Rate D) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hp hp1) (mul_nonneg hF1 hF2)
  have hPC : actual151ProductError D c≤
      (actual151FirstErrorConstant c*actual151SecondErrorConstant c+
        actual151SecondConstantBound*actual151FirstErrorConstant c+
        actual151FirstConstantBound*actual151SecondErrorConstant c)*actual151Rate D := by
    exact (add_le_add (add_le_add hProd (mul_le_mul_of_nonneg_left hF.2.1 hC2))
      (mul_le_mul_of_nonneg_left hF.2.2.2 hC1)).trans_eq (by ring)
  constructor
  · unfold actual151PointwiseError actual151NuError actual151ProductError roughCollisionUniformBudget
    positivity [b_coefficient_constant_nonneg,hF.1,hF.2.2.1]
  · exact (add_le_add (add_le_add hNu hColl) hPC).trans_eq (by
      unfold actual151PointwiseConstant; ring)

/-- The proved arithmetic error tends to zero, uniformly before chi,j,n1. -/
theorem actual151_pointwise_error_tendsto_zero {c : ℝ} (hc : 0<c) :
    Tendsto (fun D : ℕ => actual151PointwiseError D c) atTop (𝓝 0) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<79/10)).comp ht
  have hz := hp.const_mul (actual151PointwiseConstant c)
  apply squeeze_zero' ((actual151_pointwise_error_rate hc).mono (fun _ h => h.1))
    ((actual151_pointwise_error_rate hc).mono (fun _ h => h.2))
  simpa only [actual151Rate,neg_div,mul_zero] using hz

/-- The rate is also exposed directly on the genuine arithmetic sum, with
one threshold before every original arithmetic parameter. -/
theorem actual151_repaired_power_uniform {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ,2≤D₀ ∧ ∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,∀ n₁ : ℕ,
      Lemma151Supported (lemma151Q D) n₁ → (n₁ : ℝ)<lemma56PaperT D →
      ‖lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁-
        χ.evalNat n₁*(lemma34Tau 2 n₁ : ℂ)*actual151MainConstant (j.val+1)‖≤
        ‖χ.evalNat n₁‖*(actual151PointwiseConstant c*actual151Rate D)*
          (lemma34Tau 2 n₁ : ℝ) := by
  obtain ⟨N,hN,h⟩ := actual151_repaired_quantitative_character hc
  obtain ⟨M,hM⟩ := eventually_atTop.mp (actual151_pointwise_error_rate hc)
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD χ hA j n₁ hn₁ hnT
  exact (h D ((le_max_left _ _).trans hD) χ hA j n₁ hn₁ hnT).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hM D ((le_max_right _ _).trans hD)).2 (norm_nonneg _))
      (Nat.cast_nonneg _))

/-- Pure rate bookkeeping: an actual O(L^4.4) weighted arithmetic budget
would leave L^-3.5. This does not assume or prove that separate arithmetic budget. -/
theorem actual151_outer_four_log_scale {D : ℕ} (hL : 0<lemma23PaperL D) :
    actual151Rate D*lemma23PaperL D^(22/5 : ℝ)=lemma23PaperL D^(-7/2 : ℝ) := by
  unfold actual151Rate
  rw [←Real.rpow_add hL]
  norm_num

end ZhangLS.Spec
