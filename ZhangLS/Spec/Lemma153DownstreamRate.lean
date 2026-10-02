import ZhangLS.Spec.Lemma153DownstreamError
/-! Sharp-enough quantitative scale of the repaired residue. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

noncomputable def lemma153ShiftedValueConstant : ℝ := 1+48*Real.exp 1*Real.pi
noncomputable def lemma153ResidueBracketConstant : ℝ :=
  12288*(Real.exp 1)^2*Real.pi + lemma153ShiftedValueConstant*(384*Real.exp 1+64*lemma153ShiftedValueConstant)
noncomputable def lemma153ResidueRateConstant : ℝ :=
  64*Real.exp 1*lemma153StripConstant*lemma153ResidueBracketConstant

lemma lemma153_shifted_value_constant_pos : 0<lemma153ShiftedValueConstant := by
  unfold lemma153ShiftedValueConstant; positivity
lemma lemma153_residue_bracket_constant_pos : 0<lemma153ResidueBracketConstant := by
  unfold lemma153ResidueBracketConstant
  have := lemma153_shifted_value_constant_pos
  positivity
lemma lemma153_residue_rate_constant_pos : 0<lemma153ResidueRateConstant := by
  unfold lemma153ResidueRateConstant
  have := lemma153_residue_bracket_constant_pos
  have := lemma153_strip_constant_pos
  positivity

lemma lemma153_shifted_value_scale {L b : ℝ} (hL : 1≤L) (hb : b≤3*Real.pi*L^(-9:ℤ)) :
    L^(-2022:ℤ)+(16*Real.exp 1*L^2)*b ≤ lemma153ShiftedValueConstant*L^(-7:ℤ) := by
  have hL0 : 0<L := by linarith
  have hsmall : L^(-2022:ℤ)≤L^(-7:ℤ) := by
    rw [←Real.rpow_intCast,←Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  calc
    _ ≤ L^(-7:ℤ)+(16*Real.exp 1*L^2)*(3*Real.pi*L^(-9:ℤ)) := by gcongr
    _ = _ := by
      unfold lemma153ShiftedValueConstant
      simp only [zpow_neg,zpow_ofNat]
      field_simp
      ring

lemma lemma153_residue_bracket_scale {L b : ℝ} (hL : 1≤L) (hb0 : 0≤b)
    (hb : b≤3*Real.pi*L^(-9:ℤ)) :
    let B := 16*Real.exp 1*L^2
    let E := 128*Real.exp 1*L^3
    let V := L^(-2022:ℤ)+B*b
    let t := L^(11/10:ℝ)
    2*B*E*b+V*(E+16*t*B+64*t^2*V) ≤
      lemma153ResidueBracketConstant*L^(-39/10:ℝ) := by
  dsimp only
  let V := L^(-2022:ℤ)+(16*Real.exp 1*L^2)*b
  let K := lemma153ShiftedValueConstant
  let t := L^(11/10:ℝ)
  have hL0 : 0<L := by linarith
  have hK : 0<K := lemma153_shifted_value_constant_pos
  have ht : 0≤t := Real.rpow_nonneg hL0.le _
  have hV0 : 0≤V := by dsimp [V]; positivity
  have hV : V≤K*L^(-7:ℤ) := lemma153_shifted_value_scale hL hb
  have h4 : L^(-4:ℤ)≤L^(-39/10:ℝ) := by
    rw [←Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have ht5 : t*L^(-5:ℤ)=L^(-39/10:ℝ) := by
    dsimp [t]
    rw [←Real.rpow_intCast,←Real.rpow_add hL0]
    norm_num
  have ht14 : t^2*L^(-14:ℤ)=L^(-59/5:ℝ) := by
    dsimp [t]
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul hL0.le,←Real.rpow_intCast,←Real.rpow_add hL0]
    norm_num
  have h14 : t^2*L^(-14:ℤ)≤L^(-39/10:ℝ) := by
    rw [ht14]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hterm1 : 2*(16*Real.exp 1*L^2)*(128*Real.exp 1*L^3)*b ≤
      (12288*(Real.exp 1)^2*Real.pi)*L^(-39/10:ℝ) := by
    calc
      _ ≤ 2*(16*Real.exp 1*L^2)*(128*Real.exp 1*L^3)*(3*Real.pi*L^(-9:ℤ)) := by gcongr
      _ = (12288*(Real.exp 1)^2*Real.pi)*L^(-4:ℤ) := by
        simp only [zpow_neg,zpow_ofNat]; field_simp; ring
      _ ≤ _ := by gcongr
  have hterm2 : V*(128*Real.exp 1*L^3)≤(128*Real.exp 1*K)*L^(-39/10:ℝ) := by
    calc
      _ ≤ (K*L^(-7:ℤ))*(128*Real.exp 1*L^3) := by gcongr
      _ = (128*Real.exp 1*K)*L^(-4:ℤ) := by
        simp only [zpow_neg,zpow_ofNat]; field_simp
      _ ≤ _ := by gcongr
  have hterm3 : V*(16*t*(16*Real.exp 1*L^2))≤(256*Real.exp 1*K)*L^(-39/10:ℝ) := by
    calc
      _ ≤ (K*L^(-7:ℤ))*(16*t*(16*Real.exp 1*L^2)) := by gcongr
      _ = (256*Real.exp 1*K)*(t*L^(-5:ℤ)) := by
        simp only [zpow_neg,zpow_ofNat]; field_simp; ring
      _ = _ := by rw [ht5]
  have hterm4 : V*(64*t^2*V)≤(64*K^2)*L^(-39/10:ℝ) := by
    calc
      _ ≤ (K*L^(-7:ℤ))*(64*t^2*(K*L^(-7:ℤ))) := by gcongr
      _ = (64*K^2)*(t^2*L^(-14:ℤ)) := by
        simp only [zpow_neg,zpow_ofNat]; field_simp
      _ ≤ _ := by gcongr
  change 2*(16*Real.exp 1*L^2)*(128*Real.exp 1*L^3)*b+V*((128*Real.exp 1*L^3)+16*t*(16*Real.exp 1*L^2)+64*t^2*V) ≤ _
  calc
    _ = 2*(16*Real.exp 1*L^2)*(128*Real.exp 1*L^3)*b +
      V*(128*Real.exp 1*L^3)+V*(16*t*(16*Real.exp 1*L^2))+V*(64*t^2*V) := by ring
    _ ≤ (12288*(Real.exp 1)^2*Real.pi)*L^(-39/10:ℝ)+
      (128*Real.exp 1*K)*L^(-39/10:ℝ)+(256*Real.exp 1*K)*L^(-39/10:ℝ)+
      (64*K^2)*L^(-39/10:ℝ) := add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4
    _ = _ := by unfold lemma153ResidueBracketConstant; dsimp [K]; ring

lemma lemma153_actual_shifted_residue_rate {D : ℕ} (hD : 3≤D)
    (χ : RealPrimitiveCharacter D) (hL : 2≤lemma23PaperL D)
    (hA : NormalizedAssumptionA χ) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (hγ : ‖γ‖≤1/(4*lemma23PaperL D))
    (hγscale : ‖γ‖≤3*lemma44PaperAlpha D) :
    ‖lemma153ActualResidue χ β γ - lemma153EulerProduct χ β γ 1 * LDerivAtOne χ^2‖ ≤
      lemma153ResidueRateConstant*(1+Real.log (lemma23PaperL D))^18*
        lemma23PaperL D^(-39/10:ℝ) := by
  have hγ' : ‖γ‖≤3*Real.pi*lemma23PaperL D^(-9:ℤ) := by
    simpa only [paper_alpha_eq_L9,mul_assoc] using hγscale
  apply (lemma153_actual_shifted_residue_error_bound hD χ hL hA β γ hpar hγ).trans
  have hb := lemma153_residue_bracket_scale (by linarith : 1≤lemma23PaperL D) (norm_nonneg γ) hγ'
  calc
    _ ≤ lemma153LocalPrefactorBound D*(lemma153ResidueBracketConstant*lemma23PaperL D^(-39/10:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (lemma153_local_prefactor_bound_nonneg D)
    _ = _ := by unfold lemma153LocalPrefactorBound lemma153LocalUBound lemma153ResidueRateConstant; ring

end ZhangLS.Spec
