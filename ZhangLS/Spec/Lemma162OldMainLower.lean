import ZhangLS.Spec.Lemma162CorrectedCenter
import ZhangLS.Spec.Lemma84WeightedArithmetic

/-! Quantitative lower bound for the literal main term printed in Lemma 16.2.
The denominator is the actual two-branch main term from Lemma 16.1. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_old_main_restricted_upper {D : ℕ} (χ : RealPrimitiveCharacter D)
    (P : Nat.Primes → Prop) :
    ‖lemma161RestrictedProduct χ 0 P 1‖ ≤ lemma152ProductBound := by
  apply le_of_tendsto (lemma161_restricted_multipliable χ 0 rfl P 1 (by norm_num)).hasProd.norm
  filter_upwards with S
  apply (prod_le_prod (fun _ _ => norm_nonneg _)
    (fun q _ => lemma161_restricted_norm_le χ 0 rfl P q 1 (by norm_num))).trans
  exact lemma152_finite_majorant_product_le S

/-- Covers the exceptional q=2 branch by its literal factor 2. -/
lemma lemma162_old_main_denominator_upper {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ‖lemma161MainTerm χ‖ ≤ 2*lemma152ProductBound := by
  rw [← lemma161_zero_center_equals_main]
  unfold lemma161Star
  split_ifs
  · rw [norm_mul]
    norm_num only [Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (lemma162_old_main_restricted_upper χ _) (by norm_num)
  · have hh : ‖lemma161EulerProduct χ 0 1‖ ≤ lemma152ProductBound := by
      simpa [lemma161RestrictedProduct,lemma161RestrictedFactor,lemma161EulerProduct] using
        lemma162_old_main_restricted_upper χ (fun _ => True)
    linarith [lemma152_product_bound_pos]

lemma lemma162_old_ramified_product_lower {D : ℕ} (hD : 0<D) :
    (Nat.totient D:ℝ)/(D:ℝ) ≤ ∏ q ∈ D.primeFactors, (q:ℝ)/((q:ℝ)+1) := by
  have hd : (D:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  rw [lemma84_totient_real_product]
  have he : (D:ℝ)*(∏ q ∈ D.primeFactors, (1-(q:ℝ)⁻¹))/(D:ℝ) =
      ∏ q ∈ D.primeFactors, (1-(q:ℝ)⁻¹) := by field_simp [hd]
  rw [he]
  apply Finset.prod_le_prod
  · intro q hq
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le
    have hi : (q:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
    linarith
  · intro q hq
    have hq0 : (0:ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
    apply (le_div_iff₀ (by positivity : 0<(q:ℝ)+1)).mpr
    have hi : (q:ℝ)*(q:ℝ)⁻¹=1 := mul_inv_cancel₀ hq0.ne'
    nlinarith [inv_nonneg.mpr hq0.le]

lemma lemma162_old_totient_lower {D : ℕ} (hD : 0<D)
    (hL : 1<lemma23PaperL D) :
    (Real.exp (2/Real.log 2)*(1+Real.log (lemma23PaperL D))^6)⁻¹ ≤
      (Nat.totient D:ℝ)/(D:ℝ) := by
  have hd : (0:ℝ)<D := Nat.cast_pos.mpr hD
  have hphi : (0:ℝ)<Nat.totient D := Nat.cast_pos.mpr (Nat.totient_pos.mpr hD)
  have hh := lemma84_reciprocal_totient_uniform hD hL (le_refl (Real.log (D:ℝ)))
  have hi : ((Nat.totient D:ℝ)/(D:ℝ))⁻¹ ≤
      Real.exp (2/Real.log 2)*(1+Real.log (lemma23PaperL D))^6 := by
    rw [inv_div]
    calc
      _ = (D:ℝ)*(Nat.totient D:ℝ)⁻¹ := by ring
      _ ≤ (D:ℝ)*((D:ℝ)⁻¹*(Real.exp (2/Real.log 2)*(1+Real.log (lemma23PaperL D))^6)) :=
        mul_le_mul_of_nonneg_left hh hd.le
      _ = _ := by rw [←mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
  simpa only [one_div,inv_inv] using
    one_div_le_one_div_of_le (inv_pos.mpr (div_pos hphi hd)) hi

/-- An exact positive absolute constant; no numerical approximation is used. -/
noncomputable def lemma162OldMainLowerConstant : ℝ :=
  6/(Real.pi^2*(2*lemma152ProductBound)*(Real.exp (2/Real.log 2))^2)

lemma lemma162_old_main_lower_constant_pos : 0<lemma162OldMainLowerConstant := by
  unfold lemma162OldMainLowerConstant
  have hB := lemma152_product_bound_pos
  have hpi := Real.pi_pos
  positivity

lemma lemma162_old_main_norm_eq {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ‖lemma162CorrectedCenterMain χ‖ =
      (6/Real.pi^2)*((Nat.totient D:ℝ)/((D:ℝ)*‖lemma161MainTerm χ‖))*
        ∏ q ∈ D.primeFactors, (q:ℝ)/((q:ℝ)+1) := by
  unfold lemma162CorrectedCenterMain
  rw [norm_mul,norm_mul,norm_div,norm_pow,norm_div,norm_mul,norm_prod]
  simp only [Complex.norm_ofNat,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  congr 2
  funext q
  rw [norm_div,Complex.norm_natCast]
  have he : (q:ℂ)+1 = (((q:ℝ)+1:ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(q:ℝ)+1)]

/-- The actual printed Euler main term dominates a fixed log-log power,
uniformly in D and in the actual primitive real character. -/
theorem lemma162_old_main_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 1<lemma23PaperL D) :
    lemma162OldMainLowerConstant/(1+Real.log (lemma23PaperL D))^12 ≤
      ‖lemma162CorrectedCenterMain χ‖ := by
  let E := Real.exp (2/Real.log 2)
  let H := 1+Real.log (lemma23PaperL D)
  let T := (Nat.totient D:ℝ)/(D:ℝ)
  have hd : (0:ℝ)<D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.modulus_ne_zero)
  have hp : 0<‖lemma161MainTerm χ‖ := norm_pos_iff.mpr (lemma161_main_ne_zero χ)
  have hB := lemma152_product_bound_pos
  have hE : 0<E := Real.exp_pos _
  have hH : 0<H := by dsimp [H]; linarith [Real.log_pos hL]
  have hT : 0≤T := by dsimp [T]; positivity
  have ht := lemma162_old_totient_lower (Nat.pos_of_ne_zero χ.modulus_ne_zero) hL
  have hr := lemma162_old_ramified_product_lower (Nat.pos_of_ne_zero χ.modulus_ne_zero)
  have hden := lemma162_old_main_denominator_upper χ
  have hprod : (E*H^6)⁻¹*(E*H^6)⁻¹ ≤
      T*(∏ q ∈ D.primeFactors, (q:ℝ)/((q:ℝ)+1)) :=
    mul_le_mul ht (ht.trans hr) (by positivity) hT
  rw [lemma162_old_main_norm_eq]
  calc
    _ = ((6/Real.pi^2)*((E*H^6)⁻¹*(E*H^6)⁻¹))/(2*lemma152ProductBound) := by
      change (6/(Real.pi^2*(2*lemma152ProductBound)*E^2))/H^12 = _
      field_simp [hH.ne',hE.ne',hB.ne',Real.pi_ne_zero]
    _ ≤ ((6/Real.pi^2)*(T*(∏ q ∈ D.primeFactors, (q:ℝ)/((q:ℝ)+1))))/
        ‖lemma161MainTerm χ‖ :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hprod (by positivity)) hp hden
    _ = _ := by dsimp [T]; ring

end ZhangLS.Spec
