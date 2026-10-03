import ZhangLS.Spec.Lemma162ExactCenter
import ZhangLS.Spec.Lemma152MonomialVariation
import ZhangLS.Spec.Lemma153DownstreamNormalization

/-! Summable finite-shift center error for actual V's raw numerator.
The exact identity proves the two q⁻¹ gains without dividing by F00,2. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_raw_center_prime_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (hbsmall : ‖β‖≤1/10)
    (γ : ℂ) (hγ : γ.re=0) (hgsmall : ‖γ‖≤1/10) (q : Nat.Primes) :
    ‖lemma162RawPrimeCorrection χ β γ q 1-lemma162RawPrimeCorrection χ 0 0 q 1‖≤
      10*(‖β‖+‖γ‖)*(q.val:ℝ)^(-(9/5:ℝ)) := by
  rw [lemma162_actual_raw_center χ β hβ γ hγ q,lemma162_actual_raw_center_zero]
  split_ifs
  · simp only [sub_self,norm_zero]
    positivity
  · let a : ℂ := (q.val:ℂ)^(-β)
    let b : ℂ := (q.val:ℂ)^γ
    have hb : ‖b‖=1 := by simpa [b] using lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hγ])
    have haD : ‖a-1‖≤10*‖β‖*(q.val:ℝ)^(1/5:ℝ) := by
      simpa [a,lemma32_prime_monomial_eq_cpow q.property.pos] using lemma152_shift_monomial_variation q.property.pos β hbsmall
    have hbD : ‖b-1‖≤10*‖γ‖*(q.val:ℝ)^(1/5:ℝ) := by
      simpa [b,lemma32_prime_monomial_eq_cpow q.property.pos] using lemma152_shift_monomial_variation q.property.pos (-γ) (by simpa using hgsmall)
    have hab : ‖a*b-1‖≤10*(‖β‖+‖γ‖)*(q.val:ℝ)^(1/5:ℝ) := by
      rw [show a*b-1 = (a-1)*b+(b-1) by ring]
      apply (norm_add_le _ _).trans
      rw [norm_mul,hb,mul_one]
      linarith
    change ‖(1-a*b*((q.val:ℂ)⁻¹)^2)-(1-((q.val:ℂ)⁻¹)^2)‖≤_
    rw [show (1-a*b*((q.val:ℂ)⁻¹)^2)-(1-((q.val:ℂ)⁻¹)^2) =
      -(a*b-1)*((q.val:ℂ)⁻¹)^2 by ring,norm_mul,norm_neg,norm_pow,norm_inv,Complex.norm_natCast]
    calc
      _ ≤ (10*(‖β‖+‖γ‖)*(q.val:ℝ)^(1/5:ℝ))*((q.val:ℝ)⁻¹)^2 :=
        mul_le_mul_of_nonneg_right hab (sq_nonneg _)
      _ = _ := by
        rw [pow_two,←Real.rpow_neg_one]
        calc
          _ = (10*(‖β‖+‖γ‖))*((q.val:ℝ)^(1/5:ℝ)*(q.val:ℝ)^(-1:ℝ)*(q.val:ℝ)^(-1:ℝ)) := by ring
          _ = _ := by rw [←Real.rpow_add (Nat.cast_pos.mpr q.property.pos),←Real.rpow_add (Nat.cast_pos.mpr q.property.pos)]; norm_num

lemma lemma162_raw_center_prime_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (q : Nat.Primes) :
    ‖lemma162RawPrimeCorrection χ β γ q 1‖≤1+(q.val:ℝ)^(-2:ℝ) := by
  rw [lemma162_actual_raw_center χ β hβ γ hγ q]
  split_ifs
  · have hn := lemma153_ramified_center_norm_le_one q
    exact hn.trans (by have := Real.rpow_nonneg (Nat.cast_nonneg q.val) (-2:ℝ); linarith)
  · have ha := lemma83_cpow_shift_norm q.property.pos β hβ
    have hb : ‖(q.val:ℂ)^γ‖=1 := by simpa using lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hγ])
    apply (norm_sub_le _ _).trans
    rw [norm_one,norm_mul,norm_mul,norm_pow,ha,hb,one_mul,norm_inv,Complex.norm_natCast]
    rw [show (-2:ℝ)=(-1)+(-1) by norm_num,Real.rpow_add (Nat.cast_pos.mpr q.property.pos),Real.rpow_neg_one,pow_two]
    simp

noncomputable def lemma162CenterProductBound : ℝ := Real.exp (∑' q : Nat.Primes, (q.val:ℝ)^(-2:ℝ))
noncomputable def lemma162CenterVariationConstant : ℝ :=
  10*lemma162CenterProductBound*(1+∑' q : Nat.Primes, (q.val:ℝ)^(-(9/5:ℝ)))

lemma lemma162_center_product_bound_pos : 0< lemma162CenterProductBound := Real.exp_pos _
lemma lemma162_center_variation_constant_pos : 0<lemma162CenterVariationConstant := by
  unfold lemma162CenterVariationConstant
  have ht : 0≤∑' q : Nat.Primes, (q.val:ℝ)^(-(9/5:ℝ)) := tsum_nonneg (fun _ => by positivity)
  have hB := lemma162_center_product_bound_pos
  positivity

lemma lemma162_center_square_summable : Summable (fun q : Nat.Primes => (q.val:ℝ)^(-2:ℝ)) :=
  (Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ)< -1)).subtype Nat.Prime
lemma lemma162_center_variation_summable : Summable (fun q : Nat.Primes => (q.val:ℝ)^(-(9/5:ℝ))) :=
  (Real.summable_nat_rpow.mpr (by norm_num : -(9/5:ℝ)< -1)).subtype Nat.Prime

lemma lemma162_finite_center_majorant_bound (S : Finset Nat.Primes) :
    (∏ q ∈ S, (1+(q.val:ℝ)^(-2:ℝ)))≤lemma162CenterProductBound := by
  apply (Real.prod_one_add_le_exp_sum S (fun _ => by positivity)).trans
  exact Real.exp_le_exp.mpr (lemma162_center_square_summable.sum_le_tsum S (fun _ _ => by positivity))

lemma lemma162_raw_center_product_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (hbsmall : ‖β‖≤1/10)
    (γ : ℂ) (hγ : γ.re=0) (hgsmall : ‖γ‖≤1/10) :
    ‖lemma162RawEulerProduct χ β γ 1-lemma162RawEulerProduct χ 0 0 1‖≤
      lemma162CenterVariationConstant*(‖β‖+‖γ‖) := by
  have ht := (lemma162_raw_euler_multipliable χ β hβ γ hγ 1 (by norm_num)).hasProd
  have hz := (lemma162_raw_euler_multipliable χ 0 rfl 0 rfl 1 (by norm_num)).hasProd
  apply le_of_tendsto (ht.sub hz).norm
  filter_upwards with S
  let E := ‖β‖+‖γ‖
  have hE : 0≤E := by dsimp [E]; positivity
  have hb := lemma83_product_perturbation S
    (fun q => lemma162RawPrimeCorrection χ β γ q 1)
    (fun q => lemma162RawPrimeCorrection χ 0 0 q 1)
    (fun q => 1+(q.val:ℝ)^(-2:ℝ))
    (fun q => 10*E*(q.val:ℝ)^(-(9/5:ℝ)))
    (fun q _ => by have := Real.rpow_nonneg (Nat.cast_nonneg q.val) (-2:ℝ); linarith)
    (fun q _ => lemma162_raw_center_prime_norm χ β hβ γ hγ q)
    (fun q _ => lemma162_raw_center_prime_norm χ 0 rfl 0 rfl q)
    (fun q _ => lemma162_raw_center_prime_comparison χ β hβ hbsmall γ hγ hgsmall q)
  apply hb.trans
  have hsum : (∑ q ∈ S, 10*E*(q.val:ℝ)^(-(9/5:ℝ)))≤
      (10*E)*(1+∑' q : Nat.Primes, (q.val:ℝ)^(-(9/5:ℝ))) := by
    rw [←mul_sum]
    gcongr
    exact (lemma162_center_variation_summable.sum_le_tsum S (fun _ _ => by positivity)).trans (by linarith)
  calc
    _ ≤ lemma162CenterProductBound*((10*E)*(1+∑' q : Nat.Primes, (q.val:ℝ)^(-(9/5:ℝ)))) :=
      mul_le_mul (lemma162_finite_center_majorant_bound S) hsum (sum_nonneg (fun _ _ => by positivity))
        lemma162_center_product_bound_pos.le
    _ = _ := by unfold lemma162CenterVariationConstant; dsimp [E]; ring

/-- Exact ramified normalization of the zero-shift numerator, proved from
its actual prime factors. This is a comparison value, not a substitute V. -/
lemma lemma162_raw_center_zero_exact {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma162RawEulerProduct χ 0 0 1 =
      ((Nat.totient D:ℂ)/(D:ℂ))*lemma171AnalyticCorrection D 1 := by
  have hh := (lemma153_ramified_totient_hasProd χ.modulus_ne_zero).mul
    (lemma171_local_corrections_hasProd χ 1 (by norm_num))
  have hp : HasProd (fun q : Nat.Primes => lemma162RawPrimeCorrection χ 0 0 q 1)
      (((Nat.totient D:ℂ)/(D:ℂ))*lemma171AnalyticCorrection D 1) := by
    apply hh.congr_fun
    intro q
    rw [lemma162_actual_raw_center_zero,lemma171_local_correction χ q.property _
      (lemma32_prime_monomial_norm_lt_one q.property.one_lt 1 (by norm_num)),
      lemma83_prime_monomial_one q.property.pos]
    split_ifs <;> ring
  exact (lemma162_raw_euler_multipliable χ 0 rfl 0 rfl 1 (by norm_num)).hasProd.unique hp

lemma lemma162_raw_center_zero_norm_le_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ‖lemma162RawEulerProduct χ 0 0 1‖≤1 := by
  apply le_of_tendsto (lemma162_raw_euler_multipliable χ 0 rfl 0 rfl 1 (by norm_num)).hasProd.norm
  filter_upwards with S
  apply prod_le_one (fun _ _ => norm_nonneg _)
  intro q hq
  rw [lemma162_actual_raw_center_zero]
  split_ifs
  · exact lemma153_ramified_center_norm_le_one q
  · have hu : 0≤(q.val:ℝ)⁻¹ ∧ (q.val:ℝ)⁻¹≤1 := ⟨by positivity,inv_le_one_of_one_le₀ (by exact_mod_cast q.property.one_lt.le)⟩
    have he : (1:ℂ)-((q.val:ℂ)⁻¹)^2 = ((1-((q.val:ℝ)⁻¹)^2:ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonneg (by nlinarith [sq_nonneg ((q.val:ℝ)⁻¹)])]
    nlinarith [sq_nonneg ((q.val:ℝ)⁻¹)]

end ZhangLS.Spec
