import ZhangLS.Spec.Lemma162CorrectedAnalytic
import ZhangLS.Spec.Lemma162LocalDataRational
import ZhangLS.Spec.Lemma162FirstRemainderNorm

/-! Exact finite-shift center of the ACTUAL raw product. No zero-shift
substitution is made in the principal identity, including at the prime 2. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Classical
set_option maxHeartbeats 3000000

lemma lemma162_raw_rational_center (a u v b : ℂ) (hv : v=1 ∨ v=-1)
    (hu : 1-u≠0) (hvu : 1-v*u≠0) (hub : 1-u*b≠0) (hvub : 1-v*u*b≠0) :
    lemma162RawPolynomial (lemma162M00 a u v (u*b)) (lemma162M01 a u v (u*b))
      (lemma162M10 u v (u*b)) (lemma162M11 v (u*b)) (lemma162LocalLambda a u v) b v u =
        1-a*b*u^2 := by
  rcases hv with rfl | rfl
  all_goals
    unfold lemma162RawPolynomial lemma162M00 lemma162M01 lemma162M10 lemma162M11
      lemma162LocalLambda lemma162RawP lemma162RawQ lemma162RawS
    simp only [one_mul,neg_mul,mul_neg,sub_neg_eq_add] at *
    field_simp [hu,hvu,hub,hvub]
    ring

/-- Both shifts remain at their genuine finite-D values. -/
lemma lemma162_actual_raw_center {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (q : Nat.Primes) :
    lemma162RawPrimeCorrection χ β γ q 1 =
      if q.val∣D then (1-(q.val:ℂ)⁻¹)^2
      else 1-(q.val:ℂ)^(-β)*(q.val:ℂ)^γ*((q.val:ℂ)⁻¹)^2 := by
  by_cases hd : q.val∣D
  · have hv := χ.evalNat_eq_zero_of_dvd_modulus hd q.property.ne_one
    simp only [lemma162RawPrimeCorrection,if_pos hd,if_pos hv,
      lemma83_prime_monomial_one q.property.pos]
  · have hv := lemma32_character_prime_cases_of_not_dvd χ q.property hd
    have hv0 : χ.evalNat q.val≠0 := by rcases hv with h | h <;> rw [h] <;> norm_num
    rw [lemma162RawPrimeCorrection,if_neg hv0,if_neg hd,lemma83_prime_monomial_one q.property.pos]
    obtain ⟨h00,h01,h10,h11,hlam⟩ := lemma162_actual_local_data_rational χ β hβ γ hγ q
    rw [h00,h01,h10,h11,hlam]
    have hu : ‖(q.val:ℂ)⁻¹‖≤1/2 := by
      rw [norm_inv,Complex.norm_natCast]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
        (show (2:ℝ)≤q.val by exact_mod_cast q.property.two_le)
    have hb : ‖(q.val:ℂ)^γ‖≤1 := by
      simpa using (lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hγ])).le
    obtain ⟨hdu,hdvu,hdub,hdvub⟩ := lemma162_four_denominator_bounds
      ((q.val:ℂ)⁻¹) (χ.evalNat q.val) ((q.val:ℂ)^γ) hu (χ.evalNat_norm_le_one _) hb
    exact lemma162_raw_rational_center _ _ _ _ hv
      (norm_pos_iff.mp (by linarith)) (norm_pos_iff.mp (by linarith))
      (norm_pos_iff.mp (by linarith)) (norm_pos_iff.mp (by linarith))

lemma lemma162_actual_raw_center_zero {D : ℕ} (χ : RealPrimitiveCharacter D) (q : Nat.Primes) :
    lemma162RawPrimeCorrection χ 0 0 q 1 =
      if q.val∣D then (1-(q.val:ℂ)⁻¹)^2 else 1-((q.val:ℂ)⁻¹)^2 := by
  simpa using lemma162_actual_raw_center χ 0 rfl 0 rfl q

lemma lemma162_actual_raw_center_diagonal {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (q : Nat.Primes) :
    lemma162RawPrimeCorrection χ β β q 1 = lemma162RawPrimeCorrection χ 0 0 q 1 := by
  rw [lemma162_actual_raw_center χ β hβ β hβ q,lemma162_actual_raw_center_zero]
  split_ifs
  · rfl
  · have hn : (q.val:ℂ)≠0 := Nat.cast_ne_zero.mpr q.property.ne_zero
    rw [←Complex.cpow_add _ _ hn,neg_add_cancel,Complex.cpow_zero,one_mul]

lemma lemma162_actual_raw_product_center_diagonal {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) :
    lemma162RawEulerProduct χ β β 1 = lemma162RawEulerProduct χ 0 0 1 :=
  tprod_congr (lemma162_actual_raw_center_diagonal χ β hβ)

end ZhangLS.Spec
