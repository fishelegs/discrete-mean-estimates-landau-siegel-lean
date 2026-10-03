import ZhangLS.Spec.Lemma162ActualRawExtraction

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

lemma lemma162_center_prime_monomial {p : ℕ} (hp : 0<p) (γ : ℂ) :
    lemma32PrimeMonomial p (1-γ) = (p:ℂ)⁻¹*(p:ℂ)^γ := by
  rw [lemma32_prime_monomial_eq_cpow hp]
  have hn : (p:ℂ)≠0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [show -(1-γ) = (-1:ℂ)+γ by ring,Complex.cpow_add _ _ hn,Complex.cpow_neg_one]

lemma lemma162_actual_local_data_rational {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (q : Nat.Primes) :
    let a : ℂ := (q.val:ℂ)^(-β)
    let u : ℂ := (q.val:ℂ)⁻¹
    let v := χ.evalNat q.val
    let b : ℂ := (q.val:ℂ)^γ
    lemma162Local00 χ β γ q = lemma162M00 a u v (u*b) ∧
      lemma162Local01 χ β γ q = lemma162M01 a u v (u*b) ∧
      lemma162Local10 χ β γ q = lemma162M10 u v (u*b) ∧
      lemma162Local11 χ β γ q = lemma162M11 v (u*b) ∧
      lemma161LambdaFactor χ β q.val 1 = lemma162LocalLambda a u v := by
  let a : ℂ := (q.val:ℂ)^(-β)
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let b : ℂ := (q.val:ℂ)^γ
  have ha : ‖a‖=1 := lemma83_cpow_shift_norm q.property.pos β hβ
  have hb : ‖b‖=1 := by simpa [b] using lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hγ])
  have hu : ‖u‖≤1/2 := by
    dsimp [u]
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ)≤q.val by exact_mod_cast q.property.two_le)
  have hv : ‖v‖≤1 := χ.evalNat_norm_le_one _
  have hult : ‖u‖<1 := hu.trans_lt (by norm_num)
  have hx : ‖u*b‖<1 := by simpa [norm_mul,hb] using hult
  have hvu : ‖v*u‖<1 := lt_of_le_of_lt (by
    rw [norm_mul];exact mul_le_of_le_one_left (norm_nonneg _) hv) hult
  have hvx : ‖v*(u*b)‖<1 := lt_of_le_of_lt (by
    rw [norm_mul];exact mul_le_of_le_one_left (norm_nonneg _) hv) hx
  have hax : ‖a*(u*b)‖<1 := by simpa [norm_mul,ha] using hx
  have hau : ‖a*(v*u)‖<1 := by simpa [norm_mul,ha] using hvu
  have h00 : lemma162Local00 χ β γ q = lemma162M00 a u v (u*b) := by
    have hleft := lemma161_local_correction_identity a u v (u*b)
      (MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (q.val:ZMod D))
      (lemma83_one_sub_ne_zero hult) (lemma83_one_sub_ne_zero hx)
      (lemma83_one_sub_ne_zero hvu) (lemma83_one_sub_ne_zero hvx)
      (lemma83_one_sub_ne_zero hax) (lemma83_one_sub_ne_zero hau)
    have hright := lemma162_m00_source_identity a u v (u*b)
      (lemma83_one_sub_ne_zero hult) (lemma83_one_sub_ne_zero hx)
      (lemma83_one_sub_ne_zero hvu) (lemma83_one_sub_ne_zero hvx)
      (lemma83_one_sub_ne_zero hax) (lemma83_one_sub_ne_zero hau)
    have he : lemma162Local00 χ β γ q = lemma152LocalCorrection a 0 u v (u*b) := by
      unfold lemma162Local00 lemma161PrimeFactor
      rw [lemma32_prime_monomial_eq_cpow q.property.pos β,lemma162_center_prime_monomial q.property.pos γ]
    exact he.trans (hleft.symm.trans hright)
  have hlam : lemma161LambdaFactor χ β q.val 1 = lemma162LocalLambda a u v := by
    rw [lemma161_lambda_factor_rational χ β q.property.pos]
    unfold lemma162LocalLambda
    dsimp [a,u,v]
    congr 1
    ring
  refine ⟨h00,?_,?_,?_,hlam⟩
  · unfold lemma162Local01 lemma162GeneralMPrimeFactor
    simp only [if_neg q.property.not_dvd_one,if_pos (dvd_refl q.val)]
    rw [show lemma161PrimeFactor χ β q (1-γ)=lemma162M00 a u v (u*b) from h00,
      hlam,lemma162_center_prime_monomial q.property.pos γ]
    change lemma162M00 a u v (u*b)+lemma162LocalLambda a u v*v*(u*b)/
      ((1-u)*(1-v*(u*b))) = lemma162M01 a u v (u*b)
    unfold lemma162M00
    ring
  · simp [lemma162Local10,lemma162GeneralMPrimeFactor,q.property.not_dvd_one,
      lemma162M10,lemma162_center_prime_monomial q.property.pos γ]
  · simp [lemma162Local11,lemma162GeneralMPrimeFactor,lemma162M11,
      lemma162_center_prime_monomial q.property.pos γ]

end ZhangLS.Spec
