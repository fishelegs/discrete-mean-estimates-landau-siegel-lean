import ZhangLS.Spec.Lemma162ActualLocalBridge
import ZhangLS.Spec.Lemma162LocalExtraction

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def lemma162RawPrimeCorrection {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  if χ.evalNat q.val=0 then (1-lemma32PrimeMonomial q.val s)^2 else
    lemma162RawPolynomial (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
      (lemma162Local10 χ β γ q) (lemma162Local11 χ β γ q) (lemma161LambdaFactor χ β q.val 1)
        ((q.val:ℂ)^γ) (χ.evalNat q.val) (lemma32PrimeMonomial q.val s)

lemma lemma162_normalizers_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) :
    HasProd (lemma162LocalNormalizer χ β γ) (lemma161Star χ β (1-γ)) := by
  have hs : 9/10 ≤ (1-γ).re := by simp [hγ]; norm_num
  have hodd := (lemma162_odd_m_multipliable χ β hβ (by norm_num : (1:ℕ)≠0)
    (by norm_num : (1:ℕ)≠0) (1-γ) hs).hasProd
  have htwo := lemma153_finite_ite_hasProd ({lemma162PrimeTwo} : Finset Nat.Primes)
    (fun _q => lemma162TwoNormalizer χ β (1-γ))
  simp only [prod_singleton] at htwo
  rw [lemma162_star_odd_decomposition χ β hβ (1-γ) hs]
  apply (htwo.mul hodd).congr_fun
  intro q
  by_cases hq : q=lemma162PrimeTwo
  · subst q
    simp [lemma162LocalNormalizer,lemma162OddMPrimeFactor,lemma162PrimeTwo]
  · have hp : 2<q.val := by
      have htwo := q.property.two_le
      have hn : q.val≠2 := fun h => hq (Subtype.ext h)
      omega
    simp [lemma162LocalNormalizer,lemma162OddMPrimeFactor,hq,hp,lemma162Local00]

lemma lemma162_local_normalizer_nonzero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) (q : Nat.Primes) :
    lemma162LocalNormalizer χ β γ q ≠ 0 := by
  intro hz
  exact hstar ((lemma162_normalizers_hasProd χ β hβ γ hγ).unique
    (hasProd_zero_of_exists_eq_zero ⟨q,hz⟩))

lemma lemma162_ramified_actual_data {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) (hq : χ.evalNat q.val=0) :
    lemma162Local00 χ β γ q=1 ∧ lemma162Local01 χ β γ q=1 ∧
      lemma162Local10 χ β γ q=1 ∧ lemma162Local11 χ β γ q=1 ∧
        lemma161LambdaFactor χ β q.val 1=1 := by
  have hb : lemma161PrimeFactor χ β q (1-γ)=1 := by
    simp [lemma161PrimeFactor,lemma152LocalCorrection,hq]
  simp [lemma162Local00,lemma162Local01,lemma162Local10,lemma162Local11,
    lemma162GeneralMPrimeFactor,hq,hb,lemma161LambdaFactor]

lemma lemma162_h3_ramified (n : ℕ) : lemma83LocalH3 1 0 0 n=1 := by
  unfold lemma83LocalH3 lemma83AddConvolution
  simp_rw [lemma161_h2_zero]
  change lemma83LocalH2 1 0 n=1
  rw [lemma161_h2_zero]
  simp

lemma lemma162_ramified_raw_coefficient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) (hq : χ.evalNat q.val=0) (n : ℕ) :
    lemma162RawPrimeCoefficient χ β γ q n = ((q.val:ℂ)^γ)^n := by
  obtain ⟨h00,h01,h10,h11,hlam⟩ := lemma162_ramified_actual_data χ β γ q hq
  simp [lemma162RawPrimeCoefficient,h00,h01,h10,h11,hlam,hq,
    lemma162RawCoefficient,lemma162_h3_ramified,lemma161_h2_zero]

lemma lemma162_ramified_normalizer {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) (hq : χ.evalNat q.val=0) :
    lemma162LocalNormalizer χ β γ q=1 := by
  by_cases he : q=lemma162PrimeTwo
  · subst q
    have h2 : χ.evalNat 2=0 := hq
    simp [lemma162LocalNormalizer,lemma162TwoNormalizer,h2,
      lemma161PrimeFactor,lemma152LocalCorrection,lemma162PrimeTwo]
  · simp only [lemma162LocalNormalizer,if_neg he]
    exact (lemma162_ramified_actual_data χ β γ q hq).1

/-- Exact finite-D extraction of each actual local series. All six shifted
factors are present, and no χ(2)=1 baseline is canceled by division. -/
lemma lemma162_actual_raw_local_extraction {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) (q : Nat.Primes)
    (s : ℂ) (hs : 1<s.re) :
    lemma162RawPrimeCorrection χ β γ q s =
      lemma162LocalNormalizer χ β γ q *
        lemma162ShiftedRemoval (χ.evalNat q.val) ((q.val:ℂ)^γ) (lemma32PrimeMonomial q.val s) *
          lemma162ActualLocalSeries χ β γ q s := by
  let b : ℂ := (q.val:ℂ)^γ
  let v := χ.evalNat q.val
  let z := lemma32PrimeMonomial q.val s
  let N := lemma162LocalNormalizer χ β γ q
  have hn : ‖b‖=1 := by
    simpa [b] using lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hγ])
  have hz : ‖z‖<1 := (lemma152_monomial_norm_half q.property s hs.le).trans_lt (by norm_num)
  have hbz : ‖b*z‖<1 := by simpa [norm_mul,hn] using hz
  have hvz : ‖v*z‖<1 := lt_of_le_of_lt
    (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hz
  have hvbz : ‖v*b*z‖<1 := by
    rw [mul_assoc]
    exact lt_of_le_of_lt (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hbz
  have hN : N ≠ 0 := lemma162_local_normalizer_nonzero χ β hβ γ hγ hstar q
  rw [lemma162_actual_local_series_eq_raw χ β hβ γ hγ hstar q s]
  by_cases hq : χ.evalNat q.val=0
  · rw [lemma162RawPrimeCorrection,if_pos hq,lemma162_ramified_normalizer χ β γ q hq]
    simp only [lemma162_ramified_raw_coefficient χ β γ q hq,div_one]
    rw [hq]
    have he : (∑' n : ℕ, b^n*z^n) = 1/(1-b*z) := by
      simpa [mul_pow] using (hasSum_geometric_of_norm_lt_one hbz).tsum_eq
    change (1-z)^2 = 1*lemma162ShiftedRemoval 0 b z*(∑' n : ℕ, b^n*z^n)
    rw [he]
    unfold lemma162ShiftedRemoval
    have hbzn := lemma83_one_sub_ne_zero hbz
    have hbzn' : 1-z*b ≠ 0 := by simpa [mul_comm] using hbzn
    simp only [zero_mul,sub_zero,one_pow,mul_one,one_mul]
    field_simp [hbzn,hbzn']
  · have hv : v=1 ∨ v=-1 := by
      have hh := MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (q.val:ZMod D)
      exact hh.resolve_left hq
    have hraw := lemma162_raw_local_hasSum (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
      (lemma162Local10 χ β γ q) (lemma162Local11 χ β γ q) (lemma161LambdaFactor χ β q.val 1) b v z hv hz hbz
    have he : (∑' n : ℕ, (lemma162RawPrimeCoefficient χ β γ q n/N)*z^n) =
      (lemma162RawPolynomial (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
        (lemma162Local10 χ β γ q) (lemma162Local11 χ β γ q) (lemma161LambdaFactor χ β q.val 1) b v z /
        (lemma162RawP b v z*lemma162RawQ v z))/N := by
      convert (hraw.div_const N).tsum_eq using 1
      apply tsum_congr
      intro n
      unfold lemma162RawPrimeCoefficient
      ring
    change lemma162RawPrimeCorrection χ β γ q s = N*lemma162ShiftedRemoval v b z*
      (∑' n : ℕ, (lemma162RawPrimeCoefficient χ β γ q n/N)*z^n)
    rw [he,lemma162RawPrimeCorrection,if_neg hq]
    have hP : lemma162RawP b v z ≠ 0 :=
      mul_ne_zero (lemma83_one_sub_ne_zero hbz) (pow_ne_zero 2 (lemma83_one_sub_ne_zero hvbz))
    have hQ : lemma162RawQ v z ≠ 0 :=
      mul_ne_zero (lemma83_one_sub_ne_zero hvz) (pow_ne_zero 2 (lemma83_one_sub_ne_zero hz))
    have hr : lemma162ShiftedRemoval v b z = lemma162RawP b v z*lemma162RawQ v z := by
      unfold lemma162ShiftedRemoval lemma162RawP lemma162RawQ
      ring
    rw [hr]
    change _ = N*(lemma162RawP b v z*lemma162RawQ v z)*(_/(lemma162RawP b v z*lemma162RawQ v z)/N)
    field_simp
    rfl

end ZhangLS.Spec
