import ZhangLS.Spec.Lemma162ActualUnramifiedBound
import ZhangLS.Spec.Lemma162ActualShiftedIdentity
import ZhangLS.Spec.Lemma32ModulusFactors

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def lemma162UnramifiedMajorant (q : Nat.Primes) : ℝ :=
  lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) +
    240*(q.val:ℝ)^(-(19/10:ℝ)) + (773*lemma162GeneralMNormBound)*(q.val:ℝ)^(-(9/5:ℝ))

lemma lemma162_unramified_majorant_nonneg (q : Nat.Primes) : 0≤lemma162UnramifiedMajorant q := by
  unfold lemma162UnramifiedMajorant
  have hC := lemma152_correction_constant_pos
  have hM := lemma162_general_m_norm_bound_pos
  positivity

lemma lemma162_unramified_majorant_summable : Summable lemma162UnramifiedMajorant := by
  have h19 : Summable (fun q : Nat.Primes => (q.val:ℝ)^(-(19/10:ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(19/10:ℝ) < -1)).subtype Nat.Prime
  have h18 : Summable (fun q : Nat.Primes => (q.val:ℝ)^(-(9/5:ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(9/5:ℝ) < -1)).subtype Nat.Prime
  exact ((h19.mul_left lemma152CorrectionConstant).add (h19.mul_left 240)).add
    (h18.mul_left (773*lemma162GeneralMNormBound))

lemma lemma162_unramified_raw_error_majorized {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (q : Nat.Primes) (hq : ¬q.val∣D) (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma162RawPrimeCorrection χ β γ q s-1‖≤lemma162UnramifiedMajorant q := by
  have hp : (0:ℝ)<q.val := by exact_mod_cast q.property.pos
  have hp1 : (1:ℝ)≤q.val := by exact_mod_cast q.property.one_lt.le
  have hz : ‖lemma32PrimeMonomial q.val s‖≤(q.val:ℝ)^(-(9/10:ℝ)) := by
    rw [lemma83_prime_monomial_norm_rpow q.property.pos]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hlin : (240/(q.val:ℝ))*‖lemma32PrimeMonomial q.val s‖≤240*(q.val:ℝ)^(-(19/10:ℝ)) := by
    calc
      _ ≤ (240/(q.val:ℝ))*(q.val:ℝ)^(-(9/10:ℝ)) := mul_le_mul_of_nonneg_left hz (by positivity)
      _ = _ := by
        rw [show -(19/10:ℝ)=(-1)+(-(9/10)) by ring,Real.rpow_add hp,Real.rpow_neg_one]
        ring
  have hsq : ‖lemma32PrimeMonomial q.val s‖^2≤(q.val:ℝ)^(-(9/5:ℝ)) := by
    calc
      _ ≤ ((q.val:ℝ)^(-(9/10:ℝ)))^2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ = _ := by
        rw [pow_two,← Real.rpow_add hp]
        congr 1
        ring
  have he := lemma162_actual_raw_unramified_error χ β hβ γ hγ q
    (lemma32_character_prime_cases_of_not_dvd χ q.property hq) s hs
  apply he.trans
  unfold lemma162UnramifiedMajorant
  have hM := lemma162_general_m_norm_bound_pos
  gcongr

lemma lemma162_ramified_raw_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) (hq : q.val∣D) (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma162RawPrimeCorrection χ β γ q s-1‖≤3 := by
  have hv := χ.evalNat_eq_zero_of_dvd_modulus hq q.property.ne_one
  rw [lemma162RawPrimeCorrection,if_pos hv]
  let z := lemma32PrimeMonomial q.val s
  have hz : ‖z‖≤1 := (lemma152_monomial_norm_radius q s hs).trans lemma83_regular_radius_lt_one.le
  change ‖(1-z)^2-1‖≤3
  rw [show (1-z)^2-1 = -2*z+z^2 by ring]
  calc
    _ ≤ ‖(-2:ℂ)*z‖+‖z^2‖ := norm_add_le _ _
    _ = 2*‖z‖+‖z‖^2 := by rw [norm_mul,norm_pow];norm_num
    _ ≤ 3 := by nlinarith [norm_nonneg z,pow_le_pow_left₀ (norm_nonneg z) hz 2]

noncomputable def lemma162RawMajorant (D : ℕ) (q : Nat.Primes) : ℝ :=
  lemma162UnramifiedMajorant q + if q.val∣D then 3 else 0

lemma lemma162_raw_majorant_nonneg (D : ℕ) (q : Nat.Primes) : 0≤lemma162RawMajorant D q := by
  unfold lemma162RawMajorant
  have h := lemma162_unramified_majorant_nonneg q
  split_ifs <;> linarith

lemma lemma162_raw_majorant_summable {D : ℕ} (hD : D≠0) : Summable (lemma162RawMajorant D) :=
  lemma162_unramified_majorant_summable.add
    (lemma162_prime_divisor_indicator_summable hD (fun _ => 3))

lemma lemma162_actual_raw_error_majorized {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (q : Nat.Primes) (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma162RawPrimeCorrection χ β γ q s-1‖≤lemma162RawMajorant D q := by
  unfold lemma162RawMajorant
  by_cases hq : q.val∣D
  · rw [if_pos hq]
    exact (lemma162_ramified_raw_error χ β γ q hq s hs).trans
      (by have h := lemma162_unramified_majorant_nonneg q; linarith)
  · rw [if_neg hq,add_zero]
    exact lemma162_unramified_raw_error_majorized χ β hβ γ hγ q hq s hs

end ZhangLS.Spec
