import ZhangLS.Spec.Lemma162LocalDataRational
import ZhangLS.Spec.Lemma162FirstRemainderNorm
import ZhangLS.Spec.Lemma162OddLocalRatio

/-! A fully uniform prime-error estimate for the ACTUAL raw factors.
Only unramified primes are included; ramified factors are treated separately. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2500000

lemma lemma162_actual_raw_linear_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (q : Nat.Primes) (hv : χ.evalNat q.val=1 ∨ χ.evalNat q.val=-1) :
    ‖lemma162RawLinear (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
      (lemma162Local10 χ β γ q) (lemma161LambdaFactor χ β q.val 1)
        ((q.val:ℂ)^γ) (χ.evalNat q.val)‖ ≤ 240/(q.val:ℝ) := by
  let a : ℂ := (q.val:ℂ)^(-β)
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let b : ℂ := (q.val:ℂ)^γ
  have ha : ‖a‖≤1 := (lemma83_cpow_shift_norm q.property.pos β hβ).le
  have hb : ‖b‖≤1 := by simpa [b] using (lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hγ])).le
  have huv : ‖u‖≤1/2 := by
    dsimp [u]
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ)≤q.val by exact_mod_cast q.property.two_le)
  have hvn : ‖v‖≤1 := χ.evalNat_norm_le_one _
  obtain ⟨hdu,hdvu,hdub,hdvub⟩ := lemma162_four_denominator_bounds u v b huv hvn hb
  have hu0 : 1-u≠0 := norm_pos_iff.mp (by linarith)
  have hvu0 : 1-v*u≠0 := norm_pos_iff.mp (by linarith)
  have hub0 : 1-u*b≠0 := norm_pos_iff.mp (by linarith)
  have hvub0 : 1-v*u*b≠0 := norm_pos_iff.mp (by linarith)
  have hcoeff := lemma162_shifted_first_coefficient a u v b hv hu0 hvu0 hub0 hvub0
  obtain ⟨h00,h01,h10,h11,hlam⟩ := lemma162_actual_local_data_rational χ β hβ γ hγ q
  have he : lemma162RawLinear (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
      (lemma162Local10 χ β γ q) (lemma161LambdaFactor χ β q.val 1) b v =
      u*(1+2*v)*lemma162FirstRemainder a u v b := by
    rw [h00,h01,h10,hlam]
    exact hcoeff
  change ‖lemma162RawLinear (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
      (lemma162Local10 χ β γ q) (lemma161LambdaFactor χ β q.val 1) b v‖ ≤ _
  rw [he,norm_mul,norm_mul]
  have hR := lemma162_first_remainder_bound a u v b ha huv hvn hb
  have hk := lemma162_norm_one_add_twice v hvn
  calc
    _ ≤ ‖u‖*3*80 := by gcongr
    _ = 240/(q.val:ℝ) := by dsimp [u]; rw [norm_inv,Complex.norm_natCast]; ring

lemma lemma162_actual_raw_unramified_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (q : Nat.Primes) (hv : χ.evalNat q.val=1 ∨ χ.evalNat q.val=-1)
    (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma162RawPrimeCorrection χ β γ q s-1‖ ≤
      lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) +
        (240/(q.val:ℝ))*‖lemma32PrimeMonomial q.val s‖ +
          (773*lemma162GeneralMNormBound)*‖lemma32PrimeMonomial q.val s‖^2 := by
  let b : ℂ := (q.val:ℂ)^γ
  let v := χ.evalNat q.val
  let z := lemma32PrimeMonomial q.val s
  have hv0 : χ.evalNat q.val≠0 := by rcases hv with h | h <;> rw [h] <;> norm_num
  have hs1 : 9/10≤(1-γ).re := by simp [hγ]; norm_num
  have h00 : ‖lemma162Local00 χ β γ q‖≤lemma162GeneralMNormBound := by
    simpa [lemma162Local00] using lemma162_general_m_local_norm χ β hβ 1 1 q (1-γ) hs1
  have h01 := lemma162_general_m_local_norm χ β hβ 1 q.val q (1-γ) hs1
  have h10 := lemma162_general_m_local_norm χ β hβ q.val 1 q (1-γ) hs1
  have h11 := lemma162_general_m_local_norm χ β hβ q.val q.val q (1-γ) hs1
  have hlam := lemma161_lambda_norm_le χ β hβ q.property
  have hb : ‖b‖≤1 := by simpa [b] using (lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hγ])).le
  have hvn : ‖v‖≤1 := χ.evalNat_norm_le_one _
  have hz : ‖z‖≤1 := (lemma152_monomial_norm_radius q s hs).trans lemma83_regular_radius_lt_one.le
  have ht := lemma162_raw_tail_bound (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
    (lemma162Local10 χ β γ q) (lemma162Local11 χ β γ q) (lemma161LambdaFactor χ β q.val 1)
    b v z lemma162GeneralMNormBound lemma162_general_m_norm_bound_pos.le h00 h01 h10 h11 hlam hb hvn hz
  have hlin := lemma162_actual_raw_linear_bound χ β hβ γ hγ q hv
  have hbase := lemma161_prime_error_uniform χ β hβ q (1-γ) hs1
  rw [lemma162RawPrimeCorrection,if_neg hv0,
    lemma162_raw_polynomial_expansion _ _ _ _ _ _ _ _ hv]
  change ‖lemma162Local00 χ β γ q+lemma162RawLinear (lemma162Local00 χ β γ q)
      (lemma162Local01 χ β γ q) (lemma162Local10 χ β γ q) (lemma161LambdaFactor χ β q.val 1) b v*z+
        z^2*lemma162RawTail (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
          (lemma162Local10 χ β γ q) (lemma162Local11 χ β γ q) (lemma161LambdaFactor χ β q.val 1) b v z-1‖ ≤ _
  let C := lemma162RawLinear (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
    (lemma162Local10 χ β γ q) (lemma161LambdaFactor χ β q.val 1) b v
  let T := lemma162RawTail (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
    (lemma162Local10 χ β γ q) (lemma162Local11 χ β γ q) (lemma161LambdaFactor χ β q.val 1) b v z
  change ‖lemma162Local00 χ β γ q+C*z+z^2*T-1‖≤_
  rw [show lemma162Local00 χ β γ q+C*z+z^2*T-1 =
    (lemma162Local00 χ β γ q-1)+C*z+z^2*T by ring]
  calc
    _ ≤ ‖lemma162Local00 χ β γ q-1‖+‖C*z‖+‖z^2*T‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) +
        (240/(q.val:ℝ))*‖z‖ + ‖z‖^2*(773*lemma162GeneralMNormBound) := by
      simp only [norm_mul,norm_pow]
      gcongr
      simpa [lemma162Local00] using hbase
    _ = _ := by dsimp [z]; ring

end ZhangLS.Spec
