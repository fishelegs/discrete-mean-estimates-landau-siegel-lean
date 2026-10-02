import ZhangLS.Spec.Lemma171EulerFactors

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 400000

/-- Additive Cauchy convolution of local prime-power coefficients. -/
noncomputable def lemma83AddConvolution (f g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ ij ∈ antidiagonal n, f ij.1 * g ij.2

/-- Coefficients of the product of two geometric series. -/
noncomputable def lemma83LocalH2 (a b : ℂ) : ℕ → ℂ :=
  lemma83AddConvolution (fun n => a^n) (fun n => b^n)

/-- Coefficients of the product of three geometric series. -/
noncomputable def lemma83LocalH3 (a b c : ℂ) : ℕ → ℂ :=
  lemma83AddConvolution (lemma83LocalH2 a b) (fun n => c^n)

/-- Coefficients of `(1-X)/((1-aX)(1-bX)(1-cX))`. -/
noncomputable def lemma83LocalKappa (a b c : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => lemma83LocalH3 a b c (n+1) - lemma83LocalH3 a b c n

@[simp] lemma lemma83_local_h2_zero (a b : ℂ) : lemma83LocalH2 a b 0 = 1 := by
  simp [lemma83LocalH2,lemma83AddConvolution]

@[simp] lemma lemma83_local_h3_zero (a b c : ℂ) : lemma83LocalH3 a b c 0 = 1 := by
  simp [lemma83LocalH3,lemma83AddConvolution]

@[simp] lemma lemma83_local_kappa_zero (a b c : ℂ) : lemma83LocalKappa a b c 0 = 1 := rfl

lemma lemma83_local_kappa_succ (a b c : ℂ) (n : ℕ) :
    lemma83LocalKappa a b c (n+1) =
      lemma83LocalH3 a b c (n+1) - lemma83LocalH3 a b c n := rfl

lemma lemma83_add_convolution_mul_pow (f g : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    lemma83AddConvolution f g n * z^n =
      lemma83AddConvolution (fun i => f i*z^i) (fun j => g j*z^j) n := by
  unfold lemma83AddConvolution
  rw [sum_mul]
  apply sum_congr rfl
  intro ij hij
  have h := mem_antidiagonal.mp hij
  rw [← h,pow_add]
  ring

lemma lemma83_add_convolution_hasSum {f g : ℕ → ℂ} {u v : ℂ}
    (hf : HasSum f u) (hg : HasSum g v) :
    HasSum (lemma83AddConvolution f g) (u*v) := by
  have hfn : Summable (fun n => ‖f n‖) := summable_norm_iff.mpr hf.summable
  have hgn : Summable (fun n => ‖g n‖) := summable_norm_iff.mpr hg.summable
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  convert hs using 1
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn,
    hf.tsum_eq,hg.tsum_eq]

lemma lemma83_add_convolution_power_series_hasSum {f g : ℕ → ℂ} {u v z : ℂ}
    (hf : HasSum (fun n => f n*z^n) u) (hg : HasSum (fun n => g n*z^n) v) :
    HasSum (fun n => lemma83AddConvolution f g n*z^n) (u*v) := by
  simpa only [lemma83_add_convolution_mul_pow] using lemma83_add_convolution_hasSum hf hg

lemma lemma83_local_h2_hasSum (a b z : ℂ) (ha : ‖a*z‖ < 1) (hb : ‖b*z‖ < 1) :
    HasSum (fun n => lemma83LocalH2 a b n*z^n) ((1-a*z)⁻¹*(1-b*z)⁻¹) := by
  apply lemma83_add_convolution_power_series_hasSum
  · simpa only [mul_pow] using hasSum_geometric_of_norm_lt_one ha
  · simpa only [mul_pow] using hasSum_geometric_of_norm_lt_one hb

lemma lemma83_local_h3_hasSum (a b c z : ℂ)
    (ha : ‖a*z‖ < 1) (hb : ‖b*z‖ < 1) (hc : ‖c*z‖ < 1) :
    HasSum (fun n => lemma83LocalH3 a b c n*z^n)
      ((1-a*z)⁻¹*(1-b*z)⁻¹*(1-c*z)⁻¹) := by
  apply lemma83_add_convolution_power_series_hasSum
  · exact lemma83_local_h2_hasSum a b z ha hb
  · simpa only [mul_pow] using hasSum_geometric_of_norm_lt_one hc

/-- The exact convergent local factor, under the three geometric convergence conditions. -/
lemma lemma83_local_kappa_hasSum (a b c z : ℂ)
    (ha : ‖a*z‖ < 1) (hb : ‖b*z‖ < 1) (hc : ‖c*z‖ < 1) :
    HasSum (fun n => lemma83LocalKappa a b c n*z^n)
      ((1-z)/((1-a*z)*(1-b*z)*(1-c*z))) := by
  let H := (1-a*z)⁻¹*(1-b*z)⁻¹*(1-c*z)⁻¹
  have hh : HasSum (fun n => lemma83LocalH3 a b c n*z^n) H :=
    lemma83_local_h3_hasSum a b c z ha hb hc
  have ht : HasSum (fun n => lemma83LocalH3 a b c (n+1)*z^(n+1)) (H-1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hh
  have hk : HasSum (fun n => lemma83LocalKappa a b c (n+1)*z^(n+1))
      (H-1-z*H) := by
    convert ht.sub (hh.mul_left z) using 1
    funext n
    rw [lemma83_local_kappa_succ,pow_succ]
    ring
  have hall : HasSum (fun n => lemma83LocalKappa a b c n*z^n) (H-1-z*H+1) := by
    simpa using (hasSum_nat_add_iff (f := fun n => lemma83LocalKappa a b c n*z^n) 1).mp hk
  convert hall using 1
  dsimp [H]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma lemma83_local_kappa_summable (a b c z : ℂ)
    (ha : ‖a*z‖ < 1) (hb : ‖b*z‖ < 1) (hc : ‖c*z‖ < 1) :
    Summable (fun n => lemma83LocalKappa a b c n*z^n) :=
  (lemma83_local_kappa_hasSum a b c z ha hb hc).summable

lemma lemma83_local_kappa_norm_summable (a b c z : ℂ)
    (ha : ‖a*z‖ < 1) (hb : ‖b*z‖ < 1) (hc : ‖c*z‖ < 1) :
    Summable (fun n => ‖lemma83LocalKappa a b c n*z^n‖) :=
  summable_norm_iff.mpr (lemma83_local_kappa_summable a b c z ha hb hc)

lemma lemma83_local_h2_one (n : ℕ) : lemma83LocalH2 1 1 n = (n+1 : ℂ) := by
  simp [lemma83LocalH2,lemma83AddConvolution]

lemma lemma83_local_h3_one (n : ℕ) :
    lemma83LocalH3 1 1 1 n = ∑ k ∈ range (n+1), (k+1 : ℂ) := by
  simp only [lemma83LocalH3,lemma83AddConvolution,lemma83_local_h2_one,one_pow,mul_one]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k _ => (k+1 : ℂ)) n

@[simp] lemma lemma83_local_kappa_one (n : ℕ) : lemma83LocalKappa 1 1 1 n = (n+1 : ℂ) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [lemma83_local_kappa_succ,lemma83_local_h3_one,lemma83_local_h3_one,sum_range_succ]
    simp

lemma lemma83_local_kappa_first (a b c : ℂ) : lemma83LocalKappa a b c 1 = a+b+c-1 := by
  simp [lemma83LocalKappa,lemma83LocalH3,lemma83LocalH2,lemma83AddConvolution,
    Finset.Nat.antidiagonal_succ]
  ring

end ZhangLS.Spec
