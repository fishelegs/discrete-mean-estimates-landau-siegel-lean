import ZhangLS.Spec.Lemma162LocalKernel
import ZhangLS.Spec.Lemma162HadamardH2H3

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma162RawP (b v z : ℂ) : ℂ := (1-b*z)*(1-v*b*z)^2
noncomputable def lemma162RawQ (v z : ℂ) : ℂ := (1-v*z)*(1-z)^2
noncomputable def lemma162RawS (b v z : ℂ) : ℂ :=
  1-b*v*(1+2*v)*z^2+b*v*(b+v)*z^3

noncomputable def lemma162RawPolynomial (F00 F01 F10 F11 lam b v z : ℂ) : ℂ :=
  (F00-lam*F10-F01+lam*F11)*lemma162RawP b v z*lemma162RawQ v z +
    (lam*F10-lam*F11)*lemma162RawQ v z +
    (F01-lam*F11)*lemma162RawP b v z + lam*F11*lemma162RawS b v z

lemma lemma162_common_denominator (D A B C P Q S : ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    D+A*(1/P)+B*(1/Q)+C*(S/(P*Q)) =
      (D*P*Q+A*Q+B*P+C*S)/(P*Q) := by
  field_simp

/-- Exact raw local Hadamard series. All exceptional constant terms remain. -/
lemma lemma162_raw_local_hasSum (F00 F01 F10 F11 lam b v z : ℂ)
    (hv : v=1 ∨ v=-1) (hz : ‖z‖ < 1) (hbz : ‖b*z‖ < 1) :
    HasSum (fun n : ℕ => lemma162RawCoefficient F00 F01 F10 F11 lam b v n *
      lemma83LocalH3 1 v v n*z^n)
      (lemma162RawPolynomial F00 F01 F10 F11 lam b v z /
        (lemma162RawP b v z*lemma162RawQ v z)) := by
  have hvnorm : ‖v‖ = 1 := by rcases hv with rfl | rfl <;> norm_num
  have hvz : ‖v*z‖ < 1 := by simpa [norm_mul,hvnorm] using hz
  have hvbz : ‖v*(b*z)‖ < 1 := by simpa [norm_mul,hvnorm] using hbz
  have hvvz : ‖v*(v*z)‖ < 1 := by simpa [norm_mul,hvnorm] using hz
  have hb : HasSum (fun n : ℕ => lemma83LocalH3 1 v v n*(b*z)^n)
      (1/lemma162RawP b v z) := by
    convert lemma83_local_h3_hasSum 1 v v (b*z) (by simpa using hbz) hvbz hvbz using 1
    simp [lemma162RawP,div_eq_mul_inv,mul_inv_rev,pow_two,mul_comm,mul_left_comm]
  have he : HasSum (fun n : ℕ => lemma83LocalH3 1 v v n*(v*z)^n)
      (1/lemma162RawQ v z) := by
    convert lemma83_local_h3_hasSum 1 v v (v*z) (by simpa using hvz) hvvz hvvz using 1
    rcases hv with rfl | rfl <;>
      simp [lemma162RawQ,div_eq_mul_inv,mul_inv_rev,pow_two,mul_comm,mul_left_comm]
  have hbe : HasSum (fun n : ℕ => lemma83LocalH2 b v n*lemma83LocalH3 1 v v n*z^n)
      (lemma162RawS b v z/(lemma162RawP b v z*lemma162RawQ v z)) := by
    convert lemma162_h2_h3_hadamard_hasSum b v 1 v v z
      (by simpa using hbz) hvbz hvbz (by simpa using hvz) hvvz hvvz using 1
    rcases hv with rfl | rfl
    all_goals unfold lemma162RawS lemma162RawP lemma162RawQ
    all_goals congr 1 <;> ring
  have h0 := hasSum_ite_eq (0:ℕ) (F00-lam*F10-F01+lam*F11)
  have hs := ((h0.add (hb.mul_left (lam*F10-lam*F11))).add
    (he.mul_left (F01-lam*F11))).add (hbe.mul_left (lam*F11))
  convert hs using 1
  · funext n
    by_cases hn : n=0
    · subst n
      simp [lemma162RawCoefficient]
    · simp only [lemma162RawCoefficient,if_neg hn,mul_pow]
      ring
  · have hP : lemma162RawP b v z ≠ 0 := by
      unfold lemma162RawP
      apply mul_ne_zero (lemma83_one_sub_ne_zero hbz)
      apply pow_ne_zero 2
      exact lemma83_one_sub_ne_zero (by simpa [mul_assoc] using hvbz)
    have hQ : lemma162RawQ v z ≠ 0 :=
      mul_ne_zero (lemma83_one_sub_ne_zero hvz) (pow_ne_zero 2 (lemma83_one_sub_ne_zero hz))
    exact (lemma162_common_denominator _ _ _ _ _ _ _ hP hQ).symm

end ZhangLS.Spec
