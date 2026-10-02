import Mathlib.Data.Nat.Choose.Basic
import ZhangLS.Spec.Lemma23Nu20Bounds
set_option autoImplicit false
namespace ZhangLS.Spec
set_option maxHeartbeats 2000000

lemma lemma34_multichoose_recurrence (k e : ℕ) (hk : 0 < k) :
    (e+1) * Nat.multichoose k (e+1) = (e+k) * Nat.multichoose k e := by
  rw [Nat.multichoose_eq,Nat.multichoose_eq]
  have h := Nat.add_one_mul_choose_eq (k+e-1) e
  have he : k+(e+1)-1 = k+e := by omega
  have hs : k+e-1+1 = k+e := by omega
  rw [he]
  rw [hs] at h
  simpa only [add_comm,mul_comm] using h.symm

lemma lemma34_multichoose_40_square_le_1600 (e : ℕ) :
    Nat.multichoose 40 e ^ 2 ≤ Nat.multichoose 1600 e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h40 := lemma34_multichoose_recurrence 40 e (by norm_num)
    have h1600 := lemma34_multichoose_recurrence 1600 e (by norm_num)
    have hc : (e+40) ^ 2 ≤ (e+1) * (e+1600) := by nlinarith
    have hh : (e+1) ^ 2 * Nat.multichoose 40 (e+1) ^ 2 ≤
        (e+1) ^ 2 * Nat.multichoose 1600 (e+1) := by
      calc
        _ = ((e+40) * Nat.multichoose 40 e) ^ 2 := by rw [← mul_pow,h40]
        _ ≤ ((e+1)*(e+1600)) * Nat.multichoose 1600 e := by
          rw [mul_pow]
          exact Nat.mul_le_mul hc ih
        _ = (e+1) * ((e+1600) * Nat.multichoose 1600 e) := by ring
        _ = (e+1) * ((e+1) * Nat.multichoose 1600 (e+1)) := by rw [← h1600]
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < (e+1)^2)).mp hh

end ZhangLS.Spec
