import ZhangLS.Spec.Lemma23GoodSet
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000

lemma lemma33_prime_fraction_cross_ne {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 0 < a) (hap : a < p) (hb : 0 < b) (hbq : b < q)
    (hne : p ≠ q ∨ a ≠ b) : a*q ≠ b*p := by
  intro he
  have hd : p ∣ a*q := by rw [he]; exact dvd_mul_left p b
  have hpa : ¬p ∣ a := by
    intro hd
    exact (not_le_of_gt hap) (Nat.le_of_dvd ha hd)
  have hpq : p ∣ q := (hp.dvd_mul.mp hd).resolve_left hpa
  have hp_eq : p = q := (Nat.dvd_prime hq).mp hpq |>.resolve_left hp.ne_one
  subst q
  have hab : a = b := Nat.eq_of_mul_eq_mul_right hp.pos he
  exact hne.elim (fun h => h rfl) (fun h => h hab)

lemma lemma33_prime_fraction_separation {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 0 < a) (hap : a < p) (hb : 0 < b) (hbq : b < q)
    (hne : p ≠ q ∨ a ≠ b) :
    1 / ((p : ℝ) * q) ≤ |(a : ℝ)/p - (b : ℝ)/q| := by
  have hcross := lemma33_prime_fraction_cross_ne hp hq ha hap hb hbq hne
  have hnum : 1 ≤ |(a : ℝ)*q - (b : ℝ)*p| := by
    rcases lt_or_gt_of_ne hcross with h | h
    · have hc : (a : ℝ)*q + 1 ≤ (b : ℝ)*p := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hc : (b : ℝ)*p + 1 ≤ (a : ℝ)*q := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have he : (a : ℝ)/p - (b : ℝ)/q = ((a : ℝ)*q - (b : ℝ)*p)/(p*q) := by
    field_simp
  rw [he,abs_div,abs_of_pos (mul_pos hpR hqR)]
  exact div_le_div_of_nonneg_right hnum (mul_pos hpR hqR).le

end ZhangLS.Spec
