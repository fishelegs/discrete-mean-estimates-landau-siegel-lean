import ZhangLS.Spec.Lemma33Fractions
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxHeartbeats 2000000

/-- Distinct reduced fractions have nonzero cross difference, even for composite denominators. -/
theorem reduced_fraction_cross_ne {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hap : a.Coprime p) (hbq : b.Coprime q)
    (hne : p ≠ q ∨ a ≠ b) : a*q ≠ b*p := by
  intro he
  have hpq : p ∣ q := hap.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left p b)
  have hqp : q ∣ p := hbq.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left q a)
  have hp_eq : p = q := Nat.dvd_antisymm hpq hqp
  subst q
  have hab : a = b := Nat.eq_of_mul_eq_mul_right hp he
  exact hne.elim (fun h => h rfl) (fun h => h hab)

/-- The ordinary real distance between distinct reduced fractions is at least the reciprocal
product of their denominators. -/
theorem reduced_fraction_separation {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hap : a.Coprime p) (hbq : b.Coprime q)
    (hne : p ≠ q ∨ a ≠ b) :
    1 / ((p : ℝ) * q) ≤ |(a : ℝ)/p - (b : ℝ)/q| := by
  have hcross := reduced_fraction_cross_ne hp hq hap hbq hne
  have hnum : 1 ≤ |(a : ℝ)*q - (b : ℝ)*p| := by
    rcases lt_or_gt_of_ne hcross with h | h
    · have hc : (a : ℝ)*q + 1 ≤ (b : ℝ)*p := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hc : (b : ℝ)*p + 1 ≤ (a : ℝ)*q := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have he : (a : ℝ)/p - (b : ℝ)/q = ((a : ℝ)*q - (b : ℝ)*p)/(p*q) := by
    field_simp
  rw [he,abs_div,abs_of_pos (mul_pos hpR hqR)]
  exact div_le_div_of_nonneg_right hnum (mul_pos hpR hqR).le

end ZhangLS.Spec
