import ZhangLS.Spec.Proposition71ActualKappaSeries
import ZhangLS.Spec.Lemma83ModifiedKappaProduct
import ZhangLS.Spec.Proposition71DivisorWeights
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_principal_character_nat (m n : ℕ) :
    (1 : DirichletCharacter ℂ m) (n : ZMod m) = if n.Coprime m then 1 else 0 := by
  by_cases h : n.Coprime m
  · rw [if_pos h]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n m).mpr h)
  · rw [if_neg h]
    exact MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using h)

lemma proposition71_principal_LSeries {m : ℕ} (hm : m ≠ 0) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ m) (n : ZMod m)) s =
      riemannZeta s * ∏ p ∈ m.primeFactors, (1-(p : ℂ)^(-s)) := by
  letI : NeZero m := ⟨hm⟩
  have hh := DirichletCharacter.LSeries_changeLevel (show 1 ∣ m from one_dvd m)
    (1 : DirichletCharacter ℂ 1) hs
  have hc (p : ℕ) : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  calc
    _ = LSeries (1 : ℕ → ℂ) s * ∏ p ∈ m.primeFactors, (1-(p : ℂ)^(-s)) := by
      simpa only [DirichletCharacter.changeLevel_one, hc, one_mul] using hh
    _ = _ := by rw [LSeries_one_eq_riemannZeta hs]


lemma proposition71_coprime_kappa_summable (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re = 0) (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => if n.Coprime m then lemma83Kappa β n else 0) s := by
  have hh := proposition71_kappa_twist_summable (1 : DirichletCharacter ℂ m) β hβ hs
  simpa only [proposition71_principal_character_nat, ite_mul, one_mul, zero_mul] using hh

/-- The genuine coprime κ series, with its exact finite Euler correction. -/
theorem proposition71_coprime_kappa_LSeries (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re = 0) {m : ℕ} (hm : m ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => if n.Coprime m then lemma83Kappa β n else 0) s =
      lemma83Lambda β m s *
        (riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s) := by
  have hsβ (j : Fin 3) : 1 < (s+β j).re := by simpa [hβ j] using hs
  have hh := proposition71_kappa_twist_LSeries_ratio
    (1 : DirichletCharacter ℂ m) β hβ hs
  have he : (fun n : ℕ => (1 : DirichletCharacter ℂ m) (n : ZMod m)*lemma83Kappa β n) =
      (fun n : ℕ => if n.Coprime m then lemma83Kappa β n else 0) := by
    funext n
    simp only [proposition71_principal_character_nat, ite_mul, one_mul, zero_mul]
  rw [he] at hh
  rw [hh, proposition71_principal_LSeries hm (hsβ 0),
    proposition71_principal_LSeries hm (hsβ 1),
    proposition71_principal_LSeries hm (hsβ 2), proposition71_principal_LSeries hm hs]
  have heβ (j : Fin 3) : -(s+β j) = -s-β j := by ring
  simp only [lemma83Lambda, lemma83LambdaFactor, heβ,
    Finset.prod_mul_distrib, div_eq_mul_inv, mul_inv_rev, ← Finset.prod_inv_distrib]
  ring

end ZhangLS.Spec
