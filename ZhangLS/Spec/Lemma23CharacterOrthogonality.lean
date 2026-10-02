import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Character orthogonality for the discrete mean in Lemma 3.4

Mathlib supplies exact orthogonality for the full finite group of Dirichlet characters.  This
module records the Hermitian form of that identity, which is the kernel needed to expand the
character-family mean square of the actual `X₁` and `X₂` sums.  Prime-modulus separation and the
mean-square coefficient estimate are handled separately.
-/

namespace ZhangLS.Spec

/-- The Hermitian character kernel is diagonal on units modulo a nonzero modulus. -/
theorem lemma23_dirichletCharacter_hermitian_orthogonality
    {q : ℕ} [NeZero q] [Fact q.Prime] {a b : ZMod q}
    (ha : IsUnit a) :
    (∑ ψ : DirichletCharacter ℂ q, ψ a * star (ψ b)) =
      if a = b then (q.totient : ℂ) else 0 := by
  calc
    (∑ ψ : DirichletCharacter ℂ q, ψ a * star (ψ b)) =
        ∑ ψ : DirichletCharacter ℂ q, ψ a * ψ⁻¹ b := by
          apply Finset.sum_congr rfl
          intro ψ hψ
          rw [MulChar.star_apply']
    _ = ∑ ψ : DirichletCharacter ℂ q, ψ⁻¹ a * ψ b := by
      exact Fintype.sum_bijective (fun ψ : DirichletCharacter ℂ q => ψ⁻¹)
        inv_involutive.bijective
        (fun ψ => ψ a * ψ⁻¹ b) (fun ψ => ψ⁻¹ a * ψ b)
        (fun ψ => by simp)
    _ = if a = b then (q.totient : ℂ) else 0 := by
      simpa only [MulChar.inv_apply, Ring.inverse_eq_inv] using
        (DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) (n := q) ha b)

/-- For a prime modulus, distinct positive natural indices below the modulus are orthogonal
under the full family of Dirichlet characters.  This is the arithmetic input for the first
discrete mean estimate in Lemma 3.3. -/
theorem lemma23_dirichletCharacter_nat_hermitian_orthogonality
    {p : ℕ} (hp : p.Prime)
    {m n : ℕ} (hmpos : 0 < m) (hm_lt : m < p) (hn_lt : n < p) :
    (∑ ψ : DirichletCharacter ℂ p,
      ψ (m : ZMod p) * star (ψ (n : ZMod p))) =
      if m = n then (p.totient : ℂ) else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hmUnit : IsUnit (m : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdiv
    have hle : p ≤ m := Nat.le_of_dvd hmpos hdiv
    omega
  have hcast : ((m : ZMod p) = (n : ZMod p)) ↔ m = n := by
    rw [ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hn_lt]
  have horth := lemma23_dirichletCharacter_hermitian_orthogonality
    (a := (m : ZMod p)) (b := (n : ZMod p)) hmUnit
  simpa only [hcast] using horth

/-- Expand the complex squared norm of a finite sum into its Hermitian double sum. -/
theorem lemma23_complex_normSq_finset_sum
    {α : Type*} (s : Finset α) (f : α → ℂ) :
    (Complex.normSq (∑ i ∈ s, f i) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, star (f i) * f j := by
  rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sum]
  exact Finset.sum_mul_sum s s (fun i => star (f i)) f

/-- Exact Parseval identity for all Dirichlet characters modulo a prime, for a polynomial whose
index range is shorter than the modulus.  This is the discrete mean-value theorem needed for the
endpoint partial sums in Zhang's `X₁` and `X₂`. -/
theorem lemma23_prime_character_mean_square_exact
    {p M : ℕ} (hp : p.Prime)
    (hM : M < p) (a : ℕ → ℂ) :
    (∑ ψ : DirichletCharacter ℂ p,
      ‖∑ n ∈ Finset.Icc 1 M, a n * ψ (n : ZMod p)‖ ^ 2) =
      (p.totient : ℝ) *
        ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2 := by
  classical
  let K : Finset ℕ := Finset.Icc 1 M
  let c : DirichletCharacter ℂ p → ℕ → ℂ := fun ψ n => a n * ψ (n : ZMod p)
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hterm (ψ : DirichletCharacter ℂ p) :
      Complex.ofReal (‖∑ n ∈ K, c ψ n‖ ^ 2) =
        ∑ m ∈ K, ∑ n ∈ K, star (c ψ m) * c ψ n := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [c] using lemma23_complex_normSq_finset_sum K (fun n => c ψ n)
  have horth (m n : ℕ) (hm : m ∈ K) (hn : n ∈ K) :
      (∑ ψ : DirichletCharacter ℂ p,
        star (ψ (m : ZMod p)) * ψ (n : ZMod p)) =
        if m = n then (p.totient : ℂ) else 0 := by
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hm_lt : m < p := lt_of_le_of_lt (Finset.mem_Icc.mp hm).2 hM
    have hn_lt : n < p := lt_of_le_of_lt (Finset.mem_Icc.mp hn).2 hM
    calc
      _ = ∑ ψ : DirichletCharacter ℂ p,
          ψ (n : ZMod p) * star (ψ (m : ZMod p)) := by
            apply Finset.sum_congr rfl
            intro ψ hψ
            ring
      _ = if n = m then (p.totient : ℂ) else 0 :=
            lemma23_dirichletCharacter_nat_hermitian_orthogonality hp
              (hmpos := (Finset.mem_Icc.mp hn).1)
              (hm_lt := hn_lt) (hn_lt := hm_lt)
      _ = if m = n then (p.totient : ℂ) else 0 := by
            by_cases h : m = n <;> simp [h, eq_comm]
  have hmain :
      Complex.ofReal
          (∑ ψ : DirichletCharacter ℂ p,
            ‖∑ n ∈ K, c ψ n‖ ^ 2) =
        (p.totient : ℂ) *
          ∑ n ∈ K, Complex.normSq (a n) := by
    calc
      Complex.ofReal
          (∑ ψ : DirichletCharacter ℂ p,
            ‖∑ n ∈ K, c ψ n‖ ^ 2) =
        ∑ ψ : DirichletCharacter ℂ p,
          ∑ m ∈ K, ∑ n ∈ K, star (c ψ m) * c ψ n := by
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro ψ hψ
            exact hterm ψ
      _ = ∑ m ∈ K, ∑ ψ : DirichletCharacter ℂ p,
            ∑ n ∈ K, star (c ψ m) * c ψ n := by
            rw [Finset.sum_comm]
      _ = ∑ m ∈ K, ∑ n ∈ K,
            ∑ ψ : DirichletCharacter ℂ p, star (c ψ m) * c ψ n := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.sum_comm]
      _ = ∑ m ∈ K, ∑ n ∈ K,
            (star (a m) * a n) *
              ∑ ψ : DirichletCharacter ℂ p,
                star (ψ (m : ZMod p)) * ψ (n : ZMod p) := by
            apply Finset.sum_congr rfl
            intro m hm
            apply Finset.sum_congr rfl
            intro n hn
            calc
              (∑ ψ : DirichletCharacter ℂ p,
                  star (c ψ m) * c ψ n) =
                ∑ ψ : DirichletCharacter ℂ p,
                  (star (a m) * a n) *
                    (star (ψ (m : ZMod p)) * ψ (n : ZMod p)) := by
                    apply Finset.sum_congr rfl
                    intro ψ hψ
                    simp only [c, star_mul]
                    ring
              _ = (star (a m) * a n) *
                    ∑ ψ : DirichletCharacter ℂ p,
                      star (ψ (m : ZMod p)) * ψ (n : ZMod p) := by
                    rw [← Finset.mul_sum]
      _ = ∑ m ∈ K, ∑ n ∈ K,
            (star (a m) * a n) *
              (if m = n then (p.totient : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro m hm
            apply Finset.sum_congr rfl
            intro n hn
            rw [horth m n hm hn]
      _ = ∑ m ∈ K, (star (a m) * a m) * (p.totient : ℂ) := by
            apply Finset.sum_congr rfl
            intro m hm
            simp [mul_ite, Finset.sum_ite_eq, hm]
      _ = (p.totient : ℂ) * ∑ n ∈ K, Complex.normSq (a n) := by
            rw [← Finset.sum_mul]
            rw [mul_comm]
            congr 1
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro n hn
            rw [Complex.star_def]
            exact Complex.normSq_eq_conj_mul_self.symm
  apply Complex.ofReal_injective
  simpa [K, Complex.normSq_eq_norm_sq] using hmain

end ZhangLS.Spec
