import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Colon
import Lean.Elab.Tactic.Omega

/-! A coefficient-level weighted colon argument for the local polynomial
`x^4 + x^2 + y^4`. The x-degree is bounded, but the y-degree need not be. -/

noncomputable section

namespace PiWeightedColon

def weight (d k c : ℕ) : ℕ := k + 2 * (c / d)

def Data {R : Type*} [Zero R] (d m : ℕ) (f : ℕ → ℕ → R) : Prop :=
  ∀ k c, weight d k c < m → f k c = 0

def action {R : Type*} [AddZeroClass R] (f : ℕ → ℕ → R) (k c : ℕ) : R :=
  (if 4 ≤ k then f (k - 4) c else 0) +
  (if 2 ≤ k then f (k - 2) c else 0) +
  (if 4 ≤ c then f k (c - 4) else 0)

theorem action_data {R : Type*} [AddZeroClass R] {d m : ℕ}
    (hd : d = 1 ∨ d = 3) {f : ℕ → ℕ → R} (hf : Data d m f) :
    Data d (m + 2) (action f) := by
  intro k c hkc
  unfold action
  have h4 : (if 4 ≤ k then f (k - 4) c else 0) = 0 := by
    split_ifs with h
    · apply hf
      rcases hd with rfl | rfl <;> simp only [weight] at * <;> omega
    · rfl
  have h2 : (if 2 ≤ k then f (k - 2) c else 0) = 0 := by
    split_ifs with h
    · apply hf
      simp only [weight] at *
      omega
    · rfl
  have hy : (if 4 ≤ c then f k (c - 4) else 0) = 0 := by
    split_ifs with h
    · apply hf
      rcases hd with rfl | rfl <;> simp only [weight] at * <;> omega
    · rfl
  rw [h4, h2, hy, zero_add, zero_add]

/-- Recover every low-weight input coefficient from the output coefficient at
`(k+2,c)`. The x⁴ contribution has strictly lower input weight. The y⁴
contribution has lower weight, or the same weight and larger x exponent.
Strong induction on weight, followed by induction on `B-k`, handles both.
Only additive cancellation is used; the coefficient ring need not be a domain. -/
theorem data_of_action {R : Type*} [AddCancelMonoid R] {d m B : ℕ}
    (hd : d = 1 ∨ d = 3) {f : ℕ → ℕ → R}
    (hB : ∀ k c, B ≤ k → f k c = 0)
    (hf : Data d (m + 2) (action f)) : Data d m f := by
  have recover : ∀ w k c, weight d k c = w → w < m → f k c = 0 := by
    intro w
    induction w using Nat.strong_induction_on with
    | h w ih =>
      have inner : ∀ b k c, B - k = b → weight d k c = w → w < m → f k c = 0 := by
        intro b
        induction b using Nat.strong_induction_on with
        | h b ihb =>
          intro k c hb hw hwm
          by_cases hk : B ≤ k
          · exact hB k c hk
          have hx : (if 4 ≤ k + 2 then f (k + 2 - 4) c else 0) = 0 := by
            split_ifs with h
            · have hlt : weight d (k + 2 - 4) c < w := by
                simp only [weight] at hw ⊢
                omega
              exact ih _ hlt _ _ rfl (by omega)
            · rfl
          have hy : (if 4 ≤ c then f (k + 2) (c - 4) else 0) = 0 := by
            split_ifs with h
            · have hw' : weight d (k + 2) (c - 4) ≤ w := by
                rcases hd with rfl | rfl <;> simp only [weight] at * <;> omega
              by_cases hlt : weight d (k + 2) (c - 4) < w
              · exact ih _ hlt _ _ rfl (by omega)
              · apply ihb (B - (k + 2)) _ (k + 2) (c - 4) rfl (by omega) hwm
                omega
            · rfl
          have hz := hf (k + 2) c (by simp only [weight] at hw ⊢; omega)
          unfold action at hz
          rw [hx, hy, if_pos (by omega), show k + 2 - 2 = k by omega,
            zero_add, add_zero] at hz
          exact hz
      intro k c hw hwm
      exact inner (B - k) k c rfl hw hwm
  intro k c hkc
  exact recover (weight d k c) k c rfl hkc

open Polynomial

abbrev Bivariate (R : Type*) [Semiring R] := Polynomial (Polynomial R)

def coeff {R : Type*} [Semiring R] (f : Bivariate R) (k c : ℕ) : R :=
  (f.coeff k).coeff c

def localQ (R : Type*) [Semiring R] : Bivariate R :=
  X ^ 4 + X ^ 2 + C (X ^ 4)

theorem coeff_if {R : Type*} [Semiring R] (h : Prop) [Decidable h]
    (p q : Polynomial R) (n : ℕ) :
    (if h then p else q).coeff n = if h then p.coeff n else q.coeff n := by
  split <;> rfl

theorem coeff_localQ_mul {R : Type*} [CommSemiring R]
    (f : Bivariate R) (k c : ℕ) :
    coeff (localQ R * f) k c = action (coeff f) k c := by
  simp only [coeff, localQ, action, add_mul, Polynomial.coeff_add,
    coeff_X_pow_mul', coeff_C_mul, coeff_if, Polynomial.coeff_zero]

theorem coeff_x_bound {R : Type*} [Semiring R] (f : Bivariate R) :
    ∀ k c, f.natDegree + 1 ≤ k → coeff f k c = 0 := by
  intro k c hk
  simp [coeff, coeff_eq_zero_of_natDegree_lt (show f.natDegree < k by omega)]

/-- Exact local weighted colon identity, stated as coefficient vanishing.
No ideal-membership characterization is assumed by this theorem. -/
theorem weighted_colon {R : Type*} [CommRing R] {d m : ℕ}
    (hd : d = 1 ∨ d = 3) (f : Bivariate R) :
    Data d (m + 2) (coeff (localQ R * f)) ↔ Data d m (coeff f) := by
  have heq : coeff (localQ R * f) = action (coeff f) := by
    funext k c
    exact coeff_localQ_mul f k c
  rw [heq]
  exact ⟨data_of_action hd (coeff_x_bound f), action_data hd⟩

/-- The `2N+1` thresholds occurring in the local data at either endpoint. -/
theorem weighted_colon_step {R : Type*} [CommRing R] {d : ℕ}
    (hd : d = 1 ∨ d = 3) (N : ℕ) (f : Bivariate R) :
    Data d (2 * (N + 1) + 1) (coeff (localQ R * f)) ↔
      Data d (2 * N + 1) (coeff f) := by
  have ht : 2 * (N + 1) + 1 = (2 * N + 1) + 2 := by omega
  rw [ht]
  exact weighted_colon hd f

theorem data_mul {R : Type*} [CommRing R] {d m : ℕ}
    (a f : Bivariate R) (hf : Data d m (coeff f)) :
    Data d m (coeff (a * f)) := by
  intro k c hkc
  unfold coeff
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro uv huv
  have hk := Finset.mem_antidiagonal.mp hij
  have hc := Finset.mem_antidiagonal.mp huv
  have hc' : uv.2 / d ≤ c / d := Nat.div_le_div_right (by omega)
  have hz := hf ij.2 uv.2 (by simp only [weight] at *; omega)
  change (a.coeff ij.1).coeff uv.1 * coeff f ij.2 uv.2 = 0
  rw [hz, mul_zero]

/-- The local data ideal defined directly by the floored weight condition. -/
def dataIdeal (R : Type*) [CommRing R] (d m : ℕ) : Ideal (Bivariate R) where
  carrier := {f | Data d m (coeff f)}
  zero_mem' := by intro k c _; simp [coeff]
  add_mem' := by
    intro a b ha hb k c hkc
    simp only [coeff, Polynomial.coeff_add]
    change coeff a k c + coeff b k c = 0
    rw [ha k c hkc, hb k c hkc, zero_add]
  smul_mem' := by
    intro a f hf
    exact data_mul a f hf

theorem mem_dataIdeal {R : Type*} [CommRing R] (d m : ℕ) (f : Bivariate R) :
    f ∈ dataIdeal R d m ↔ Data d m (coeff f) := Iff.rfl

/-- Ideal form of the local weighted colon identity. -/
theorem dataIdeal_colon {R : Type*} [CommRing R] {d m : ℕ}
    (hd : d = 1 ∨ d = 3) :
    (dataIdeal R d (m + 2)).colon {localQ R} = dataIdeal R d m := by
  ext f
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
  exact weighted_colon hd f

end PiWeightedColon
