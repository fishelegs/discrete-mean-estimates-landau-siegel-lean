import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact finite orthogonal projections for the principal-subtracted arithmetic sample mean.
The input vector is arbitrary: no zero-mean assumption is made about a polar approximation. -/
set_option autoImplicit false
namespace ZhangLS.Spec.ActualSampleProjection
open scoped BigOperators
noncomputable section
variable {p : ℕ} [NeZero p]
abbrev Samples (p : ℕ) := ZMod p → ℂ

def energy (z : Samples p) : ℝ := ∑ j, Complex.normSq (z j)
def pairing (z w : Samples p) : ℂ := ∑ j, z j * star (w j)
def mean (z : Samples p) : ℂ := (∑ j, z j) / (p : ℂ)
def principal (p : ℕ) (j : ZMod p) : ℂ := if j = 0 then 1 else -1 / ((p : ℂ) - 1)
def evenPart (z : Samples p) : Samples p := fun j => (z j + z (-j)) / 2
def oddPart (z : Samples p) : Samples p := fun j => (z j - z (-j)) / 2
def evenProjection (z : Samples p) : Samples p := fun j =>
  evenPart z j - mean z - principal p j * (z 0 - mean z)
def oddProjection (z : Samples p) : Samples p := oddPart z

def Even (z : Samples p) : Prop := ∀ j, z (-j) = z j
def Odd (z : Samples p) : Prop := ∀ j, z (-j) = -z j
def EvenTarget (z : Samples p) : Prop := Even z ∧ (∑ j, z j) = 0 ∧ z 0 = 0

theorem sum_neg (f : ZMod p → ℂ) : (∑ j, f (-j)) = ∑ j, f j := by
  exact Fintype.sum_bijective (fun j : ZMod p => -j) neg_involutive.bijective _ _
    (fun _ => rfl)

theorem pairing_self (z : Samples p) : pairing z z = (energy z : ℂ) := by
  simp only [pairing, energy, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def, mul_comm]

theorem pairing_add_left (x y z : Samples p) :
    pairing (fun j => x j + y j) z = pairing x z + pairing y z := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

theorem pairing_sub_left (x y z : Samples p) :
    pairing (fun j => x j - y j) z = pairing x z - pairing y z := by
  simp [pairing, sub_mul, Finset.sum_sub_distrib]

theorem pairing_const_left (a : ℂ) (z : Samples p) :
    pairing (fun _ => a) z = a * star (∑ j, z j) := by
  simp [pairing, Finset.mul_sum, star_sum]

theorem pairing_scale_left (a : ℂ) (x z : Samples p) :
    pairing (fun j => a * x j) z = a * pairing x z := by
  simp [pairing, Finset.mul_sum, mul_assoc]

theorem energy_nonneg (z : Samples p) : 0 ≤ energy z :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

theorem energy_add (z w : Samples p) :
    energy (fun j => z j + w j) = energy z + energy w + 2 * (pairing z w).re := by
  simp only [energy, pairing, Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Complex.normSq_apply, Complex.mul_re]
  ring

theorem energy_pythagorean (z w : Samples p) (h : pairing z w = 0) :
    energy (fun j => z j + w j) = energy z + energy w := by
  rw [energy_add, h]
  simp

omit [NeZero p] in
theorem evenPart_even (z : Samples p) : Even (evenPart z) := by
  intro j
  simp only [evenPart, neg_neg]
  ring

omit [NeZero p] in
theorem oddPart_odd (z : Samples p) : Odd (oddPart z) := by
  intro j
  simp only [oddPart, neg_neg]
  ring

omit [NeZero p] in
theorem even_add_odd (z : Samples p) : (fun j => evenPart z j + oddPart z j) = z := by
  funext j
  simp only [evenPart, oddPart]
  ring

theorem sum_evenPart (z : Samples p) : (∑ j, evenPart z j) = ∑ j, z j := by
  change (∑ j, (z j + z (-j)) / 2) = ∑ j, z j
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_neg]
  ring

theorem odd_sum_zero {z : Samples p} (hz : Odd z) : (∑ j, z j) = 0 := by
  change ∀ j, z (-j) = -z j at hz
  have h := sum_neg z
  simp only [hz, Finset.sum_neg_distrib] at h
  linear_combination -h / 2

omit [NeZero p] in
theorem odd_zero {z : Samples p} (hz : Odd z) : z 0 = 0 := by
  have h := hz 0
  simp only [neg_zero] at h
  linear_combination h / 2

theorem even_odd_orthogonal {z w : Samples p} (hz : Even z) (hw : Odd w) :
    pairing z w = 0 := by
  change ∀ j, z (-j) = z j at hz
  change ∀ j, w (-j) = -w j at hw
  have h := sum_neg (fun j => z j * star (w j))
  simp only [hz, hw, star_neg, mul_neg, Finset.sum_neg_distrib] at h
  change -pairing z w = pairing z w at h
  linear_combination -h / 2

theorem pairing_conj_symm (z w : Samples p) : star (pairing z w) = pairing w z := by
  simp [pairing, star_sum, mul_comm]

theorem odd_even_orthogonal {z w : Samples p} (hz : Odd z) (hw : Even w) :
    pairing z w = 0 := by
  rw [← pairing_conj_symm, even_odd_orthogonal hw hz, star_zero]

theorem energy_even_add_odd (z : Samples p) :
    energy z = energy (evenPart z) + energy (oddPart z) := by
  rw [← energy_pythagorean _ _ (even_odd_orthogonal (evenPart_even z) (oddPart_odd z)),
    even_add_odd]

theorem p_cast_ne_zero : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p

omit [NeZero p] in
theorem p_sub_one_ne_zero (hp : 2 ≤ p) : (p : ℂ) - 1 ≠ 0 := by
  have : (1 : ℂ) ≠ (p : ℂ) := by exact_mod_cast (show 1 ≠ p by omega)
  exact sub_ne_zero.mpr this.symm

omit [NeZero p] in
theorem principal_even : Even (principal p) := by
  intro j
  simp [principal]

theorem sum_principal (hp : 2 ≤ p) : (∑ j, principal p j) = 0 := by
  classical
  have hcard : ((Finset.univ.erase 0 : Finset (ZMod p)).card : ℂ) = (p : ℂ) - 1 := by
    simp [Finset.card_erase_of_mem, ZMod.card, Nat.cast_sub (show 1 ≤ p by omega)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
  have he : (∑ j ∈ (Finset.univ.erase 0 : Finset (ZMod p)), principal p j) =
      ((p : ℂ) - 1) * (-1 / ((p : ℂ) - 1)) := by
    calc
      _ = ∑ _j ∈ (Finset.univ.erase 0 : Finset (ZMod p)), -1 / ((p : ℂ) - 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [principal, (Finset.mem_erase.mp hj).1]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [he]
  simp only [principal, ↓reduceIte]
  field_simp [p_sub_one_ne_zero hp]
  ring

theorem evenProjection_zero (z : Samples p) : evenProjection z 0 = 0 := by
  simp only [evenProjection, evenPart, principal, neg_zero, ↓reduceIte]
  ring

theorem evenProjection_even (z : Samples p) : Even (evenProjection z) := by
  intro j
  simp only [evenProjection, evenPart_even z j, principal_even j]

theorem sum_evenProjection (hp : 2 ≤ p) (z : Samples p) :
    (∑ j, evenProjection z j) = 0 := by
  change (∑ j, (evenPart z j - mean z - principal p j * (z 0 - mean z))) = 0
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_evenPart, ← Finset.sum_mul,
    sum_principal hp]
  simp only [zero_mul, sub_zero, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mean]
  field_simp [p_cast_ne_zero (p := p)]
  ring

theorem evenProjection_mem (hp : 2 ≤ p) (z : Samples p) : EvenTarget (evenProjection z) :=
  ⟨evenProjection_even z, sum_evenProjection hp z, evenProjection_zero z⟩

theorem evenProjection_fixed {z : Samples p} (hz : EvenTarget z) :
    evenProjection z = z := by
  funext j
  rcases hz with ⟨he, hs, hz⟩
  change ∀ j, z (-j) = z j at he
  simp only [evenProjection, evenPart, he, mean, hs, zero_div, hz, sub_zero,
    mul_zero]
  ring

omit [NeZero p] in
theorem oddProjection_fixed {z : Samples p} (hz : Odd z) : oddProjection z = z := by
  funext j
  change ∀ j, z (-j) = -z j at hz
  simp only [oddProjection, oddPart, hz]
  ring

theorem evenProjection_idempotent (hp : 2 ≤ p) (z : Samples p) :
    evenProjection (evenProjection z) = evenProjection z :=
  evenProjection_fixed (evenProjection_mem hp z)

omit [NeZero p] in
theorem oddProjection_idempotent (z : Samples p) :
    oddProjection (oddProjection z) = oddProjection z :=
  oddProjection_fixed (oddPart_odd z)

theorem principal_pairing_zero {z : Samples p}
    (hs : (∑ j, z j) = 0) (hz : z 0 = 0) : pairing (principal p) z = 0 := by
  classical
  have he : (∑ j ∈ (Finset.univ.erase 0 : Finset (ZMod p)), z j) = 0 := by
    have hh := Finset.sum_erase_add Finset.univ z (Finset.mem_univ (0 : ZMod p))
    rw [hz, hs, add_zero] at hh
    exact hh
  unfold pairing
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
  simp only [hz, star_zero, mul_zero, add_zero]
  calc
    _ = ∑ j ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
        (-1 / ((p : ℂ) - 1)) * star (z j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [principal, (Finset.mem_erase.mp hj).1]
    _ = (-1 / ((p : ℂ) - 1)) * star (∑ j ∈ (Finset.univ.erase 0 : Finset (ZMod p)), z j) := by
      rw [star_sum, Finset.mul_sum]
    _ = 0 := by rw [he, star_zero, mul_zero]

theorem evenProjection_orthogonal (z : Samples p) {w : Samples p} (hw : EvenTarget w) :
    pairing (fun j => z j - evenProjection z j) w = 0 := by
  have hdecomp : (fun j => z j - evenProjection z j) =
      (fun j => oddPart z j + mean z + (z 0 - mean z) * principal p j) := by
    funext j
    simp only [evenProjection, evenPart, oddPart]
    ring
  rw [hdecomp, pairing_add_left, pairing_add_left,
    odd_even_orthogonal (oddPart_odd z) hw.1, pairing_const_left,
    pairing_scale_left, principal_pairing_zero hw.2.1 hw.2.2, hw.2.1]
  simp

theorem oddProjection_orthogonal (z : Samples p) {w : Samples p} (hw : Odd w) :
    pairing (fun j => z j - oddProjection z j) w = 0 := by
  have hdecomp : (fun j => z j - oddProjection z j) = evenPart z := by
    funext j
    simp only [oddProjection, oddPart, evenPart]
    ring
  rw [hdecomp]
  exact even_odd_orthogonal (evenPart_even z) hw

theorem evenProjection_pythagorean (hp : 2 ≤ p) (z : Samples p) :
    energy z = energy (fun j => z j - evenProjection z j) + energy (evenProjection z) := by
  have h := energy_pythagorean _ _ (evenProjection_orthogonal z (evenProjection_mem hp z))
  simpa using h

theorem oddProjection_pythagorean (z : Samples p) :
    energy z = energy (fun j => z j - oddProjection z j) + energy (oddProjection z) := by
  have h := energy_pythagorean _ _ (oddProjection_orthogonal z (oddPart_odd z))
  simpa [oddProjection] using h

theorem evenProjection_contracts (hp : 2 ≤ p) (z : Samples p) :
    energy (evenProjection z) ≤ energy z := by
  rw [evenProjection_pythagorean hp z]
  exact le_add_of_nonneg_left (energy_nonneg _)

theorem oddProjection_contracts (z : Samples p) : energy (oddProjection z) ≤ energy z := by
  rw [oddProjection_pythagorean z]
  exact le_add_of_nonneg_left (energy_nonneg _)

theorem energy_reflect (z : Samples p) : energy (fun j => z (-j)) = energy z := by
  exact Fintype.sum_bijective (fun j : ZMod p => -j) neg_involutive.bijective _ _
    (fun _ => rfl)

theorem energy_evenPart (z : Samples p) :
    energy (evenPart z) = (energy z + (pairing z (fun j => z (-j))).re) / 2 := by
  have hpoint (a b : ℂ) : 4 * Complex.normSq ((a + b) / 2) =
      Complex.normSq a + Complex.normSq b + 2 * (a * star b).re := by
    simp [Complex.normSq_apply]
    ring
  have h := congrArg (fun f : ZMod p → ℝ => ∑ j, f j)
    (funext (fun j => hpoint (z j) (z (-j))))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  change 4 * energy (evenPart z) = energy z + energy (fun j => z (-j)) +
    2 * (∑ j, (z j * star (z (-j))).re) at h
  rw [energy_reflect] at h
  have hp : (pairing z (fun j => z (-j))).re = ∑ j, (z j * star (z (-j))).re := by
    simp [pairing, Complex.re_sum]
  rw [← hp] at h
  linarith

theorem energy_oddPart (z : Samples p) :
    energy (oddPart z) = (energy z - (pairing z (fun j => z (-j))).re) / 2 := by
  have h := energy_even_add_odd z
  rw [energy_evenPart] at h
  linarith

theorem energy_principal (hp : 2 ≤ p) (w : ℂ) :
    energy (fun j : ZMod p => principal p j * w) =
      (p : ℝ) / ((p : ℝ) - 1) * Complex.normSq w := by
  classical
  have hd : (p : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hcard : ((Finset.univ.erase 0 : Finset (ZMod p)).card : ℝ) = (p : ℝ) - 1 := by
    simp [Finset.card_erase_of_mem, ZMod.card, Nat.cast_sub (show 1 ≤ p by omega)]
  have hnorm : Complex.normSq (-1 / ((p : ℂ) - 1) * w) =
      Complex.normSq w / ((p : ℝ) - 1) ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_div]
    have he : ((p : ℂ) - 1) = (((p : ℝ) - 1 : ℝ) : ℂ) := by simp
    rw [he, Complex.normSq_ofReal]
    norm_num
    field_simp
  unfold energy
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
  have he : (∑ j ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
      Complex.normSq (principal p j * w)) =
      ((p : ℝ) - 1) * (Complex.normSq w / ((p : ℝ) - 1) ^ 2) := by
    calc
      _ = ∑ _j ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
          Complex.normSq w / ((p : ℝ) - 1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [principal, if_neg (Finset.mem_erase.mp hj).1, hnorm]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [he]
  simp only [principal, ↓reduceIte, one_mul]
  field_simp
  ring

theorem zero_mean_even_decomposition (hp : 2 ≤ p) (z : Samples p)
    (hs : (∑ j, z j) = 0) :
    energy (evenPart z) = energy (evenProjection z) +
      (p : ℝ) / ((p : ℝ) - 1) * Complex.normSq (z 0) := by
  have hform : evenPart z = fun j => evenProjection z j + principal p j * z 0 := by
    funext j
    simp [evenProjection, mean, hs]
  have horth : pairing (fun j => principal p j * z 0) (evenProjection z) = 0 := by
    have hf : (fun j => principal p j * z 0) = fun j => z 0 * principal p j := by
      funext j; ring
    rw [hf, pairing_scale_left, principal_pairing_zero (sum_evenProjection hp z)
      (evenProjection_zero z), mul_zero]
  have horth' : pairing (evenProjection z) (fun j => principal p j * z 0) = 0 := by
    rw [← pairing_conj_symm, horth, star_zero]
  rw [hform, energy_pythagorean _ _ horth', energy_principal hp]

/-- The exact unnormalized even nonprincipal arithmetic quadratic. -/
def evenMoment (z : Samples p) : ℝ :=
  ((p : ℝ) - 1) / (2 * p) * (energy z + (pairing z (fun j => z (-j))).re)
    - Complex.normSq (z 0)
/-- The odd quadratic; the principal character is even. -/
def oddMoment (z : Samples p) : ℝ :=
  ((p : ℝ) - 1) / (2 * p) * (energy z - (pairing z (fun j => z (-j))).re)

theorem evenMoment_eq_projected_energy (hp : 2 ≤ p) (z : Samples p)
    (hs : (∑ j, z j) = 0) :
    evenMoment z = ((p : ℝ) - 1) / p * energy (evenProjection z) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hd : (p : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h := zero_mean_even_decomposition hp z hs
  rw [energy_evenPart] at h
  unfold evenMoment
  field_simp at h ⊢
  nlinarith

theorem oddMoment_eq_projected_energy (z : Samples p) :
    oddMoment z = ((p : ℝ) - 1) / p * energy (oddProjection z) := by
  unfold oddProjection
  rw [energy_oddPart]
  unfold oddMoment
  ring

/-- `false` is even, `true` is odd. -/
def project (odd : Bool) (z : Samples p) : Samples p :=
  if odd then oddProjection z else evenProjection z

def moment (odd : Bool) (z : Samples p) : ℝ :=
  if odd then oddMoment z else evenMoment z

theorem project_contracts (hp : 2 ≤ p) (odd : Bool) (z : Samples p) :
    energy (project odd z) ≤ energy z := by
  cases odd
  · exact evenProjection_contracts hp z
  · exact oddProjection_contracts z

theorem project_idempotent (hp : 2 ≤ p) (odd : Bool) (z : Samples p) :
    project odd (project odd z) = project odd z := by
  cases odd
  · exact evenProjection_idempotent hp z
  · exact oddProjection_idempotent z

theorem moment_eq_projected_energy (hp : 2 ≤ p) (odd : Bool) (z : Samples p)
    (hs : (∑ j, z j) = 0) :
    moment odd z = ((p : ℝ) - 1) / p * energy (project odd z) := by
  cases odd
  · exact evenMoment_eq_projected_energy hp z hs
  · exact oddMoment_eq_projected_energy z

theorem mean_add (z w : Samples p) :
    mean (fun j => z j + w j) = mean z + mean w := by
  unfold mean
  rw [Finset.sum_add_distrib]
  ring

theorem mean_scale (a : ℂ) (z : Samples p) :
    mean (fun j => a * z j) = a * mean z := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

theorem project_add (odd : Bool) (z w : Samples p) :
    project odd (fun j => z j + w j) = fun j => project odd z j + project odd w j := by
  cases odd <;> funext j
  · simp only [project, Bool.false_eq_true, ↓reduceIte, evenProjection, mean_add, evenPart]
    ring
  · simp only [project, ↓reduceIte, oddProjection, oddPart]
    ring

theorem project_scale (odd : Bool) (a : ℂ) (z : Samples p) :
    project odd (fun j => a * z j) = fun j => a * project odd z j := by
  cases odd <;> funext j
  · simp only [project, Bool.false_eq_true, ↓reduceIte, evenProjection, mean_scale, evenPart]
    ring
  · simp only [project, ↓reduceIte, oddProjection, oddPart]
    ring

def projectLinear (odd : Bool) : Samples p →ₗ[ℂ] Samples p where
  toFun := project odd
  map_add' z w := project_add odd z w
  map_smul' a z := project_scale odd a z

theorem project_zero (odd : Bool) : project odd (0 : Samples p) = 0 :=
  (projectLinear odd).map_zero

theorem project_error_decomposition (odd : Bool) (F A : Samples p) :
    project odd F = fun j => project odd (fun j => F j - A j) j + project odd A j := by
  rw [← project_add]
  congr 1
  funext j
  ring

/-- Exact cross-plus-square identity. The approximation A is arbitrary. -/
theorem projected_error_identity (odd : Bool) (F A : Samples p) :
    energy (project odd F) = energy (project odd (fun j => F j - A j)) +
      energy (project odd A) +
      2 * (pairing (project odd (fun j => F j - A j)) (project odd A)).re := by
  rw [project_error_decomposition odd F A, energy_add]

theorem energy_eq_norm_sq (z : Samples p) :
    energy z = ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (ZMod p))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [energy, Complex.normSq_eq_norm_sq]

theorem sqrt_energy_eq_norm (z : Samples p) :
    Real.sqrt (energy z) = ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (ZMod p))‖ := by
  rw [energy_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem sqrt_energy_triangle (z w : Samples p) :
    Real.sqrt (energy (fun j => z j + w j)) ≤
      Real.sqrt (energy z) + Real.sqrt (energy w) := by
  simp only [sqrt_energy_eq_norm]
  exact norm_add_le (WithLp.toLp 2 z : EuclideanSpace ℂ (ZMod p)) (WithLp.toLp 2 w)

/-- The Hilbert-space triangle inequality for the actual projected local error. -/
theorem projected_error_triangle (odd : Bool) (F A : Samples p) :
    Real.sqrt (energy (project odd F)) ≤
      Real.sqrt (energy (project odd (fun j => F j - A j))) +
      Real.sqrt (energy (project odd A)) := by
  rw [project_error_decomposition odd F A]
  exact sqrt_energy_triangle _ _

def polarEnergy (odd : Bool) (A : Samples p) : ℝ :=
  ((p : ℝ) - 1) / p * energy (project odd A)

def nonpolarRemainder (odd : Bool) (F A : Samples p) (diagonal : ℝ) : ℝ :=
  ((p : ℝ) - 1) / p * (energy (project odd (fun j => F j - A j)) +
      2 * (pairing (project odd (fun j => F j - A j)) (project odd A)).re)
    - ((p : ℝ) - 1) / 2 * diagonal

theorem polarEnergy_nonneg (hp : 2 ≤ p) (odd : Bool) (A : Samples p) :
    0 ≤ polarEnergy odd A := by
  unfold polarEnergy
  apply mul_nonneg
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_nonneg (by linarith) (Nat.cast_nonneg p)
  · exact energy_nonneg _

theorem polarEnergy_le (hp : 2 ≤ p) (odd : Bool) (A : Samples p) :
    polarEnergy odd A ≤ ((p : ℝ) - 1) * (energy A / p) := by
  have hc : 0 ≤ ((p : ℝ) - 1) / p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_nonneg (by linarith) (Nat.cast_nonneg p)
  unfold polarEnergy
  calc
    _ ≤ ((p : ℝ) - 1) / p * energy A := mul_le_mul_of_nonneg_left (project_contracts hp odd A) hc
    _ = _ := by ring

/-- Retains the original finite arithmetic normalization and actual diagonal.
There is no estimate premise on the nonpolar remainder. -/
theorem actual_moment_local_error_identity (hp : 2 ≤ p) (odd : Bool)
    (F A : Samples p) (hs : (∑ j, F j) = 0) (diagonal : ℝ) :
    moment odd F = nonpolarRemainder odd F A diagonal +
      ((p : ℝ) - 1) / 2 * diagonal + polarEnergy odd A := by
  rw [moment_eq_projected_energy hp odd F hs, projected_error_identity odd F A]
  unfold nonpolarRemainder polarEnergy
  ring

theorem pairing_sub_right (x y z : Samples p) :
    pairing x (fun j => y j - z j) = pairing x y - pairing x z := by
  simp [pairing, mul_sub, Finset.sum_sub_distrib]

theorem project_residual_orthogonal (hp : 2 ≤ p) (odd : Bool) (z w : Samples p) :
    pairing (fun j => z j - project odd z j) (project odd w) = 0 := by
  cases odd
  · exact evenProjection_orthogonal z (evenProjection_mem hp w)
  · exact oddProjection_orthogonal z (oddPart_odd w)

/-- Hermitian self-adjointness, together with `project_idempotent`, verifies these are
actual orthogonal projections on the whole sample space. -/
theorem project_selfadjoint (hp : 2 ≤ p) (odd : Bool) (z w : Samples p) :
    pairing (project odd z) w = pairing z (project odd w) := by
  have h1 := project_residual_orthogonal hp odd z w
  have h2 := project_residual_orthogonal hp odd w z
  rw [pairing_sub_left] at h1 h2
  have h3 := congrArg star h2
  simp only [star_sub, pairing_conj_symm, star_zero] at h3
  linear_combination h3 - h1

theorem mean_constant (c : ℂ) : mean (fun _ : ZMod p => c) = c := by
  simp only [mean, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp [p_cast_ne_zero (p := p)]

theorem project_constant (odd : Bool) (c : ℂ) :
    project odd (fun _ : ZMod p => c) = 0 := by
  cases odd <;> funext j
  · simp [project, evenProjection, mean_constant, evenPart]
  · simp [project, oddProjection, oddPart]

theorem project_principal (hp : 2 ≤ p) (odd : Bool) :
    project odd (principal p) = 0 := by
  have hm : mean (principal p) = 0 := by rw [mean, sum_principal hp, zero_div]
  cases odd <;> funext j
  · simp [project, evenProjection, evenPart, hm, principal]
  · simp only [project, ↓reduceIte, oddProjection, oddPart, principal_even j, sub_self,
      zero_div, Pi.zero_apply]

theorem project_principal_scale (hp : 2 ≤ p) (odd : Bool) (c : ℂ) :
    project odd (fun j : ZMod p => c * principal p j) = 0 := by
  rw [project_scale, project_principal hp odd]
  funext j
  simp

theorem oddProjection_p_two (z : Samples 2) : oddProjection z = 0 := by
  funext j
  have hneg : -j = j := by fin_cases j <;> decide
  simp [oddProjection, oddPart, hneg]

theorem evenProjection_p_two (z : Samples 2) : evenProjection z = 0 := by
  have he := evenProjection_mem (by omega : 2 ≤ 2) z
  have hs := he.2.1
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu] at hs
  norm_num [evenProjection_zero] at hs
  funext j
  fin_cases j
  · exact he.2.2
  · exact hs

theorem project_p_two (odd : Bool) (z : Samples 2) : project odd z = 0 := by
  cases odd
  · exact evenProjection_p_two z
  · exact oddProjection_p_two z


theorem evenProjection_of_odd {z : Samples p} (hz : Odd z) : evenProjection z = 0 := by
  have hs := odd_sum_zero hz
  have h0 := odd_zero hz
  change ∀ j, z (-j) = -z j at hz
  funext j
  simp [evenProjection, evenPart, hz, mean, hs, h0]

omit [NeZero p] in
theorem oddProjection_of_even {z : Samples p} (hz : Even z) : oddProjection z = 0 := by
  change ∀ j, z (-j) = z j at hz
  funext j
  simp [oddProjection, oddPart, hz]

end
end ZhangLS.Spec.ActualSampleProjection
