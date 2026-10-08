import RightRemainderBridge

noncomputable section

namespace PiWeightedColon

open Polynomial

def stairWeight (s a : ℕ) : ℕ := s + 4 * (a / 2)

def StairBound (M : ℕ) (f : Plane) : Prop :=
  ∀ s a, M < stairWeight s a → coeff f s a = 0

def QuotBound (M : ℕ) (h : Plane) : Prop :=
  ∀ s a, M < stairWeight s a + 4 → coeff h s a = 0

def bimono (s a : ℕ) (b : F2) : Plane := monomial s (monomial a b)

theorem stairBound_zero (M : ℕ) : StairBound M 0 := by intro s a _; simp [coeff]

theorem quotBound_zero (M : ℕ) : QuotBound M 0 := by intro s a _; simp [coeff]

theorem stairBound_add {M : ℕ} {f g : Plane}
    (hf : StairBound M f) (hg : StairBound M g) : StairBound M (f + g) := by
  intro s a hsa
  simp only [coeff, Polynomial.coeff_add]
  change coeff f s a + coeff g s a = 0
  rw [hf s a hsa, hg s a hsa, zero_add]

theorem quotBound_add {M : ℕ} {f g : Plane}
    (hf : QuotBound M f) (hg : QuotBound M g) : QuotBound M (f + g) := by
  intro s a hsa
  simp only [coeff, Polynomial.coeff_add]
  change coeff f s a + coeff g s a = 0
  rw [hf s a hsa, hg s a hsa, zero_add]

theorem stairBound_bimono {M s a : ℕ} (b : F2) (hw : stairWeight s a ≤ M) :
    StairBound M (bimono s a b) := by
  intro k c hkc
  by_cases hs : s = k
  · subst k
    have ha : a ≠ c := by intro he; subst c; omega
    simp [coeff, bimono, Polynomial.coeff_monomial, ha]
  · simp [coeff, bimono, Polynomial.coeff_monomial, hs]

theorem quotBound_bimono {M s a : ℕ} (b : F2) (hw : stairWeight s a + 4 ≤ M) :
    QuotBound M (bimono s a b) := by
  intro k c hkc
  by_cases hs : s = k
  · subst k
    have ha : a ≠ c := by intro he; subst c; omega
    simp [coeff, bimono, Polynomial.coeff_monomial, ha]
  · simp [coeff, bimono, Polynomial.coeff_monomial, hs]

theorem bimono_Q_identity (s a : ℕ) (b : F2) :
    bimono s (a + 2) b = globalQ * bimono s a b +
      bimono (s + 4) a b + bimono (s + 2) a b := by
  have he : globalQ * bimono s a b =
      bimono (s + 4) a b + bimono (s + 2) a b + bimono s (a + 2) b := by
    rw [globalQ_expanded]
    simp only [bimono, add_mul, X_pow_eq_monomial,
      monomial_mul_monomial, one_mul, C_mul_monomial]
    simp only [Nat.add_comm]
  rw [he]
  have hc : ∀ p q r : Plane, p + q + r + p + q = r := by
    intro p q r
    calc
      _ = (p + p) + (q + q) + r := by ring
      _ = r := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add, zero_add]
  exact (hc _ _ _).symm

theorem linearRemainder_add (A B D E : Line) :
    linearRemainder (A + D) (B + E) = linearRemainder A B + linearRemainder D E := by
  simp only [linearRemainder, map_add, mul_add]
  ring

theorem lineEmbedding_monomial (s : ℕ) (b : F2) :
    lineEmbedding (monomial s b) = bimono s 0 b := by
  simp [lineEmbedding, bimono, map_monomial, monomial_zero_left]

theorem y_lineEmbedding_monomial (s : ℕ) (b : F2) :
    C X * lineEmbedding (monomial s b) = bimono s 1 b := by
  rw [lineEmbedding_monomial]
  simp only [bimono, C_mul_monomial, monomial_zero_left]
  have he : (C b * X : Line) = monomial 1 b := by
    simpa only [pow_one] using (C_mul_X_pow_eq_monomial (a := b) (n := 1))
  rw [mul_comm (X : Line) (C b), he]

def DivisionBound (M : ℕ) (f : Plane) : Prop :=
  ∃ h : Plane, ∃ A B : Line,
    f = globalQ * h + linearRemainder A B ∧ QuotBound M h ∧
      A.natDegree ≤ M ∧ B.natDegree ≤ M

theorem divisionBound_zero (M : ℕ) : DivisionBound M 0 := by
  refine ⟨0, 0, 0, ?_, quotBound_zero M, ?_, ?_⟩ <;> simp [linearRemainder]

theorem divisionBound_add {M : ℕ} {f g : Plane}
    (hf : DivisionBound M f) (hg : DivisionBound M g) : DivisionBound M (f + g) := by
  obtain ⟨h, A, B, he, hq, ha, hb⟩ := hf
  obtain ⟨j, D, E, je, jq, jd, je'⟩ := hg
  refine ⟨h + j, A + D, B + E, ?_, quotBound_add hq jq,
    (natDegree_add_le _ _).trans (max_le ha jd),
    (natDegree_add_le _ _).trans (max_le hb je')⟩
  rw [he, je, linearRemainder_add]
  ring

/-- Recursive reduction of an actual monomial, keeping its coefficient.
The quotient loses four units of staircase weight. -/
theorem divisionBound_bimono (M : ℕ) : ∀ a s, ∀ b : F2,
    stairWeight s a ≤ M → DivisionBound M (bimono s a b) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro s b hw
    by_cases h0 : a = 0
    · subst a
      refine ⟨0, monomial s b, 0, ?_, quotBound_zero M, ?_, by simp⟩
      · simp only [mul_zero, linearRemainder, map_zero, mul_zero, add_zero, zero_add]
        exact (lineEmbedding_monomial s b).symm
      · exact (natDegree_monomial_le b).trans (by simpa [stairWeight] using hw)
    by_cases h1 : a = 1
    · subst a
      refine ⟨0, 0, monomial s b, ?_, quotBound_zero M, by simp, ?_⟩
      · simp only [mul_zero, linearRemainder, map_zero, zero_add]
        exact (y_lineEmbedding_monomial s b).symm
      · exact (natDegree_monomial_le b).trans (by simpa [stairWeight] using hw)
    have ha : a - 2 < a := by omega
    have haw : (a - 2) / 2 + 1 = a / 2 := by omega
    obtain ⟨h, A, B, he, hq, hA, hB⟩ := ih (a - 2) ha (s + 4) b
      (by simp only [stairWeight] at hw ⊢; omega)
    obtain ⟨j, D, E, je, jq, jD, jE⟩ := ih (a - 2) ha (s + 2) b
      (by simp only [stairWeight] at hw ⊢; omega)
    refine ⟨bimono s (a - 2) b + h + j, A + D, B + E, ?_,
      quotBound_add (quotBound_add (quotBound_bimono b
        (by simp only [stairWeight] at hw ⊢; omega)) hq) jq,
      (natDegree_add_le _ _).trans (max_le hA jD),
      (natDegree_add_le _ _).trans (max_le hB jE)⟩
    have hi := bimono_Q_identity s (a - 2) b
    rw [show a - 2 + 2 = a by omega, he, je] at hi
    rw [hi, linearRemainder_add]
    ring

theorem divisionBound_sum {ι : Type*} (M : ℕ) (S : Finset ι) (f : ι → Plane)
    (hf : ∀ i ∈ S, DivisionBound M (f i)) : DivisionBound M (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using divisionBound_zero M
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact divisionBound_add (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem staircase_division (M : ℕ) (f : Plane) (hf : StairBound M f) : DivisionBound M f := by
  rw [← sum_monomial_eq f, sum_def]
  apply divisionBound_sum
  intro s _
  rw [← sum_monomial_eq (f.coeff s), sum_def, map_sum]
  apply divisionBound_sum
  intro a ha
  apply divisionBound_bimono
  by_contra hw
  exact mem_support_iff.mp ha (hf s a (by omega))

theorem quotBound_scale_zero (h : Plane) (hh : QuotBound 1 h) : h = 0 := by
  ext s a
  exact hh s a (by simp only [stairWeight]; omega)

theorem quotBound_scale_succ (N : ℕ) (h : Plane) (hh : QuotBound (4 * (N + 1) + 1) h) :
    StairBound (4 * N + 1) h := by
  intro s a hsa
  exact hh s a (by omega)

end PiWeightedColon
