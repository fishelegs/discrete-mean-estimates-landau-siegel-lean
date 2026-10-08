import IntegerNewtonMatrix

noncomputable section

namespace PiWeightedColon

def parityBit (e : Bool) : ℕ := if e then 1 else 0
def natFrequency (e : Bool) (k : ℕ) : ℕ := 2 * k + parityBit e

/-- The prescribed weight-2 pair profile, including its exceptional j=0 pair. -/
def pairLength (N j : ℕ) : ℕ := if j = 0 then N + 1 else N - (j - 1) / 2

def frequencyLength (N h : ℕ) : ℕ :=
  (if h % 2 = 0 then 1 else 3) * pairLength N (h / 2)

theorem frequencyLength_pair (N k : ℕ) (e : Bool) :
    frequencyLength N (natFrequency e k) = endpointD e * pairLength N k := by
  have hd : natFrequency e k / 2 = k := by cases e <;> dsimp [natFrequency, parityBit] <;> omega
  have hm : natFrequency e k % 2 = parityBit e := by
    cases e <;> dsimp [natFrequency, parityBit] <;> omega
  rw [frequencyLength, hd, hm]
  cases e <;> rfl

/-- Exactly the allowed same-parity frequency nodes form a prefix. -/
theorem pair_prefix_iff (N k c : ℕ) (e : Bool) :
    k ≤ 2 * N ∧ c < endpointD e * pairLength N k ↔
      c < endpointD e * (N + 1) ∧ k ≤ 2 * (N - c / endpointD e) := by
  cases e <;> simp only [endpointD, Bool.false_eq_true, ↓reduceIte, Nat.one_mul, Nat.div_one]
  all_goals
    by_cases hk : k = 0
    · subst k
      simp [pairLength]
    · simp only [pairLength, if_neg hk]
      omega

theorem frequency_prefix_iff (N k c : ℕ) (e : Bool) :
    natFrequency e k ≤ 4 * N + 1 ∧ c < frequencyLength N (natFrequency e k) ↔
      c < endpointD e * (N + 1) ∧ k ≤ 2 * (N - c / endpointD e) := by
  rw [frequencyLength_pair]
  have hb : natFrequency e k ≤ 4 * N + 1 ↔ k ≤ 2 * N := by
    cases e <;> simp only [natFrequency, parityBit, Bool.false_eq_true, ↓reduceIte] <;> omega
  rw [hb, pair_prefix_iff]

def OriginLabel (N : ℕ) :=
  {hc : ℕ × ℕ // hc.1 ≤ 4 * N + 1 ∧ hc.2 < frequencyLength N hc.1}

def originalLabelEncode (N : ℕ) (i : ColLabel N) : OriginLabel N :=
  ⟨(natFrequency i.1 i.2.val.2, i.2.val.1),
    (frequency_prefix_iff N _ _ _).mpr ⟨i.2.property.1, Nat.le_of_lt_succ i.2.property.2⟩⟩

def frequencyParity (h : ℕ) : Bool := decide (h % 2 = 1)

theorem frequency_decode (h : ℕ) : natFrequency (frequencyParity h) (h / 2) = h := by
  by_cases hp : h % 2 = 1
  · simp only [natFrequency, parityBit, frequencyParity, hp, decide_true, ↓reduceIte]
    omega
  · simp only [natFrequency, parityBit, frequencyParity, hp, decide_false, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero]
    omega

def originalLabelDecode (N : ℕ) (i : OriginLabel N) : ColLabel N :=
  ⟨frequencyParity i.val.1, ⟨(i.val.2, i.val.1 / 2), by
    have h : i.val.2 < endpointD (frequencyParity i.val.1) * (N + 1) ∧
        i.val.1 / 2 ≤ 2 * (N - i.val.2 / endpointD (frequencyParity i.val.1)) :=
      (frequency_prefix_iff N (i.val.1 / 2) i.val.2 (frequencyParity i.val.1)).mp
        (by simpa only [frequency_decode] using i.property)
    change i.val.2 < endpointD (frequencyParity i.val.1) * (N + 1) ∧
      i.val.1 / 2 < 2 * (N - i.val.2 / endpointD (frequencyParity i.val.1)) + 1
    exact ⟨h.1, by omega⟩⟩⟩

theorem originalLabelEncode_injective (N : ℕ) : Function.Injective (originalLabelEncode N) := by
  rintro ⟨e, i⟩ ⟨e', i'⟩ he
  have hh := congrArg (fun x : OriginLabel N => x.val.1) he
  have hc := congrArg (fun x : OriginLabel N => x.val.2) he
  change natFrequency e i.val.2 = natFrequency e' i'.val.2 at hh
  change i.val.1 = i'.val.1 at hc
  have hep : e = e' := by
    cases e <;> cases e' <;> simp only [natFrequency, parityBit, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero] at hh <;> first | rfl | omega
  subst e'
  have hk : i.val.2 = i'.val.2 := by unfold natFrequency at hh; omega
  have hi : i = i' := Subtype.ext (Prod.ext hc hk)
  subst i'
  rfl

theorem originalLabelEncode_decode (N : ℕ) (i : OriginLabel N) :
    originalLabelEncode N (originalLabelDecode N i) = i := by
  apply Subtype.ext
  apply Prod.ext
  · exact frequency_decode i.val.1
  · rfl

def originalLabelEquiv (N : ℕ) : ColLabel N ≃ OriginLabel N where
  toFun := originalLabelEncode N
  invFun := originalLabelDecode N
  left_inv _ := originalLabelEncode_injective N (originalLabelEncode_decode N _)
  right_inv := originalLabelEncode_decode N

def originalIndexEquiv (N : ℕ) : ColIndex N ≃ OriginLabel N :=
  (colLabelEquiv N).trans (originalLabelEquiv N)

instance originLabelFintype (N : ℕ) : Fintype (OriginLabel N) :=
  Fintype.ofEquiv (ColIndex N) (originalIndexEquiv N)

theorem originLabel_card (N : ℕ) : Fintype.card (OriginLabel N) = 4 * (N + 1) ^ 2 := by
  rw [← Fintype.card_congr (originalIndexEquiv N), colIndex_card]

theorem originalIndexEquiv_coordinates (N : ℕ) (c : ColIndex N) :
    (originalIndexEquiv N c).val = (natFrequency (colE c) (colK c), colC c) := rfl

def originalIntegerMatrix (N : ℕ) : Matrix (RowIndex N) (OriginLabel N) ℤ :=
  fun r c => originEntry (rowS r) (rowA r) c.val.2 (c.val.1 : ℤ)

theorem originalIntegerMatrix_reindex (N : ℕ) (r : RowIndex N) (c : ColIndex N) :
    originalIntegerMatrix N r (originalIndexEquiv N c) =
      (originPolynomial (rowS r) (rowA r) (colC c)).eval (frequencyNode (colE c) (colK c)) := by
  rw [originPolynomial_eval]
  unfold originalIntegerMatrix
  rw [originalIndexEquiv_coordinates]
  change originEntry _ _ _ (natFrequency (colE c) (colK c) : ℤ) = _
  have h : (natFrequency (colE c) (colK c) : ℤ) = frequencyNode (colE c) (colK c) := by
    cases colE c <;> simp [natFrequency, parityBit, frequencyNode]
  rw [h]

/-- All earlier nodes of a block are actual columns of the same profile. -/
def columnPrefix {N : ℕ} (c : ColIndex N) (k : ℕ) (hk : k ≤ colK c) : ColIndex N :=
  ⟨c.1, ⟨c.2.1, ⟨c.2.2.1, ⟨k, Nat.lt_of_le_of_lt hk c.2.2.2.isLt⟩⟩⟩⟩

/-- Concrete factorization for every original entry. Every Newton coefficient
in this finite sum is an entry of the already verified integer Newton matrix. -/
theorem originalIntegerMatrix_block_factorization (N : ℕ) (r : RowIndex N) (c : ColIndex N) :
    originalIntegerMatrix N r (originalIndexEquiv N c) =
      ∑ k : Fin (colK c + 1),
        integerNewtonMatrix N r (columnPrefix c k.val (by have h := k.isLt; omega)) *
          newtonEvaluationFactor (colE c) k.val (colK c) := by
  rw [originalIntegerMatrix_reindex]
  have h := originEntry_newton_expansion (rowS r) (rowA r) (colC c) (colK c) (colE c)
  rw [← originPolynomial_eval] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  exact h

end PiWeightedColon
