import StaircaseNonvanishing
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace PiWeightedColon

open Polynomial

abbrev BlockIndex (N d p q : ℕ) := Σ j : Fin (N + 1), Fin d × Fin (p * (N - j.val) + q)

def BlockLabel (N d p q : ℕ) :=
  {ck : ℕ × ℕ // ck.1 < d * (N + 1) ∧ ck.2 < p * (N - ck.1 / d) + q}

theorem block_div (d j r : ℕ) (hd : 0 < d) (hr : r < d) : (d * j + r) / d = j := by
  rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hr, add_zero]

def blockEncode (N d p q : ℕ) (hd : 0 < d) (i : BlockIndex N d p q) : BlockLabel N d p q :=
  ⟨(d * i.1.val + i.2.1.val, i.2.2.val), by
    constructor
    · calc
        _ < d * i.1.val + d := Nat.add_lt_add_left i.2.1.isLt _
        _ = d * (i.1.val + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left d i.1.isLt
    · rw [block_div d i.1.val i.2.1.val hd i.2.1.isLt]
      exact i.2.2.isLt⟩

def blockDecode (N d p q : ℕ) (hd : 0 < d) (i : BlockLabel N d p q) : BlockIndex N d p q :=
  ⟨⟨i.val.1 / d, (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using i.property.1)⟩,
    ⟨⟨i.val.1 % d, Nat.mod_lt _ hd⟩, ⟨i.val.2, i.property.2⟩⟩⟩

theorem blockEncode_injective (N d p q : ℕ) (hd : 0 < d) :
    Function.Injective (blockEncode N d p q hd) := by
  rintro ⟨j, r, k⟩ ⟨j', r', k'⟩ he
  have hc := congrArg (fun x : BlockLabel N d p q => x.val.1) he
  have hk := congrArg (fun x : BlockLabel N d p q => x.val.2) he
  change d * j.val + r.val = d * j'.val + r'.val at hc
  change k.val = k'.val at hk
  have hj : j = j' := Fin.ext (by
    have hh := congrArg (fun c => c / d) hc
    simpa only [block_div d _ _ hd r.isLt, block_div d _ _ hd r'.isLt] using hh)
  subst j'
  have hr : r = r' := Fin.ext (Nat.add_left_cancel hc)
  subst r'
  have hh : k = k' := Fin.ext hk
  subst k'
  rfl

theorem blockEncode_decode (N d p q : ℕ) (hd : 0 < d) (i : BlockLabel N d p q) :
    blockEncode N d p q hd (blockDecode N d p q hd i) = i := by
  apply Subtype.ext
  apply Prod.ext
  · change d * (i.val.1 / d) + i.val.1 % d = i.val.1
    simpa only [Nat.mul_comm] using Nat.div_add_mod' i.val.1 d
  · rfl

def blockEquiv (N d p q : ℕ) (hd : 0 < d) : BlockIndex N d p q ≃ BlockLabel N d p q where
  toFun := blockEncode N d p q hd
  invFun := blockDecode N d p q hd
  left_inv _ := blockEncode_injective N d p q hd (blockEncode_decode N d p q hd _)
  right_inv := blockEncode_decode N d p q hd

abbrev RowIndex (N : ℕ) := BlockIndex N 2 4 2
abbrev ColIndex (N : ℕ) := Σ e : Bool, BlockIndex N (endpointD e) 2 1

def rowS {N : ℕ} (i : RowIndex N) : ℕ := i.2.2.val
def rowA {N : ℕ} (i : RowIndex N) : ℕ := 2 * i.1.val + i.2.1.val
def colE {N : ℕ} (i : ColIndex N) : Bool := i.1
def colC {N : ℕ} (i : ColIndex N) : ℕ := endpointD i.1 * i.2.1.val + i.2.2.1.val
def colK {N : ℕ} (i : ColIndex N) : ℕ := i.2.2.2.val

theorem endpointD_pos (e : Bool) : 0 < endpointD e := by cases e <;> decide

def RowLabel (N : ℕ) := {sa : ℕ × ℕ // sa.2 ≤ 2 * N + 1 ∧ sa.1 ≤ 4 * (N - sa.2 / 2) + 1}
abbrev ColLabel (N : ℕ) := Σ e : Bool, BlockLabel N (endpointD e) 2 1

def rowLabelEquiv (N : ℕ) : RowIndex N ≃ RowLabel N :=
  (blockEquiv N 2 4 2 (by decide)).trans {
    toFun := fun i => ⟨(i.val.2, i.val.1), by have h := i.property; omega⟩
    invFun := fun i => ⟨(i.val.2, i.val.1), by have h := i.property; omega⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def colLabelEquiv (N : ℕ) : ColIndex N ≃ ColLabel N :=
  Equiv.sigmaCongrRight (fun e => blockEquiv N (endpointD e) 2 1 (endpointD_pos e))

theorem row_index_bounds {N : ℕ} (i : RowIndex N) :
    rowA i ≤ 2 * N + 1 ∧ rowS i ≤ 4 * (N - rowA i / 2) + 1 :=
  (rowLabelEquiv N i).property

theorem col_index_bounds {N : ℕ} (i : ColIndex N) :
    colC i < endpointD (colE i) * (N + 1) ∧
      colK i ≤ 2 * (N - colC i / endpointD (colE i)) := by
  have h := (blockEncode N (endpointD i.1) 2 1 (endpointD_pos i.1) i.2).property
  have hk : colK i < 2 * (N - colC i / endpointD (colE i)) + 1 := h.2
  exact ⟨h.1, by omega⟩

theorem blockIndex_card (N d p q : ℕ) :
    Fintype.card (BlockIndex N d p q) = ∑ j : Fin (N + 1), d * (p * (N - j.val) + q) := by
  simp [BlockIndex, Fintype.card_sigma, Fintype.card_prod]

theorem common_index_count (N : ℕ) :
    (∑ j : Fin (N + 1), (8 * (N - j.val) + 4)) = 4 * (N + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    change (∑ j : Fin ((N + 1) + 1), (8 * ((N + 1) - j.val) + 4)) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
    rw [ih]
    ring

theorem rowIndex_card (N : ℕ) : Fintype.card (RowIndex N) = 4 * (N + 1) ^ 2 := by
  rw [blockIndex_card N 2 4 2]
  convert common_index_count N using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem colIndex_card (N : ℕ) : Fintype.card (ColIndex N) = 4 * (N + 1) ^ 2 := by
  rw [Fintype.card_sigma, Fintype.sum_bool]
  change Fintype.card (BlockIndex N 3 2 1) + Fintype.card (BlockIndex N 1 2 1) = _
  rw [blockIndex_card N 3 2 1, blockIndex_card N 1 2 1]
  rw [← Finset.sum_add_distrib]
  convert common_index_count N using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

instance rowLabelFintype (N : ℕ) : Fintype (RowLabel N) :=
  Fintype.ofEquiv (RowIndex N) (rowLabelEquiv N)

instance colLabelFintype (N : ℕ) : Fintype (ColLabel N) :=
  Fintype.ofEquiv (ColIndex N) (colLabelEquiv N)

theorem rowLabel_card (N : ℕ) : Fintype.card (RowLabel N) = 4 * (N + 1) ^ 2 := by
  rw [← Fintype.card_congr (rowLabelEquiv N), rowIndex_card]

theorem colLabel_card (N : ℕ) : Fintype.card (ColLabel N) = 4 * (N + 1) ^ 2 := by
  rw [← Fintype.card_congr (colLabelEquiv N), colIndex_card]

def matrixIndexEquiv (N : ℕ) : RowIndex N ≃ ColIndex N :=
  Fintype.equivOfCardEq (by rw [rowIndex_card, colIndex_card])

end PiWeightedColon
