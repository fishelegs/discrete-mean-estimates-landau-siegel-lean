import ZhangLS.Spec.Lemma61ReciprocalTailKernel

/-! # Actual reciprocal tail truncation for Lemma 6.1

The original n<T^3 finite sum and its n>=T^3 tail are split exactly.
Actual Gamma conductor growth cancels with actual P4, uniformly on the
wide high rectangle. Far-left and both horizontal tail integrals, the
actual local Cauchy relation and the original-left tail error are proved.
The full Lemma61Target remains unproved: finite polynomial error-line
shift, full horizontal edges and final constants/thresholds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def lemma61ReciprocalTailTerm {p : ℕ} (D : ℕ)
    (ψ : DirichletCharacter ℂ p) (z : ℂ) (n : ℕ) : ℂ :=
  if lemma56PaperT D ^ 3 ≤ (n : ℝ) then LSeries.term (fun m => ψ (m : ZMod p)) z n else 0

lemma lemma61_reciprocal_tail_summable {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) {z : ℂ} (hz : 1 < z.re) :
    Summable (lemma61ReciprocalTailTerm D ψ z) := by
  have hb := summable_norm_iff.mpr (DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hz)
  apply summable_norm_iff.mp
  exact hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
    unfold lemma61ReciprocalTailTerm
    split_ifs <;> simp)

lemma lemma61_actual_reciprocal_series_split {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) {z : ℂ} (hz : 1 < z.re) :
    DirichletCharacter.LFunction ψ z = lemma61ShortPolynomial D ψ z +
      ∑' n : ℕ, lemma61ReciprocalTailTerm D ψ z n := by
  classical
  let c : ℕ → ℂ := fun n => ψ (n : ZMod p)
  let f : ℕ → ℂ := LSeries.term c z
  let S := (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
    (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3)
  let short : ℕ → ℂ := fun n => if n ∈ S then f n else 0
  have hshort : Summable short := summable_of_ne_finset_zero (s := S)
    (fun n hn => by simp [short,hn])
  have htail := lemma61_reciprocal_tail_summable (D := D) ψ hz
  have hmem (n : ℕ) (hn : n ≠ 0) : n ∈ S ↔ (n : ℝ) < lemma56PaperT D ^ 3 := by
    dsimp [S]
    simp only [Finset.mem_filter,Finset.mem_Icc]
    constructor
    · exact fun h => h.2
    · intro h
      have hc : n ≤ ⌈lemma56PaperT D ^ 3⌉₊ := by
        exact_mod_cast h.le.trans (Nat.le_ceil (lemma56PaperT D ^ 3))
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hn,hc⟩,h⟩
  have hp (n : ℕ) : f n = short n + lemma61ReciprocalTailTerm D ψ z n := by
    by_cases hn : n = 0
    · simp [f,short,hn,lemma61ReciprocalTailTerm]
    · by_cases hlt : (n : ℝ) < lemma56PaperT D ^ 3
      · simp [short,(hmem n hn).mpr hlt,lemma61ReciprocalTailTerm,not_le.mpr hlt,f,c]
      · simp [short,show n ∉ S from fun h => hlt ((hmem n hn).mp h),
          lemma61ReciprocalTailTerm,le_of_not_gt hlt,f,c]
  have hs : (∑' n : ℕ, short n) = lemma61ShortPolynomial D ψ z := by
    rw [tsum_eq_sum (s := S) (fun n hn => by simp [short,hn])]
    unfold lemma61ShortPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1)
    simp only [short,if_pos hn,f,c]
    exact lemma44_LSeries_term_eq_exp _ _ hn0
  rw [DirichletCharacter.LFunction_eq_LSeries ψ hz]
  change (∑' n : ℕ, f n) = _
  simp_rw [hp]
  rw [hshort.tsum_add htail,hs]

end ZhangLS.Spec
