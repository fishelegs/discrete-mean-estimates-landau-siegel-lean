import ZhangLS.Spec.Lemma44ReflectedTailContour

/-! # Exact short, middle, and tail decomposition of the reflected series -/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma44_reflected_series_decomposition {D N : ℕ} [NeZero N]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (hL : 3 ≤ lemma23PaperL D) {z : ℂ} (hz : z.re = 3 / 2) :
    LSeries (fun n => lemma23NuArithmeticFunction χ n * ψ (n : ZMod N)) z =
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) z +
        lemma44LongDirichletSum χ ψ z +
          ∑' n : ℕ, lemma44ReflectedTailTerm χ ψ z n := by
  classical
  let c : ℕ → ℂ := fun n => lemma23NuArithmeticFunction χ n * ψ (n : ZMod N)
  let f : ℕ → ℂ := fun n => LSeries.term c z n
  let S := Finset.Icc 1 (D ^ 4)
  let M := Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊
  let short : ℕ → ℂ := fun n => if n ∈ S then f n else 0
  let middle : ℕ → ℂ := fun n => if n ∈ M then f n else 0
  have hshort : Summable short :=
    summable_of_ne_finset_zero (s := S) (by intro n hn; simp [short, hn])
  have hmiddle : Summable middle :=
    summable_of_ne_finset_zero (s := M) (by intro n hn; simp [middle, hn])
  have htail := (lemma44_reflected_tail_summable_and_bound χ ψ hz).1
  have hcut : D ^ 4 ≤ ⌊lemma23PaperP D ^ 2⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    simpa only [Nat.cast_pow] using lemma44_D4_le_P2 χ hL
  have hpoint (n : ℕ) : f n = short n + middle n + lemma44ReflectedTailTerm χ ψ z n := by
    by_cases hn : n = 0
    · subst n
      simp [f, short, middle, S, M, lemma44ReflectedTailTerm]
    dsimp [short, middle, S, M, lemma44ReflectedTailTerm]
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    by_cases hns : n ≤ D ^ 4
    · simp [hns, Nat.one_le_iff_ne_zero.mpr hn,
        not_lt.mpr hns, not_lt.mpr (hns.trans hcut), f, c]
    · have hnD : D ^ 4 < n := Nat.lt_of_not_ge hns
      by_cases hnM : n ≤ ⌊lemma23PaperP D ^ 2⌋₊
      · simp [hns, hnD, hnM, not_lt.mpr hnM]
      · simp [hns, hnD, hnM, Nat.lt_of_not_ge hnM, f, c]
  have hshortsum : (∑' n : ℕ, short n) =
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) z := by
    rw [tsum_eq_sum (s := S) (by intro n hn; simp [short, hn])]
    unfold lemma23ActualSectionFourF lemma23SectionFourF lemma23FiniteDirichletPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    simp only [short, if_pos hn, f, c]
    rw [lemma44_LSeries_term_eq_exp _ _ (Nat.ne_of_gt
      (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hn).1))]
  have hmiddlesum : (∑' n : ℕ, middle n) = lemma44LongDirichletSum χ ψ z := by
    rw [tsum_eq_sum (s := M) (by intro n hn; simp [middle, hn])]
    unfold lemma44LongDirichletSum
    apply Finset.sum_congr rfl
    intro n hn
    simp only [middle, if_pos hn, f, c]
    rw [lemma44_LSeries_term_eq_exp _ _ (Nat.ne_of_gt
      (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1))]
  change (∑' n : ℕ, f n) = _
  simp_rw [hpoint]
  rw [(hshort.add hmiddle).tsum_add htail, hshort.tsum_add hmiddle,
    hshortsum, hmiddlesum]

end ZhangLS.Spec
