import ZhangLS.Spec.Lemma44SmoothedTail

/-!
# The right Mellin integral is the actual short polynomial plus a small error

The full coefficient series is split into the short polynomial, the middle
Gaussian sum, and the infinite smoothed tail. All three have proved convergence
and bounds. The defining good-set hypothesis is used only for the middle sum.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma44_omega3_re_pos {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma44InOmega3 D s) : 0 < s.re := by
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have h3 : (3 : ℝ) ^ 3 ≤ lemma23PaperL D ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  have h39 : lemma23PaperL D ^ 3 ≤ lemma23PaperL D ^ 9 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have ha : lemma44PaperAlpha D ≤ 1 / 4 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    apply (div_le_iff₀ (pow_pos hL0 9)).mpr
    norm_num at h3
    nlinarith only [h3, h39, Real.pi_le_four]
  linarith only [hs.1, ha]

theorem lemma44_LSeries_term_eq_exp (c : ℕ → ℂ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term c s n = c n * exp (-s * (Real.log (n : ℝ) : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log hnp.le).symm
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC, hlog,
    div_eq_mul_inv, ← Complex.exp_neg]
  congr 2
  ring

noncomputable def lemma44FullGaussianSeries {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' n : ℕ,
    LSeries.term (fun m => lemma23NuArithmeticFunction χ m * ψ (m : ZMod N)) s n *
      (zhangGaussianWeight D (lemma44PaperGaussianScale D / n) : ℂ)

theorem lemma44_full_gaussian_series_decomposition {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    lemma44FullGaussianSeries χ ψ s =
      lemma44GaussianShortDirichletSum χ ψ s +
        lemma44GaussianLongDirichletSum χ ψ s (lemma44PaperGaussianScale D) +
          ∑' n : ℕ, lemma44GaussianTailTerm χ ψ s n := by
  classical
  let c : ℕ → ℂ := fun n => lemma23NuArithmeticFunction χ n * ψ (n : ZMod N)
  let f : ℕ → ℂ := fun n => LSeries.term c s n *
    (zhangGaussianWeight D (lemma44PaperGaussianScale D / n) : ℂ)
  let S := Finset.Icc 1 (D ^ 4)
  let M := Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊
  let short : ℕ → ℂ := fun n => if n ∈ S then f n else 0
  let middle : ℕ → ℂ := fun n => if n ∈ M then f n else 0
  have hshort : Summable short :=
    summable_of_ne_finset_zero (s := S) (by intro n hn; simp [short, hn])
  have hmiddle : Summable middle :=
    summable_of_ne_finset_zero (s := M) (by intro n hn; simp [middle, hn])
  have htail := (lemma44_gaussian_tail_summable_and_bound χ ψ hD hL hs).1
  have hcut : D ^ 4 ≤ ⌊lemma23PaperP D ^ 2⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    simpa only [Nat.cast_pow] using lemma44_D4_le_P2 χ hL
  have hpoint (n : ℕ) : f n = short n + middle n + lemma44GaussianTailTerm χ ψ s n := by
    by_cases hn : n = 0
    · subst n
      simp [f, short, middle, S, M, lemma44GaussianTailTerm]
    dsimp [short, middle, S, M, lemma44GaussianTailTerm]
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    by_cases hns : n ≤ D ^ 4
    · simp [hns, Nat.one_le_iff_ne_zero.mpr hn,
        not_lt.mpr hns, not_lt.mpr (hns.trans hcut), f, c]
    · have hnD : D ^ 4 < n := Nat.lt_of_not_ge hns
      by_cases hnM : n ≤ ⌊lemma23PaperP D ^ 2⌋₊
      · simp [hns, hnD, hnM, not_lt.mpr hnM]
      · simp [hns, hnD, hnM, Nat.lt_of_not_ge hnM, f, c]
  have hshortsum : (∑' n : ℕ, short n) = lemma44GaussianShortDirichletSum χ ψ s := by
    rw [tsum_eq_sum (s := S) (by intro n hn; simp [short, hn])]
    unfold lemma44GaussianShortDirichletSum
    apply Finset.sum_congr rfl
    intro n hn
    simp only [short, if_pos hn, f, c]
    rw [lemma44_LSeries_term_eq_exp _ _ (Nat.ne_of_gt
      (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hn).1))]
  have hmiddlesum : (∑' n : ℕ, middle n) =
      lemma44GaussianLongDirichletSum χ ψ s (lemma44PaperGaussianScale D) := by
    rw [tsum_eq_sum (s := M) (by intro n hn; simp [middle, hn])]
    unfold lemma44GaussianLongDirichletSum
    apply Finset.sum_congr rfl
    intro n hn
    simp only [middle, if_pos hn, f, c]
    rw [lemma44_LSeries_term_eq_exp _ _ (Nat.ne_of_gt
      (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1))]
  change (∑' n : ℕ, f n) = _
  simp_rw [hpoint]
  rw [(hshort.add hmiddle).tsum_add htail, hshort.tsum_add hmiddle,
    hshortsum, hmiddlesum]

/-- The actual complete smoothed series approximates `F`, on the full
paper region and with an absolute error constant. -/
theorem lemma44_full_gaussian_series_approximation {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44FullGaussianSeries χ ψ s -
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ ≤
        (1 + 5 * Real.exp (2 * Real.pi) + lemma44InverseSquareMass) *
          lemma23PaperL D ^ (-180 : ℤ) := by
  have hre := (lemma44_omega3_re_pos hL hs).le
  rw [lemma44_full_gaussian_series_decomposition χ ψ hD hL hre]
  have hshort := lemma44_short_smoothing_error χ ψ hD hL hre
  have hmiddle := lemma44_paper_gaussian_long_sum_on_omega3 χ ψ hL hψ hs
  have htail := (lemma44_gaussian_tail_summable_and_bound χ ψ hD hL hre).2
  calc
    _ = ‖(lemma44GaussianShortDirichletSum χ ψ s -
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s) +
          lemma44GaussianLongDirichletSum χ ψ s (lemma44PaperGaussianScale D) +
            ∑' n : ℕ, lemma44GaussianTailTerm χ ψ s n‖ := by congr 1; ring
    _ ≤ ‖lemma44GaussianShortDirichletSum χ ψ s -
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ +
          ‖lemma44GaussianLongDirichletSum χ ψ s (lemma44PaperGaussianScale D)‖ +
            ‖∑' n : ℕ, lemma44GaussianTailTerm χ ψ s n‖ := norm_add₃_le
    _ ≤ _ := by linarith only [hshort, hmiddle, htail]

/-- The full right vertical Mellin integral equals the short polynomial
with a uniform `O(L^-180)` error, derived from the genuine `Ψ₁` definition. -/
theorem lemma44_right_mellin_approximation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ, lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 t * I) -
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ ≤
      (1 + 5 * Real.exp (2 * Real.pi) + lemma44InverseSquareMass) *
        lemma23PaperL D ^ (-180 : ℤ) := by
  have hm := (lemma44_product_gaussian_mellin_identity χ ψ s hD
    (B := lemma44PaperGaussianScale D)
    (Real.rpow_pos_of_pos (Real.exp_pos _) _) zero_lt_one
      (by linarith [lemma44_omega3_re_pos hL hs])).2.2
  rw [hm]
  exact lemma44_full_gaussian_series_approximation χ ψ hD hL hψ hs

end ZhangLS.Spec
