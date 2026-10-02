import ZhangLS.Spec.Lemma32SeriesConvergence
import Mathlib.NumberTheory.LSeries.Deriv

/-! # Genuine coefficient-series and short-polynomial bounds for the common front end

The coefficient sequences are independent of the primitive character in Z.
Only their actual τ₅ majorant and positive finite support are used.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

theorem proposition71_front_coefficient_summable {B : ℝ} (hB : 0≤B)
    (c : ℕ → ℂ) (hc : ∀n, 0<n → ‖c n‖≤B*(lemma34Tau 5 n : ℝ))
    {s : ℂ} (hs : 1<s.re) : LSeriesSummable c s := by
  have ht := ((lemma32_tau_lseries_summable 4 s hs).smul (B : ℂ)).norm
  rw [LSeriesSummable,←summable_norm_iff]
  apply ht.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  by_cases hn : n=0
  · subst n; simp
  apply LSeries.norm_term_le
  simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hB,Complex.norm_natCast]
  exact hc n (Nat.pos_of_ne_zero hn)

noncomputable def proposition71TauFiveThreeHalvesMass : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun m => (lemma34Tau 5 m : ℂ)) (3/2 : ℂ) n‖

lemma proposition71_tau_three_halves_norm_summable :
    Summable (fun n : ℕ => ‖LSeries.term (fun m => (lemma34Tau 5 m : ℂ)) (3/2 : ℂ) n‖) :=
  summable_norm_iff.mpr (lemma32_tau_lseries_summable 4 (3/2 : ℂ) (by norm_num))

lemma proposition71_tau_three_halves_mass_pos : 0<proposition71TauFiveThreeHalvesMass := by
  have ht := proposition71_tau_three_halves_norm_summable.le_tsum 1 (fun n hn => norm_nonneg _)
  have h1 : lemma34Tau 5 1=1 := (lemma34_tau_multiplicative 5).map_one
  have hh : (1 : ℝ)≤proposition71TauFiveThreeHalvesMass := by
    simpa [LSeries.term,proposition71TauFiveThreeHalvesMass,h1] using ht
  linarith

lemma proposition71_front_lseries_norm_bound {B : ℝ} (hB : 0≤B)
    (c : ℕ → ℂ) (hc : ∀n, 0<n → ‖c n‖≤B*(lemma34Tau 5 n : ℝ))
    {s : ℂ} (hs : s.re=3/2) : ‖LSeries c s‖≤B*proposition71TauFiveThreeHalvesMass := by
  have hseries := proposition71_front_coefficient_summable hB c hc (by rw [hs]; norm_num)
  have hnorm : Summable (fun n => ‖LSeries.term c s n‖) := summable_norm_iff.mpr hseries
  have ht (n : ℕ) : ‖LSeries.term c s n‖≤
      B*‖LSeries.term (fun m => (lemma34Tau 5 m : ℂ)) (3/2 : ℂ) n‖ := by
    by_cases hn : n=0
    · subst n; simp
    rw [LSeries.norm_term_eq,LSeries.norm_term_eq,if_neg hn,if_neg hn,hs,Complex.norm_natCast]
    have hre : (3/2 : ℂ).re=(3/2 : ℝ) := by norm_num
    rw [hre]
    calc
      _≤(B*(lemma34Tau 5 n : ℝ))/(n : ℝ)^(3/2 : ℝ) :=
        div_le_div_of_nonneg_right (hc n (Nat.pos_of_ne_zero hn)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _=_ := by ring
  apply (norm_tsum_le_tsum_norm hnorm).trans
  have hh := Summable.tsum_le_tsum ht hnorm (proposition71_tau_three_halves_norm_summable.mul_left B)
  simpa only [tsum_mul_left,proposition71TauFiveThreeHalvesMass] using hh

lemma proposition71_front_lseries_analytic {B : ℝ} (hB : 0≤B)
    (c : ℕ → ℂ) (hc : ∀n, 0<n → ‖c n‖≤B*(lemma34Tau 5 n : ℝ))
    {s : ℂ} (hs : 1<s.re) : AnalyticAt ℂ (LSeries c) s := by
  have hab : LSeries.abscissaOfAbsConv c≤(1 : ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact proposition71_front_coefficient_summable hB c hc (by simpa using hy)
  exact LSeries_analyticOnNhd c s (hab.trans_lt (by exact_mod_cast hs))

noncomputable def proposition71ShortCoefficientMass (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n∈S, ‖a n‖*Real.sqrt (n : ℝ)

lemma proposition71_short_coefficient_mass_nonneg (S : Finset ℕ) (a : ℕ → ℂ) :
    0≤proposition71ShortCoefficientMass S a := sum_nonneg (fun _ _ => by positivity)

lemma proposition71_short_polynomial_norm (S : Finset ℕ) (hS : ∀n∈S, 0<n)
    (a : ℕ → ℂ) {s : ℂ} (hs : s.re=3/2) :
    ‖∑n∈S, a n*(n : ℂ)^(s-1)‖≤proposition71ShortCoefficientMass S a := by
  apply (norm_sum_le _ _).trans_eq
  apply sum_congr rfl
  intro n hn
  have hnp : 0<(n : ℝ) := by exact_mod_cast hS n hn
  rw [norm_mul,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hnp]
  rw [Complex.sub_re,hs,Complex.one_re]
  norm_num only [show (3/2 : ℝ)-1=1/2 by norm_num]
  rw [←Real.sqrt_eq_rpow]

lemma proposition71_short_coefficient_mass_bound {P B : ℝ} (hP : 1≤P) (hB : 0≤B)
    (S : Finset ℕ) (hS : ∀n∈S, 0<n ∧ (n : ℝ)≤P)
    (a : ℕ → ℂ) (ha : ∀n∈S, ‖a n‖≤B) :
    proposition71ShortCoefficientMass S a≤B*P^2 := by
  have hP0 : 0≤P := by linarith
  have hsub : S⊆Icc 1 ⌊P⌋₊ := fun n hn => mem_Icc.mpr ⟨(hS n hn).1,Nat.le_floor (hS n hn).2⟩
  have hcard : (S.card : ℝ)≤P := by
    have hh := card_le_card hsub
    simp only [Nat.card_Icc,add_tsub_cancel_right] at hh
    exact (by exact_mod_cast hh : (S.card : ℝ)≤⌊P⌋₊).trans (Nat.floor_le hP0)
  have hP2 : P≤P^2 := by nlinarith
  unfold proposition71ShortCoefficientMass
  calc
    _≤∑ _n∈S, B*P := by
      apply sum_le_sum; intro n hn
      have hsqrt : Real.sqrt (n : ℝ)≤P := (Real.sqrt_le_iff).mpr ⟨hP0,(hS n hn).2.trans hP2⟩
      exact mul_le_mul (ha n hn) hsqrt (Real.sqrt_nonneg _) hB
    _=(S.card : ℝ)*(B*P) := by simp
    _≤P*(B*P) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hB hP0)
    _=_ := by ring

end ZhangLS.Spec
