import ZhangLS.Spec.Proposition141SmallCoefficientSum
import ZhangLS.Spec.Proposition71DeltaLargeTail

/-! # Genuine summable long-index envelope for Section14

The constant below is the actual convergent tau5 Dirichlet series at 2. It
is independent of every conductor, coefficient and shift. Bounds retain the
complete scale and both outer divisor factors; there is no residual defined
by subtraction. Prime summation and outer conductor accumulation are separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

/-- Absolute summability of the actual positive τ₅ Dirichlet series at 2. -/
theorem proposition141_tau_five_square_summable :
    Summable (fun n:ℕ => (lemma34Tau 5 n:ℝ)/(n:ℝ)^2) := by
  have ht := (lemma32_tau_lseries_summable 4 (2:ℂ) (by norm_num)).norm
  apply ht.congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n=0
  · subst n; simp
  · simp [hn,Real.rpow_two]

noncomputable def proposition141TauFiveSquareMass : ℝ :=
  ∑'n:ℕ,(lemma34Tau 5 n:ℝ)/(n:ℝ)^2

theorem proposition141_tau_five_square_mass_nonneg : 0≤proposition141TauFiveSquareMass :=
  tsum_nonneg (fun _ => by positivity)

/-- The original κ* divided by l² remains summable after the D₁,d dilation. -/
theorem proposition141_dilated_kappa_square_summable {B : ℝ} (hB : 0≤B)
    {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ) {D₁ d : ℕ}
    (hD₁ : 0<D₁) (hd : 0<d) :
    Summable (fun l:ℕ => ‖κ (D₁*d*l)‖/(l:ℝ)^2) := by
  have ht := proposition141_tau_five_square_summable.mul_left
    (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))
  apply ht.of_nonneg_of_le (fun _ => by positivity)
  intro l
  by_cases hl : l=0
  · subst l; simp
  have hb := div_le_div_of_nonneg_right
    (proposition141_kappa_three_factor_bound hB hκ hD₁ hd (Nat.pos_of_ne_zero hl))
    (sq_nonneg (l:ℝ))
  simpa only [mul_div_assoc] using hb

/-- Every original dilation factor appears in the actual infinite energy. -/
theorem proposition141_dilated_kappa_square_sum {B : ℝ} (hB : 0≤B)
    {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ) {D₁ d : ℕ}
    (hD₁ : 0<D₁) (hd : 0<d) :
    (∑'l:ℕ,‖κ (D₁*d*l)‖/(l:ℝ)^2) ≤
      B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*proposition141TauFiveSquareMass := by
  have ht := proposition141_tau_five_square_summable.mul_left
    (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))
  have hh := (proposition141_dilated_kappa_square_summable hB hκ hD₁ hd).tsum_le_tsum (fun l => ?_) ht
  · simpa only [tsum_mul_left,proposition141TauFiveSquareMass] using hh
  · by_cases hl : l=0
    · subst l; simp
    have hb := div_le_div_of_nonneg_right
      (proposition141_kappa_three_factor_bound hB hκ hD₁ hd (Nat.pos_of_ne_zero hl))
      (sq_nonneg (l:ℝ))
    simpa only [mul_div_assoc] using hb

/-- The actual Δ envelope after an arbitrary positive dilation, with its
scale squared retained exactly. -/
theorem proposition141_scaled_large_delta_tail {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {q l : ℝ} (hq : 0<q)
    (hl : q*lemma51PaperT0 D^(51/50:ℝ)<l) :
    ‖lemma53PaperDelta D (l/q)‖ ≤
      proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2/l^2 := by
  have ht : 0<lemma51PaperT0 D^(51/50:ℝ) := by
    apply Real.rpow_pos_of_pos
    exact pow_pos (by linarith : 0<lemma23PaperL D) _
  have hlp : 0<l := (mul_pos hq ht).trans hl
  have hx : lemma51PaperT0 D^(51/50:ℝ)<l/q := (lt_div_iff₀ hq).mpr (by simpa only [mul_comm] using hl)
  have hh := proposition71_actual_large_delta_tail hD hL hx
  apply hh.trans_eq
  rw [show (-2:ℝ)=-(2:ℝ) by norm_num,Real.rpow_neg (div_pos hlp hq).le,Real.rpow_two]
  field_simp

/-- The tail is an actual pointwise restriction of the original coefficient
and Δ, not an unspecified difference from a proposed main term. -/
noncomputable def proposition141DilatedDeltaTailTerm {N : ℕ}
    (D : ℕ) (θ : DirichletCharacter ℂ N) (κ : ℕ→ℂ) (D₁ d : ℕ)
    (q U : ℝ) (l : ℕ) : ℂ :=
  if U<(l:ℝ) then κ (D₁*d*l)*θ (l:ZMod N)*lemma53PaperDelta D ((l:ℝ)/q) else 0

/-- A fully explicit summable majorant for the actual restricted tail. -/
theorem proposition141_dilated_delta_tail_majorant {D N : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (θ : DirichletCharacter ℂ N)
    (κ : ℕ→ℂ) (D₁ d : ℕ) {q U : ℝ} (hq : 0<q)
    (hU : q*lemma51PaperT0 D^(51/50:ℝ)≤U) (l : ℕ) :
    ‖proposition141DilatedDeltaTailTerm D θ κ D₁ d q U l‖ ≤
      (proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2)*
        (‖κ (D₁*d*l)‖/(l:ℝ)^2) := by
  unfold proposition141DilatedDeltaTailTerm
  split_ifs with hl
  · have hb := proposition141_scaled_large_delta_tail hD hL hq (hU.trans_lt hl)
    rw [norm_mul,norm_mul]
    have hchar : ‖κ (D₁*d*l)‖*‖θ (l:ZMod N)‖≤‖κ (D₁*d*l)‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (θ.norm_le_one _) (norm_nonneg (κ (D₁*d*l)))
    have hh := mul_le_mul hchar hb (norm_nonneg _) (norm_nonneg _)
    convert hh using 1 <;> ring
  · rw [norm_zero]
    have hC := proposition71_large_delta_tail_constant_pos
    positivity

theorem proposition141_dilated_delta_tail_summable {D N : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (θ : DirichletCharacter ℂ N)
    {B : ℝ} (hB : 0≤B) {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ)
    {D₁ d : ℕ} (hD₁ : 0<D₁) (hd : 0<d) {q U : ℝ} (hq : 0<q)
    (hU : q*lemma51PaperT0 D^(51/50:ℝ)≤U) :
    Summable (proposition141DilatedDeltaTailTerm D θ κ D₁ d q U) := by
  apply Summable.of_norm_bounded
    ((proposition141_dilated_kappa_square_summable hB hκ hD₁ hd).mul_left
      (proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2))
  exact proposition141_dilated_delta_tail_majorant hD hL θ κ D₁ d hq hU

/-- Actual infinite-l tail bound for every character, with the complete
q² scale and τ₅(D₁)τ₅(d) factors still present. -/
theorem proposition141_dilated_delta_tail_bound {D N : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (θ : DirichletCharacter ℂ N)
    {B : ℝ} (hB : 0≤B) {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ)
    {D₁ d : ℕ} (hD₁ : 0<D₁) (hd : 0<d) {q U : ℝ} (hq : 0<q)
    (hU : q*lemma51PaperT0 D^(51/50:ℝ)≤U) :
    ‖∑'l:ℕ,proposition141DilatedDeltaTailTerm D θ κ D₁ d q U l‖ ≤
      proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2*
        (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*proposition141TauFiveSquareMass) := by
  have hC : 0≤proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2 :=
    mul_nonneg (mul_nonneg proposition71_large_delta_tail_constant_pos.le (Real.exp_nonneg _)) (sq_nonneg _)
  have hs := proposition141_dilated_delta_tail_summable hD hL θ hB hκ hD₁ hd hq hU
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  have hm := hs.norm.tsum_le_tsum (proposition141_dilated_delta_tail_majorant hD hL θ κ D₁ d hq hU)
    ((proposition141_dilated_kappa_square_summable hB hκ hD₁ hd).mul_left _)
  rw [tsum_mul_left] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (proposition141_dilated_kappa_square_sum hB hκ hD₁ hd) hC)

end ZhangLS.Spec
