import ZhangLS.Spec.Lemma56PerronLeftBound

/-! # Exponential margin after the logarithmic Perron contour cost -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_height_log_budget {U H : ℝ} (hU : 1 ≤ U) (hH : 0 ≤ H)
    (hmax : H ≤ Real.exp (2 * U) / 2) :
    0 ≤ Real.log (1 + H) ∧ Real.log (1 + H) ≤ 2 * U := by
  have he : 2 ≤ Real.exp (2 * U) := by
    have h := Real.add_one_le_exp (2 * U)
    linarith only [h, hU]
  constructor
  · exact Real.log_nonneg (by linarith only [hH])
  · have hsum : 1 + H ≤ Real.exp (2 * U) := by linarith only [he, hmax]
    have hlog := Real.log_le_log (by linarith only [hH] : 0 < 1 + H) hsum
    simpa only [Real.log_exp] using hlog

lemma lemma56_perron_margin_polynomial_absorption {U H : ℝ} (hU : 1 ≤ U)
    (hH : 0 ≤ H) (hmax : H ≤ Real.exp (2 * U) / 2) :
    6 * (24 * ((3 / 4 : ℝ) * U) ^ 2 + 28800 * ((3 / 4 : ℝ) * U)) *
      Real.log (1 + H) * Real.exp (-((4 / 3 : ℝ) * U)) ≤
        2017218816 * Real.exp (-((7 / 6 : ℝ) * U)) := by
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hM : 24 * ((3 / 4 : ℝ) * U) ^ 2 + 28800 * ((3 / 4 : ℝ) * U) ≤ 28824 * U ^ 2 := by
    have hs : U ≤ U ^ 2 := by nlinarith only [hU]
    nlinarith only [hs, sq_nonneg U]
  have hlog := lemma56_perron_height_log_budget hU hH hmax
  have hproduct : 6 * (24 * ((3 / 4 : ℝ) * U) ^ 2 + 28800 * ((3 / 4 : ℝ) * U)) *
      Real.log (1 + H) ≤ 345888 * U ^ 3 := by
    calc
      _ ≤ 6 * (28824 * U ^ 2) * (2 * U) := by
        gcongr
        · exact hlog.1
        · exact hlog.2
      _ = _ := by ring
  have he := Real.add_one_le_exp (U / 18)
  have hle : U / 18 ≤ Real.exp (U / 18) := by linarith only [he]
  have hcube : (U / 18) ^ 3 ≤ (Real.exp (U / 18)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hle 3
  have hce : (Real.exp (U / 18)) ^ 3 = Real.exp (U / 6) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hce] at hcube
  have hpoly : U ^ 3 ≤ 5832 * Real.exp (U / 6) := by nlinarith only [hcube]
  calc
    _ ≤ (345888 * (5832 * Real.exp (U / 6))) * Real.exp (-((4 / 3 : ℝ) * U)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact hproduct.trans (mul_le_mul_of_nonneg_left hpoly (by norm_num))
    _ = _ := by
      rw [show (345888 * (5832 * Real.exp (U / 6))) * Real.exp (-((4 / 3 : ℝ) * U)) =
        (345888 * 5832) * (Real.exp (U / 6) * Real.exp (-((4 / 3 : ℝ) * U))) by ring,
        ← Real.exp_add]
      have heq : U / 6 + -((4 / 3 : ℝ) * U) = -((7 / 6 : ℝ) * U) := by ring
      rw [heq]
      ring

lemma lemma56_paper_left_perron_budget {L B H : ℝ} (hL : 2000 ≤ L) (hB : 1 ≤ B)
    (hH : 0 ≤ H) (hmax : H ≤ Real.exp (2 * L ^ (9 / 2 : ℝ)) / 2) :
    let U := L ^ (9 / 2 : ℝ)
    let V := (3 / 4 : ℝ) * U
    let a := 1 - 1 / V
    6 * (24 * V ^ 2 + 28800 * V) * (Real.exp (L ^ 9)) ^ a *
      Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) ≤
        (2017218816 * Real.exp (1 / 4 : ℝ)) * Real.exp (L ^ 9) *
          Real.exp (-((7 / 6 : ℝ) * U)) := by
  let U := L ^ (9 / 2 : ℝ)
  let V := (3 / 4 : ℝ) * U
  let a := 1 - 1 / V
  have hLp : 0 < L := by linarith only [hL]
  have hs := lemma56_high_scale_strict_margin hL
  have hV1 : 1 ≤ V := by dsimp [V, U]; linarith only [hs.2.2.1]
  have hVp : 0 < V := by linarith only [hV1]
  have hInv : 0 < 1 / V := by positivity
  have hInv1 : 1 / V ≤ 1 := (div_le_iff₀ hVp).mpr (by simpa using hV1)
  have ha : 0 ≤ a ∧ a ≤ 1 := by dsimp [a]; constructor <;> linarith only [hInv, hInv1]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith only [ha.1, ha.2]
  have hB2 : 1 ≤ B ^ 2 := by nlinarith only [hB]
  have hden : 0 < 4 * B ^ 2 := by positivity
  have hratio : a ^ 2 / (4 * B ^ 2) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [ha2, hB2]
  have hU1 : 1 ≤ U := by dsimp [U]; linarith only [hs.2.2.1]
  have hp := lemma56_paper_power_margin_identity hLp
  have hm := lemma56_perron_margin_polynomial_absorption hU1 hH hmax
  have hlog := (lemma56_perron_height_log_budget hU1 hH hmax).1
  change 6 * (24 * V ^ 2 + 28800 * V) * (Real.exp (L ^ 9)) ^ a *
    Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) ≤ _
  rw [hp]
  calc
    _ ≤ (Real.exp (L ^ 9) *
        (6 * (24 * V ^ 2 + 28800 * V) * Real.log (1 + H) *
          Real.exp (-((4 / 3 : ℝ) * U)))) * Real.exp (1 / 4 : ℝ) := by
      have he := Real.exp_le_exp.mpr hratio
      convert mul_le_mul_of_nonneg_left he
        (by positivity : 0 ≤ 6 * (24 * V ^ 2 + 28800 * V) *
          (Real.exp (L ^ 9) * Real.exp (-((4 / 3 : ℝ) * U))) * Real.log (1 + H)) using 1 <;> ring
    _ ≤ (Real.exp (L ^ 9) * (2017218816 * Real.exp (-((7 / 6 : ℝ) * U)))) *
          Real.exp (1 / 4 : ℝ) := by gcongr
    _ = _ := by ring

theorem lemma56_uniform_primitive_perron_paper_left_bound :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ {B H τ : ℝ}, 1 ≤ B → 0 ≤ H →
        H ≤ Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2 → |τ| ≤ D →
        let a := 1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))
        (1 / (2 * Real.pi)) * ‖∫ t : ℝ in -H..H,
          lemma56PerronArithmeticIntegrand θ B (lemma23PaperP D) τ ((a : ℂ) + (t : ℂ) * I)‖ ≤
            (2017218816 * Real.exp (1 / 4 : ℝ)) * lemma23PaperP D *
              Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := by
  obtain ⟨Dleft, hleft⟩ := lemma56_uniform_primitive_perron_left_bound
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Dleft Drep, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne B H τ hB hH hHmax hτ
  have hL := (hrep D ((le_max_right _ _).trans hDN)).1
  have hBpos : 0 < B := by linarith only [hB]
  have hbound := (hleft χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne
    (x := lemma23PaperP D) hBpos (Real.exp_pos _) hH hHmax hτ).2
  have hbudget := lemma56_paper_left_perron_budget hL hB hH hHmax
  have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.two_le_pi]
  have hnorm : 0 ≤ ‖∫ t : ℝ in -H..H,
    lemma56PerronArithmeticIntegrand θ B (lemma23PaperP D) τ
      (((1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) : ℝ) + (t : ℂ) * I)‖ :=
    norm_nonneg _
  have hcoef : 1 / (2 * Real.pi) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by simpa using hpi)
  dsimp only
  calc
    _ ≤ ‖∫ t : ℝ in -H..H,
      lemma56PerronArithmeticIntegrand θ B (lemma23PaperP D) τ
        (((1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) : ℝ) + (t : ℂ) * I)‖ := by
      exact (mul_le_mul_of_nonneg_right hcoef hnorm).trans_eq (one_mul _)
    _ ≤ _ := hbound.trans hbudget

end ZhangLS.Spec
