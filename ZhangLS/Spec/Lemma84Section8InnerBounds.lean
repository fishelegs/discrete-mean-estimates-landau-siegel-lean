import ZhangLS.Spec.Lemma84Section8Objects
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

/-- Actual, normalized first and repaired-second bounds, uniform over every
positive outer index. The xi error is zero outside its permitted interior. -/
theorem lemma84_section8_inner_bounds :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      1<lemma23PaperL D ∧ ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ∀ μ : ℕ,
        (∀ n : ℕ, 0<n → ‖lemma84Section8First χ c j μ n‖≤
          4*lemma84CompanionConstant*lemma23PaperL D^(-6:ℤ)) ∧
        (∀ d r : ℕ, 0<d → 0<r →
          ‖lemma84Section8Second χ c j μ d r-lemma84Section8SecondHybrid χ c j μ d r‖≤
            12*lemma23PaperL D^(-14:ℤ)) := by
  intro c hc
  obtain ⟨Dc,hDc,hcomp⟩ := lemma84_companion_global c hc
  obtain ⟨De,hDe,herror⟩ := lemma84_genuine_main_error_bounds c hc
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      Dc≤D ∧ De≤D ∧ 2≤D ∧ 1<lemma23PaperL D ∧
        ∀ μ : ℕ, 1<lemma84Section8Cutoff D μ ∧
          lemma84Section8Cutoff D μ<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) ∧
          lemma84Section8Cutoff D μ<lemma23PaperP D ∧
          (1/4)*lemma23PaperL D^9≤Real.log (lemma84Section8Cutoff D μ) from by
    filter_upwards [eventually_ge_atTop Dc,eventually_ge_atTop De,lemma84_section8_cutoffs_eventually]
      with D hc he hd
    exact ⟨hc,he,hd⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).2.2.1,?_⟩
  intro D hDD
  obtain ⟨hDcD,hDeD,hD2,hL,hQs⟩ := hD₀ D hDD
  refine ⟨hL,?_⟩
  intro χ hA j μ
  obtain ⟨hQ1,hQcut,hQP,hlogQ⟩ := hQs μ
  have hLp : 0<lemma23PaperL D := by linarith
  have hQ := lemma84_section8_cutoff_pos D μ
  have hlogQp : 0<Real.log (lemma84Section8Cutoff D μ) := Real.log_pos hQ1
  have hxP (n : ℕ) (hn : 0<n) : lemma84Section8Cutoff D μ/n<lemma23PaperP D :=
    (div_le_self hQ.le (by exact_mod_cast hn)).trans_lt hQP
  constructor
  · intro n hn
    unfold lemma84Section8First
    split_ifs with hnQ
    · have hn0 : 0<(n:ℝ) := by exact_mod_cast hn
      have hx1 : 1≤lemma84Section8Cutoff D μ/n := (le_div_iff₀ hn0).mpr (by simpa using hnQ.le)
      have hb := hcomp D hDcD χ hA j μ _ hx1 (hxP n hn)
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlogQp]
      calc
        _ ≤ (lemma84CompanionConstant*lemma23PaperL D^3)/((1/4)*lemma23PaperL D^9) :=
          div_le_div₀ (by positivity [lemma84_companion_constant_pos]) hb (by positivity) hlogQ
        _ = _ := by simp only [zpow_neg,zpow_ofNat]; field_simp <;> ring
    · simp only [norm_zero]
      positivity [lemma84_companion_constant_pos]
  · intro d r hd hr
    have hn : 0<d*r := Nat.mul_pos hd hr
    have hn0 : 0<((d*r:ℕ):ℝ) := by exact_mod_cast hn
    have hT1 : 1≤lemma56PaperT D := by
      rw [lemma56PaperT,Real.one_le_exp_iff]
      positivity
    unfold lemma84Section8SecondHybrid
    split_ifs with hi
    · have hnQ : ((d*r:ℕ):ℝ)<lemma84Section8Cutoff D μ :=
        hi.trans_le (div_le_self hQ.le hT1)
      have hxT : lemma56PaperT D<lemma84Section8Cutoff D μ/(d*r:ℕ) := by
        have hh := (lt_div_iff₀ (lemma56_paper_T_pos D)).mp hi
        apply (lt_div_iff₀ hn0).mpr
        nlinarith only [hh]
      have hcut : (d*r:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) := by
        simpa only [Nat.cast_mul] using hnQ.trans hQcut
      have he := (herror D hDeD χ hA j μ d r hd hr hcut _ hxT (hxP (d*r) hn)).2.1
      simp only [lemma84Section8Second,lemma84Section8SecondMain,if_pos hnQ]
      rw [←sub_div,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlogQp]
      calc
        _ ≤ (3*lemma23PaperL D^(-5:ℤ))/((1/4)*lemma23PaperL D^9) :=
          div_le_div₀ (by positivity) he (by positivity) hlogQ
        _ = _ := by simp only [zpow_neg,zpow_ofNat]; field_simp <;> ring
    · simp only [sub_self,norm_zero]
      positivity

end ZhangLS.Spec
