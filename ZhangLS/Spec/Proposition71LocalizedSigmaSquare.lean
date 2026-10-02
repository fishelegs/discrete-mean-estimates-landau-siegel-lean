import ZhangLS.Spec.Proposition71LocalizedGeometry
import ZhangLS.Spec.Proposition71DyadicSigmaBound

/-! # The actual localized Section7 σ* mean-square budget

The original I(Rh) interval, (l,h)=1 condition, κ*a sequence, prime window,
primitive dyadic family and r/φ(r) weights all remain explicit.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71SigmaStar {r : ℕ} (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) (θ : DirichletCharacter ℂ r) : ℂ :=
  proposition71SigmaOnSet D c b a (h : ℝ) d (proposition71LocalizedIndices D R h) θ

noncomputable def proposition71LocalizedDyadicMean (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) : ℝ :=
  proposition71DyadicSigmaNormSum D c b a (h : ℝ) d (proposition71LocalizedIndices D R h) R

lemma proposition71_localized_dyadic_mean_expanded (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) :
    proposition71LocalizedDyadicMean D c b a R h d=
      ∑ r∈primitiveDyadicModuli R, ((r : ℝ)/(Nat.totient r : ℝ))*
        ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
          ‖proposition71SigmaStar D c b a R h d θ‖ :=
  proposition71_dyadic_sigma_norm_sum_expanded D c b a (h : ℝ) d (proposition71LocalizedIndices D R h) R

lemma proposition71_localized_dyadic_mean_nonneg (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) :
    0≤proposition71LocalizedDyadicMean D c b a R h d := by
  rw [proposition71_localized_dyadic_mean_expanded]
  exact sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sum_nonneg (fun _ _ => norm_nonneg _)))

noncomputable def proposition71LargeMeanSquareConstant : ℝ :=
  240*(32+Real.pi^2)^2*lemma54MellinStripConstant^2*4^25

lemma proposition71_large_mean_square_constant_pos : 0<proposition71LargeMeanSquareConstant := by
  have hC := lemma54_mellin_strip_constant_pos
  unfold proposition71LargeMeanSquareConstant
  positivity

/-- A genuine quantitative bound for the original localized σ* family, before
the lower-R cutoff is imposed. No averaged estimate is a hypothesis. -/
theorem proposition71_actual_localized_sigma_square :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ c b B : ℝ, 0≤B →
      ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) → ∀ R : ℝ, 1≤R →
        ∀ d h : ℕ, 0<d → 0<h → ((d*h : ℕ) : ℝ)*R≤lemma81Cutoff D →
          proposition71LocalizedDyadicMean D c b a R h d^2≤
            proposition71LargeMeanSquareConstant*B^2*(lemma34Tau 5 d : ℝ)^2*(h : ℝ)^2*
              R^2*(R^2+lemma23PaperP D)*lemma23PaperP D^3*lemma23PaperL D^6625 := by
  obtain ⟨Dg,hgeo⟩ := proposition71_uniform_localized_geometry
  refine ⟨max 2 (max Dg ⌈Real.exp 2000⌉₊),le_max_left _ _,?_⟩
  intro D hD c b B hB a ha R hR d h hd hh hcut
  have hDg := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDe := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hD1 : 1<D := by have := (le_max_left _ _).trans hD; omega
  have hL : 2000≤lemma23PaperL D := by
    have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hDe)
    simpa [lemma23PaperL] using Real.log_le_log (Real.exp_pos 2000) he
  have hg := (hgeo D hDg).2 R hR d h hd hh hcut
  have hlength := proposition71_localized_length_budget (hgeo D hDg).1 hg.1 hg.2.2
  let X := proposition71LocalScale D R h
  let N := ⌊4*X⌋₊
  let S := proposition71LocalizedIndices D R h
  have hX : 0<X := lt_of_lt_of_le (by norm_num) hg.1
  have hN : 1≤N := hlength.1
  have hSN : ∀n∈S, 0<n ∧ n≤N := by
    intro n hn
    exact mem_Icc.mp (mem_filter.mp hn).1
  have hSX : ∀n∈S, X/3≤(n : ℝ) := fun n hn => (mem_filter.mp hn).2.1
  have hNX : (N : ℝ)≤4*X := Nat.floor_le (by positivity)
  have hhR : 0<(h : ℝ) := by exact_mod_cast hh
  let Af := 15*(32+Real.pi^2)*B^2*(lemma34Tau 5 d : ℝ)^2*(1+Real.log (N : ℝ))^25
  let Ag := (16*(32+Real.pi^2))*(R^2+lemma23PaperP D)*lemma23PaperP D^3
  have hlog0 : 0≤1+Real.log (N : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)
    linarith
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hAf : 0≤Af := by dsimp [Af]; positivity
  have hAg : 0≤Ag := by dsimp [Ag]; positivity
  have hR0 : 0≤R := by linarith
  have hCM := lemma54_mellin_strip_constant_pos
  have hLp : 0≤lemma23PaperL D := by linarith
  have hmean := proposition71_actual_weighted_dyadic_sigma_bound hD1 hL c b d hB hX hR hhR
    a ha S N hN hSN hSX hg.2.1 hNX
  change proposition71LocalizedDyadicMean D c b a R h d≤
    lemma54MellinStripConstant*lemma23PaperL D^3200*(h : ℝ)*R*Real.sqrt Af*Real.sqrt Ag at hmean
  have hs := (sq_le_sq₀ (proposition71_localized_dyadic_mean_nonneg D c b a R h d) (by positivity)).mpr hmean
  simp only [mul_pow,Real.sq_sqrt hAf,Real.sq_sqrt hAg,←pow_mul] at hs
  have hAfBound : Af≤15*(32+Real.pi^2)*B^2*(lemma34Tau 5 d : ℝ)^2*(4^25*lemma23PaperL D^225) := by
    exact mul_le_mul_of_nonneg_left hlength.2 (by positivity)
  calc
    _≤lemma54MellinStripConstant^2*lemma23PaperL D^6400*(h : ℝ)^2*R^2*Af*Ag := by
      convert hs using 1 <;> ring
    _≤lemma54MellinStripConstant^2*lemma23PaperL D^6400*(h : ℝ)^2*R^2*
        (15*(32+Real.pi^2)*B^2*(lemma34Tau 5 d : ℝ)^2*(4^25*lemma23PaperL D^225))*Ag := by gcongr
    _=_ := by unfold proposition71LargeMeanSquareConstant; dsimp [Ag]; ring

end ZhangLS.Spec
