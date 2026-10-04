import ZhangLS.Spec.FixedHLambdaReplacementLocal

/-! Uniform replacement of the literal paper Λ by (φ(n)/n)² for the fixed-h
window. The threshold precedes n and j, and depends only on the fixed c. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHLambdaReplacement
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

lemma exp_error_linear {E : ℝ} (hE : 0≤E) (hE1 : E≤1) :
    Real.exp E-1 ≤ E*Real.exp 1 := by
  simpa using lemma83_real_exp_small_scale E 1 hE hE1 (by norm_num)

/-- The literal actual shifts and actual Λ, with no arithmetic approximation
hypothesis and no exclusion of n=1 or of any prime. -/
theorem paper_relative_error {D : ℕ} {c : ℝ} (hc : 0<c)
    (hL : 100≤lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hpoly : (384*Real.pi)*(1+9*Real.log (lemma23PaperL D))^2≤lemma23PaperL D)
    (j : Fin 3) {n : ℕ} (hn : 0<n)
    (hnB : Real.log n≤(201/400:ℝ)*Real.log (lemma23PaperP D)) :
    ‖lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j) /
      (((Nat.totient n:ℝ)/(n:ℝ))^2 : ℂ)-1‖ ≤
      (384*Real.pi*Real.exp 1)*(1+Real.log (Real.log (lemma23PaperP D)))^2 /
        Real.log (lemma23PaperP D) := by
  let L := lemma23PaperL D
  let B := Real.log (lemma23PaperP D)
  have hLp : 0<L := by dsimp [L]; linarith
  have hB : B=L^9 := by dsimp [B,L,lemma23PaperP]; rw [Real.log_exp]
  have hB1 : 1<B := by rw [hB]; exact one_lt_pow₀ (by dsimp [L]; linarith) (by norm_num)
  have hB0 : 0<B := by linarith
  have hlog : Real.log n≤B := by
    have hh : Real.log n≤(201/400:ℝ)*B := hnB
    nlinarith only [hh,hB0]
  have ha : lemma44PaperAlpha D=Real.pi/B := by rfl
  let E := 128*(3*lemma44PaperAlpha D)*(1+Real.log B)^2
  have hE : 0≤E := by dsimp [E]; rw [ha]; positivity
  have hEeq : E=(384*Real.pi)*(1+9*Real.log L)^2/B := by
    dsimp [E]
    rw [ha,hB,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  have hLpow : L≤L^9 := by
    simpa using pow_le_pow_right₀ (by dsimp [L]; linarith : 1≤L) (show 1≤9 by norm_num)
  have hE1 : E≤1 := by
    rw [hEeq]
    exact (div_le_iff₀ hB0).mpr (by simpa [hB,L] using hpoly.trans hLpow)
  have hh := relative_error_exp (lemma83PaperBeta D c) (lemma83_beta_re D c)
    (3*lemma44PaperAlpha D) (by rw [ha]; positivity)
    (lemma83_paper_beta_norm (by linarith : 3≤lemma23PaperL D) hc hsmall) j hn hB1 hlog
  apply hh.trans ((exp_error_linear hE hE1).trans_eq _)
  dsimp [E,B]
  rw [ha]
  ring

/-- A uniform D threshold for every positive n in the actual fixed-h window.
The constant is universal; the threshold is allowed to depend on c. -/
theorem paper_relative_error_uniform (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D≥D₀, ∀ j : Fin 3, ∀ n : ℕ,
      0<n → Real.log n≤(201/400:ℝ)*Real.log (lemma23PaperP D) →
      ‖lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j) /
        (((Nat.totient n:ℝ)/(n:ℝ))^2 : ℂ)-1‖ ≤
        C*(1+Real.log (Real.log (lemma23PaperP D)))^2/Real.log (lemma23PaperP D) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨Dc,_,hs⟩ := lemma52_exists_shift_threshold hc
  have hp := ht.eventually (lemma83_polylog_eventually_le (384*Real.pi) (by positivity) 2)
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2≤D ∧ Dc≤D ∧ 100≤lemma23PaperL D ∧
      (384*Real.pi)*(1+9*Real.log (lemma23PaperL D))^2≤lemma23PaperL D from by
    filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop Dc,
      ht.eventually_ge_atTop 100,hp] with D h2 hDc hL hpD
    exact ⟨h2,hDc,hL,hpD⟩)
  refine ⟨384*Real.pi*Real.exp 1,by positivity,D₀,(hD₀ D₀ le_rfl).1,?_⟩
  intro D hD j n hn hnB
  have hd := hD₀ D hD
  exact paper_relative_error hc hd.2.2.1 (hs D hd.2.1) hd.2.2.2 j hn hnB


/-- Conversion to the equivalent nondividing relative absolute error. -/
lemma relative_to_absolute {A : ℂ} {t e : ℝ} (ht : 0≤t)
    (ht0 : (t:ℂ)≠0) (h : ‖A/(t:ℂ)-1‖≤e) :
    ‖A-(t:ℂ)‖≤t*e := by
  have he : A-(t:ℂ)=(A/(t:ℂ)-1)*(t:ℂ) := by field_simp [ht0]
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right h ht

/-- Uniform form ready for insertion under a finite sum with the original
(φ(n)/n)² weight; positivity/nonvanishing is derived, never assumed. -/
theorem paper_absolute_error_uniform (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D≥D₀, ∀ j : Fin 3, ∀ n : ℕ,
      0<n → Real.log n≤(201/400:ℝ)*Real.log (lemma23PaperP D) →
      ‖lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j) -
        (((Nat.totient n:ℝ)/(n:ℝ))^2 : ℂ)‖ ≤
        ((Nat.totient n:ℝ)/(n:ℝ))^2 *
          (C*(1+Real.log (Real.log (lemma23PaperP D)))^2/Real.log (lemma23PaperP D)) := by
  obtain ⟨C,hC,D₀,hD₀,h⟩ := paper_relative_error_uniform c hc
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D hD j n hn hnB
  have ht0 : ((((Nat.totient n:ℝ)/(n:ℝ))^2 : ℝ):ℂ)≠0 := by
    simpa only [Complex.ofReal_pow,Complex.ofReal_div] using totient_baseline_ne_zero hn
  have hh := h D hD j n hn hnB
  have hh' : ‖lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j) /
      ((((Nat.totient n:ℝ)/(n:ℝ))^2 : ℝ):ℂ)-1‖≤
      C*(1+Real.log (Real.log (lemma23PaperP D)))^2/Real.log (lemma23PaperP D) := by
    simpa only [Complex.ofReal_pow,Complex.ofReal_div] using hh
  simpa only [Complex.ofReal_pow,Complex.ofReal_div] using
    relative_to_absolute (t := ((Nat.totient n:ℝ)/(n:ℝ))^2) (sq_nonneg _) ht0 hh'

end ZhangLS.Spec.FixedHLambdaReplacement
