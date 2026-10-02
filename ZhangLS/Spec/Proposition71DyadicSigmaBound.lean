import ZhangLS.Spec.Proposition71DyadicMellinMean

/-! # The actual weighted dyadic σ mean from proved Mellin and sieve inputs -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset MeasureTheory
open scoped Classical
set_option maxHeartbeats 3000000

lemma proposition71_actual_delta_norm_integral {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) :
    (∫t : ℝ, ‖lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)‖)≤
      lemma54MellinStripConstant*lemma23PaperL D^3200*Real.pi := by
  have hδ := proposition71_actual_delta_vertical_integrable hD hL (by norm_num : (1/2 : ℝ)≤1)
  have hbound (t : ℝ) : ‖lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)‖≤
      (lemma54MellinStripConstant*lemma23PaperL D^3200)*(1+t^2)⁻¹ := by
    have hb := lemma54_actual_mellin_closed_strip_bound hD hL
      (s := (1 : ℂ)+(t : ℂ)*I) (by norm_num) (by norm_num)
    have hn : ‖(1 : ℂ)+(t : ℂ)*I‖^2=1+t^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp [pow_two]
    simpa only [hn,Real.rpow_ofNat,div_eq_mul_inv] using hb
  have hi := integral_mono_ae hδ.norm
    (integrable_inv_one_add_sq.const_mul (lemma54MellinStripConstant*lemma23PaperL D^3200))
    (ae_of_all _ hbound)
  simpa only [integral_const_mul,integral_univ_inv_one_add_sq] using hi

/-- Actual product-polynomial bound at each Mellin height, with every moment
proved from the original coefficient sequence and the all-moduli large sieve. -/
theorem proposition71_actual_dyadic_product_bound {D : ℕ} (hL : 3≤lemma23PaperL D)
    (c b : ℝ) (d : ℕ) {B X R : ℝ} (hB : 0≤B) (hX : 0<X) (hR : 1≤R)
    (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤B) (S : Finset ℕ) (N : ℕ) (hN : 1≤N)
    (hSN : ∀n∈S, 0<n ∧ n≤N) (hSX : ∀n∈S, X/3≤(n : ℝ))
    (hRX : R^2≤X) (hNX : (N : ℝ)≤4*X) (t : ℝ) :
    proposition71DyadicPolynomialNormSum D c b a d S R t≤
      Real.sqrt (15*(32+Real.pi^2)*B^2*(lemma34Tau 5 d : ℝ)^2*(1+Real.log (N : ℝ))^25)*
      Real.sqrt ((16*(32+Real.pi^2))*(R^2+lemma23PaperP D)*lemma23PaperP D^3) := by
  have hlog : 0≤1+Real.log (N : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)
    linarith
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hF := proposition71_actual_localized_kappa_mean D c d hB hX hR a ha S N hN hSN hSX hRX hNX
    (s := (1 : ℂ)+(t : ℂ)*I) (by simp)
  have hG := proposition71_actual_weighted_dyadic_inverse_prime_mean hL hR b
    (s := (1 : ℂ)+(t : ℂ)*I) (by simp)
  have hh := proposition71_weighted_primitive_cauchy_bound (primitiveDyadicModuli R)
    (fun r => (r : ℝ)/(Nat.totient r : ℝ)) (fun r => by positivity)
    (fun r θ => proposition71KappaCharacterPolynomial D c a d S θ ((1 : ℂ)+(t : ℂ)*I))
    (fun r θ => proposition71PrimeCharacterPolynomial D b θ ((1 : ℂ)+(t : ℂ)*I))
    (by positivity) (by positivity) hF hG
  simpa only [proposition71DyadicPolynomialNormSum,proposition71DyadicCharacters,
    sum_sigma,mul_sum,mul_assoc] using hh

/-- Actual weighted σ bound. No (7.15)-type averaged estimate is assumed;
its two moments and complete Mellin integral have all been proved. -/
theorem proposition71_actual_weighted_dyadic_sigma_bound {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c b : ℝ) (d : ℕ)
    {B X R h : ℝ} (hB : 0≤B) (hX : 0<X) (hR : 1≤R) (hh : 0<h)
    (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤B) (S : Finset ℕ) (N : ℕ) (hN : 1≤N)
    (hSN : ∀n∈S, 0<n ∧ n≤N) (hSX : ∀n∈S, X/3≤(n : ℝ))
    (hRX : R^2≤X) (hNX : (N : ℝ)≤4*X) :
    proposition71DyadicSigmaNormSum D c b a h d S R≤
      lemma54MellinStripConstant*lemma23PaperL D^3200*h*R*
        Real.sqrt (15*(32+Real.pi^2)*B^2*(lemma34Tau 5 d : ℝ)^2*(1+Real.log (N : ℝ))^25)*
        Real.sqrt ((16*(32+Real.pi^2))*(R^2+lemma23PaperP D)*lemma23PaperP D^3) := by
  let A : ℝ := Real.sqrt (15*(32+Real.pi^2)*B^2*(lemma34Tau 5 d : ℝ)^2*(1+Real.log (N : ℝ))^25)*
    Real.sqrt ((16*(32+Real.pi^2))*(R^2+lemma23PaperP D)*lemma23PaperP D^3)
  have hA : 0≤A := by dsimp [A]; positivity
  have hpoint (t : ℝ) : proposition71DyadicPolynomialNormSum D c b a d S R t≤A :=
    proposition71_actual_dyadic_product_bound (by linarith) c b d hB hX hR a ha S N hN hSN hSX hRX hNX t
  have hδ := proposition71_actual_delta_vertical_integrable hD hL (by norm_num : (1/2 : ℝ)≤1)
  have hV := proposition71_dyadic_mellin_product_integrable hD hL c b a hh d S
    (fun n hn => (hSN n hn).1) R
  have hi : (∫t : ℝ, ‖lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)‖*
      proposition71DyadicPolynomialNormSum D c b a d S R t)≤
        (∫t : ℝ, ‖lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)‖)*A := by
    rw [←integral_mul_const]
    exact integral_mono_ae hV (hδ.norm.mul_const A)
      (ae_of_all _ (fun t => mul_le_mul_of_nonneg_left (hpoint t) (norm_nonneg _)))
  have hi' := hi.trans (mul_le_mul_of_nonneg_right (proposition71_actual_delta_norm_integral hD hL) hA)
  have hm := proposition71_actual_dyadic_mellin_mean hD hL c b a hh hR d S
    (fun n hn => (hSN n hn).1)
  apply hm.trans
  have hR0 : 0≤R := by linarith
  have hb' := mul_le_mul_of_nonneg_left hi' (show 0≤h*R/Real.pi by positivity)
  convert hb' using 1 <;> dsimp [A] <;> field_simp <;> ring

end ZhangLS.Spec
