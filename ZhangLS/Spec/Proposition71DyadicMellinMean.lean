import ZhangLS.Spec.Proposition71SigmaMellin
import ZhangLS.Spec.Proposition71WeightedCauchy

/-! # Actual weighted dyadic Mellin mean before the moment estimates

All finite character sums and integrals are exchanged with proved
integrability. The original hr factor produces the explicit hR/π bound.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset MeasureTheory
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71DyadicCharacters (R : ℝ) :
    Finset (Σr : ℕ, DirichletCharacter ℂ r) :=
  (primitiveDyadicModuli R).sigma (fun r =>
    (univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive))

lemma proposition71_mem_dyadic_characters {R : ℝ} {i : Σr : ℕ, DirichletCharacter ℂ r} :
    i∈proposition71DyadicCharacters R ↔
      1 < i.1 ∧ R≤(i.1 : ℝ) ∧ (i.1 : ℝ)<2*R ∧ i.2.IsPrimitive := by
  simp only [proposition71DyadicCharacters,mem_sigma,mem_filter,mem_univ,true_and,
    mem_primitiveDyadicModuli,and_assoc]

noncomputable def proposition71DyadicSigmaNormSum (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (h : ℝ) (d : ℕ) (S : Finset ℕ) (R : ℝ) : ℝ :=
  ∑ i∈proposition71DyadicCharacters R, ((i.1 : ℝ)/(Nat.totient i.1 : ℝ))*
    ‖proposition71SigmaOnSet D c b a h d S i.2‖

noncomputable def proposition71DyadicPolynomialNormSum (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (d : ℕ) (S : Finset ℕ) (R t : ℝ) : ℝ :=
  ∑ i∈proposition71DyadicCharacters R, ((i.1 : ℝ)/(Nat.totient i.1 : ℝ))*
    ‖proposition71KappaCharacterPolynomial D c a d S i.2 ((1 : ℂ)+(t : ℂ)*I)‖*
    ‖proposition71PrimeCharacterPolynomial D b i.2 ((1 : ℂ)+(t : ℂ)*I)‖

lemma proposition71_dyadic_sigma_norm_sum_expanded (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (h : ℝ) (d : ℕ) (S : Finset ℕ) (R : ℝ) :
    proposition71DyadicSigmaNormSum D c b a h d S R=
      ∑ r∈primitiveDyadicModuli R, ((r : ℝ)/(Nat.totient r : ℝ))*
        ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
          ‖proposition71SigmaOnSet D c b a h d S θ‖ := by
  simp only [proposition71DyadicSigmaNormSum,proposition71DyadicCharacters,sum_sigma,mul_sum]

/-- This real integrand, including the full finite primitive family, is integrable. -/
theorem proposition71_dyadic_mellin_product_integrable {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c b : ℝ)
    (a : ℕ → ℂ) {h : ℝ} (hh : 0<h) (d : ℕ) (S : Finset ℕ)
    (hS : ∀l∈S, 0<l) (R : ℝ) :
    Integrable (fun t : ℝ => ‖lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)‖*
      proposition71DyadicPolynomialNormSum D c b a d S R t) := by
  let U := proposition71DyadicCharacters R
  let F : (Σr : ℕ, DirichletCharacter ℂ r) → ℝ → ℂ := fun i t =>
    proposition71SigmaMellinIntegrand D c b 1 a h d S i.2 t
  have hF (i : Σr : ℕ, DirichletCharacter ℂ r) (hi : i∈U) : Integrable (F i) :=
    proposition71_sigma_mellin_integrable hD hL
      (Nat.zero_lt_of_lt (proposition71_mem_dyadic_characters.mp hi).1)
      c b (by norm_num) hh a d S hS i.2
  have hsum : Integrable (fun t : ℝ => ∑ i∈U,
      (((i.1 : ℝ)/(Nat.totient i.1 : ℝ))/(h*(i.1 : ℝ)))*‖F i t‖) :=
    integrable_finsetSum U (fun i hi => (hF i hi).norm.const_mul _)
  apply hsum.congr
  apply ae_of_all
  intro t
  dsimp only
  unfold proposition71DyadicPolynomialNormSum
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have hir : 0 < i.1 := Nat.zero_lt_of_lt (proposition71_mem_dyadic_characters.mp hi).1
  have hirR : 0<(i.1 : ℝ) := by exact_mod_cast hir
  dsimp [F]
  rw [proposition71_sigma_mellin_norm hir D c b a hh d S i.2 t]
  field_simp

/-- Actual weighted dyadic σ is controlled by the actual two-polynomial Mellin
integral. No pointwise or averaged cancellation estimate is an input. -/
theorem proposition71_actual_dyadic_mellin_mean {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c b : ℝ)
    (a : ℕ → ℂ) {h R : ℝ} (hh : 0<h) (hR : 1≤R) (d : ℕ) (S : Finset ℕ)
    (hS : ∀l∈S, 0<l) :
    proposition71DyadicSigmaNormSum D c b a h d S R≤
      (h*R/Real.pi)*∫t : ℝ, ‖lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)‖*
        proposition71DyadicPolynomialNormSum D c b a d S R t := by
  let U := proposition71DyadicCharacters R
  let w : (Σr : ℕ, DirichletCharacter ℂ r) → ℝ := fun i => (i.1 : ℝ)/(Nat.totient i.1 : ℝ)
  let F : (Σr : ℕ, DirichletCharacter ℂ r) → ℝ → ℂ := fun i t =>
    proposition71SigmaMellinIntegrand D c b 1 a h d S i.2 t
  let V : ℝ → ℝ := fun t => ‖lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)‖*
    proposition71DyadicPolynomialNormSum D c b a d S R t
  have hw (i : Σr : ℕ, DirichletCharacter ℂ r) : 0≤w i := by dsimp [w]; positivity
  have hF (i : Σr : ℕ, DirichletCharacter ℂ r) (hi : i∈U) : Integrable (F i) :=
    proposition71_sigma_mellin_integrable hD hL
      (Nat.zero_lt_of_lt (proposition71_mem_dyadic_characters.mp hi).1)
      c b (by norm_num) hh a d S hS i.2
  have hsum : Integrable (fun t : ℝ => ∑ i∈U, w i*‖F i t‖) :=
    integrable_finsetSum U (fun i hi => (hF i hi).norm.const_mul _)
  have hV : Integrable V := proposition71_dyadic_mellin_product_integrable hD hL c b a hh d S hS R
  have hpoint (t : ℝ) : (∑ i∈U, w i*‖F i t‖)≤(h*(2*R))*V t := by
    dsimp [V]
    unfold proposition71DyadicPolynomialNormSum
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro i hi
    have him := proposition71_mem_dyadic_characters.mp hi
    have hir : 0 < i.1 := Nat.zero_lt_of_lt him.1
    dsimp [F,w]
    rw [proposition71_sigma_mellin_norm hir D c b a hh d S i.2 t]
    calc
      _≤((i.1 : ℝ)/(Nat.totient i.1 : ℝ))*
          (‖lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)‖*(h*(2*R))*
            ‖proposition71KappaCharacterPolynomial D c a d S i.2 ((1 : ℂ)+(t : ℂ)*I)‖*
            ‖proposition71PrimeCharacterPolynomial D b i.2 ((1 : ℂ)+(t : ℂ)*I)‖) := by gcongr; exact him.2.2.1.le
      _=_ := by ring
  have hint : (∫t : ℝ, ∑ i∈U, w i*‖F i t‖)≤(h*(2*R))*∫t : ℝ, V t := by
    rw [←integral_const_mul]
    exact integral_mono_ae hsum (hV.const_mul _) (ae_of_all _ hpoint)
  have hnorm (i : Σr : ℕ, DirichletCharacter ℂ r) (hi : i∈U) :
      w i*‖proposition71SigmaOnSet D c b a h d S i.2‖≤
        (1/(2*Real.pi))*∫t : ℝ, w i*‖F i t‖ := by
    have hir : 0 < i.1 := Nat.zero_lt_of_lt (proposition71_mem_dyadic_characters.mp hi).1
    rw [proposition71_actual_sigma_mellin hD hL hir c b (by norm_num : (1/2 : ℝ)≤1) hh a d S hS i.2]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(1/(2*Real.pi) : ℝ)),integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm (f := F i) (μ := volume))
      (by positivity : 0≤w i*(1/(2*Real.pi)))
    convert hb using 1 <;> dsimp [F] <;> ring
  unfold proposition71DyadicSigmaNormSum
  change (∑ i∈U, w i*‖proposition71SigmaOnSet D c b a h d S i.2‖)≤_
  calc
    _≤∑ i∈U, (1/(2*Real.pi))*∫t : ℝ, w i*‖F i t‖ := sum_le_sum hnorm
    _=(1/(2*Real.pi))*∫t : ℝ, ∑ i∈U, w i*‖F i t‖ := by
      rw [←mul_sum,integral_finsetSum U (fun i hi => (hF i hi).norm.const_mul _)]
    _≤(1/(2*Real.pi))*((h*(2*R))*∫t : ℝ, V t) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _=_ := by dsimp [V]; ring

end ZhangLS.Spec
