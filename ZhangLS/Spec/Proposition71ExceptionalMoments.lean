import ZhangLS.Spec.Proposition71CoefficientEnergy
import ZhangLS.Spec.Lemma33
import ZhangLS.Spec.Lemma81ActualPolynomialMoments

/-! # Actual critical-line moments needed for (7.5)

The long κ*a polynomial retains the strict m<P² endpoint. These are actual
large-sieve applications, uniformly over bounded original sequences.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def proposition71TruncatedKappaCoefficient (D : ℕ) (c : ℝ)
    (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  if (m : ℝ)<lemma23PaperP D^2 then
    (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m else 0

noncomputable def proposition71TruncatedKappaPolynomial {p : ℕ}
    (D : ℕ) (c : ℝ) (a : ℕ → ℂ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑ m ∈ (Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun m : ℕ => (m : ℝ)<lemma23PaperP D^2),
    (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m *
      ψ (m : ZMod p)/(m : ℂ)^s

lemma proposition71_strict_polynomial_eq_LSeries {D p : ℕ} (c : ℝ)
    (a : ℕ → ℂ) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    proposition71TruncatedKappaPolynomial D c a ψ s =
      ∑ m ∈ Icc 1 ⌊lemma23PaperP D^2⌋₊,
        LSeries.term (proposition71TruncatedKappaCoefficient D c a) s m*ψ (m : ZMod p) := by
  rw [←lemma33_original_Dirichlet_sum_eq_actual]
  unfold proposition71TruncatedKappaPolynomial proposition71TruncatedKappaCoefficient
  rw [sum_filter]
  apply sum_congr rfl
  intro m hm
  split_ifs <;> simp

/-- The original strict cutoff is made explicit independently of its prefix enumeration. -/
lemma proposition71_mem_long_indices {D m : ℕ} :
    m ∈ (Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun m : ℕ => (m : ℝ)<lemma23PaperP D^2) ↔
      0<m ∧ (m : ℝ)<lemma23PaperP D^2 := by
  simp only [mem_filter,mem_Icc]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · intro h
    exact ⟨⟨h.1,Nat.le_floor h.2.le⟩,h.2⟩

lemma proposition71_truncated_coefficient_majorant {D : ℕ} (c : ℝ) {B : ℝ}
    (hB : 0≤B) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖≤B) (m : ℕ) :
    ‖proposition71TruncatedKappaCoefficient D c a m‖≤B*(lemma34Tau 5 m : ℝ) := by
  unfold proposition71TruncatedKappaCoefficient
  split_ifs
  · exact proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB a ha m
  · simp only [norm_zero]; positivity

/-- The harmonic energy after the strict cutoff, with no model coefficients. -/
lemma proposition71_truncated_coefficient_energy {D : ℕ} (c : ℝ) {B : ℝ}
    (hB : 0≤B) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖≤B) (X : ℕ) (hX : 1≤X) :
    (∑ n ∈ Icc 1 X, ‖proposition71TruncatedKappaCoefficient D c a n‖^2*(n : ℝ)⁻¹)≤
      B^2*(1+Real.log (X : ℝ))^25 := by
  calc
    _≤∑ n ∈ Icc 1 X, (B*(lemma34Tau 5 n : ℝ))^2*(n : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (proposition71_truncated_coefficient_majorant c hB a ha n)
    _=B^2*∑ n ∈ Icc 1 X, (lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹ := by
      simp_rw [mul_pow,mul_assoc]; rw [mul_sum]
    _≤_ := mul_le_mul_of_nonneg_left (proposition71_tau_five_square_harmonic_sum X hX) (sq_nonneg B)

/-- A fully proved original critical-line second moment, with explicit logarithmic exponent 225. -/
theorem proposition71_actual_kappa_second_moment {D : ℕ} (c : ℝ) {B : ℝ}
    (hB : 0≤B) (hL : 3≤lemma23PaperL D) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖≤B)
    {s : ℂ} (hs : s.re=1/2) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ‖proposition71TruncatedKappaPolynomial D c a ψ.2 s‖^2) ≤
        ((32+Real.pi^2)*3^25)*B^2*lemma23PaperP D^2*lemma23PaperL D^225 := by
  have hP1 : 1≤lemma23PaperP D := by
    apply Real.one_le_exp_iff.mpr
    exact pow_nonneg (by linarith : 0≤lemma23PaperL D) 9
  have hX : 1≤⌊lemma23PaperP D^2⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using one_le_pow₀ (n := 2) hP1)
  have hb := lemma33_actual_second_Dirichlet_mean_bound hL
    (proposition71TruncatedKappaCoefficient D c a) s
  have hm : (∑ ψ ∈ lemma33ActualFamily D,
      ‖proposition71TruncatedKappaPolynomial D c a ψ.2 s‖^2) =
      lemma33ActualMean D ⌊lemma23PaperP D^2⌋₊
        (LSeries.term (proposition71TruncatedKappaCoefficient D c a) s) := by
    simp only [lemma33ActualMean,proposition71_strict_polynomial_eq_LSeries]
  rw [hm]
  norm_num only [hs,show (2:ℝ)*(1/2)=1 by norm_num,Real.rpow_one] at hb
  simp only [div_eq_mul_inv] at hb
  have he := proposition71_truncated_coefficient_energy (D := D) c hB a ha _ hX
  have hlog : Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ) ≤ 2*lemma23PaperL D^9 := by
    have hh := Real.log_le_log (by exact_mod_cast hX : (0:ℝ)<⌊lemma23PaperP D^2⌋₊)
      (Nat.floor_le (sq_nonneg (lemma23PaperP D)))
    simpa [Real.log_pow,lemma23PaperP] using hh
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hp9 : 1≤lemma23PaperL D^9 := one_le_pow₀ hL1
  have hlog0 : 0≤1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤⌊lemma23PaperP D^2⌋₊)
    linarith
  have hlp : (1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ))^25 ≤
      3^25*lemma23PaperL D^225 := by
    have hh := pow_le_pow_left₀ hlog0 (show 1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ)≤3*lemma23PaperL D^9 by linarith) 25
    simpa only [mul_pow,←pow_mul] using hh
  apply hb.trans
  have hf : 0≤(32+Real.pi^2)*lemma23PaperP D^2 := by positivity
  calc
    _≤(32+Real.pi^2)*lemma23PaperP D^2*(B^2*(1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ))^25) := mul_le_mul_of_nonneg_left he hf
    _≤(32+Real.pi^2)*lemma23PaperP D^2*(B^2*(3^25*lemma23PaperL D^225)) := by gcongr
    _=_ := by ring

/-- Finite Hölder with precisely the exponents used in (7.5), without roots. -/
theorem proposition71_exceptional_holder {ι : Type*} [DecidableEq ι]
    (E F : Finset ι) (hEF : E⊆F) (f g : ι → ℂ) :
    (∑ i ∈ E, ‖f i‖*‖g i‖)^4 ≤
      (∑ i ∈ F, ‖f i‖^2)^2*(∑ i ∈ F, ‖g i‖^4)*(E.card : ℝ) := by
  have hcs := sum_mul_sq_le_sq_mul_sq E (fun i => ‖f i‖) (fun i => ‖g i‖)
  have hcs2 := sum_mul_sq_le_sq_mul_sq E (fun i => ‖g i‖^2) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,sum_const,nsmul_eq_mul,mul_one,←pow_mul] at hcs2
  have hf : (∑ i ∈ E, ‖f i‖^2) ≤ ∑ i ∈ F, ‖f i‖^2 :=
    sum_le_sum_of_subset_of_nonneg hEF (fun _ _ _ => sq_nonneg _)
  have hg : (∑ i ∈ E, ‖g i‖^4) ≤ ∑ i ∈ F, ‖g i‖^4 :=
    sum_le_sum_of_subset_of_nonneg hEF (fun _ _ _ => by positivity)
  have he0 : 0≤∑ i ∈ E, ‖f i‖^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hg0 : 0≤∑ i ∈ E, ‖g i‖^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _=((∑ i ∈ E, ‖f i‖*‖g i‖)^2)^2 := by ring
    _≤((∑ i ∈ E, ‖f i‖^2)*(∑ i ∈ E, ‖g i‖^2))^2 :=
      (sq_le_sq₀ (sq_nonneg _) (mul_nonneg he0 hg0)).mpr hcs
    _=(∑ i ∈ E, ‖f i‖^2)^2*(∑ i ∈ E, ‖g i‖^2)^2 := mul_pow _ _ _
    _≤(∑ i ∈ E, ‖f i‖^2)^2*((∑ i ∈ E, ‖g i‖^4)*(E.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
    _≤(∑ i ∈ F, ‖f i‖^2)^2*((∑ i ∈ F, ‖g i‖^4)*(E.card : ℝ)) := by gcongr
    _=_ := by ring

end ZhangLS.Spec
