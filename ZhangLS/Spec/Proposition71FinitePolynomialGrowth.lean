import ZhangLS.Spec.Proposition71ConductorWeights
import ZhangLS.Spec.Lemma81ActualPolynomialMoments

/-! # Genuine finite-polynomial growth for the common contour shift

The long τ₅ factor is summed using its actual harmonic divisor bound. The
short coefficient bound retains every index in the user's finite prefix.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

lemma proposition71_tau_unweighted_sum (k X : ℕ) (hX : 1≤X) :
    (∑ n∈Icc 1 X, (lemma34Tau k n : ℝ))≤(X : ℝ)*(1+Real.log (X : ℝ))^k := by
  calc
    _≤∑ n∈Icc 1 X, (X : ℝ)*((lemma34Tau k n : ℝ)*(n : ℝ)⁻¹) := by
      apply sum_le_sum
      intro n hn
      have hnp : 0<(n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
      have hnX : (n : ℝ)≤X := by exact_mod_cast (mem_Icc.mp hn).2
      calc
        _=(n : ℝ)*((lemma34Tau k n : ℝ)*(n : ℝ)⁻¹) := by field_simp
        _≤_ := mul_le_mul_of_nonneg_right hnX (by positivity)
    _=(X : ℝ)*(∑ n∈Icc 1 X, (lemma34Tau k n : ℝ)*(n : ℝ)⁻¹) := (mul_sum _ _ _).symm
    _≤_ := mul_le_mul_of_nonneg_left (proposition71_tau_harmonic_bound k X hX) (Nat.cast_nonneg X)

lemma proposition71_finite_tau_polynomial_norm {p : ℕ} {B : ℝ} (hB : 0≤B)
    (k X : ℕ) (hX : 1≤X) (c : ℕ → ℂ)
    (hc : ∀n∈Icc 1 X, ‖c n‖≤B*(lemma34Tau k n : ℝ))
    (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 0≤s.re) :
    ‖lemma81FiniteCharacterPolynomial X c ψ s‖≤B*(X : ℝ)*(1+Real.log (X : ℝ))^k := by
  unfold lemma81FiniteCharacterPolynomial lemma23FiniteDirichletPolynomial
  calc
    _≤∑ n∈Icc 1 X, ‖c n*ψ (n : ZMod p)*Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖ := norm_sum_le _ _
    _≤∑ n∈Icc 1 X, B*(lemma34Tau k n : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ)≤n := by exact_mod_cast (mem_Icc.mp hn).1
      have hlog := Real.log_nonneg hn1
      have he : ‖Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖≤1 := by
        rw [Complex.norm_exp,←Real.exp_zero]
        apply Real.exp_le_exp.mpr
        simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
          Complex.ofReal_im,mul_zero,sub_zero]
        nlinarith only [hs,hlog]
      rw [norm_mul,norm_mul]
      exact (mul_le_mul (mul_le_mul (hc n hn) (ψ.norm_le_one _) (norm_nonneg _) (by positivity))
        he (norm_nonneg _) (by positivity)).trans_eq (by ring)
    _=B*(∑ n∈Icc 1 X, (lemma34Tau k n : ℝ)) := (mul_sum _ _ _).symm
    _≤B*((X : ℝ)*(1+Real.log (X : ℝ))^k) :=
      mul_le_mul_of_nonneg_left (proposition71_tau_unweighted_sum k X hX) hB
    _=_ := by ring

lemma proposition71_long_finite_polynomial_exponential {D p : ℕ} {B : ℝ}
    (hB : 0≤B) (hL : 3≤lemma23PaperL D) (c : ℕ → ℂ)
    (hc : ∀n∈Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖c n‖≤B*(lemma34Tau 5 n : ℝ))
    (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 0≤s.re) :
    ‖lemma81FiniteCharacterPolynomial ⌊lemma23PaperP D^2⌋₊ c ψ s‖≤
      243*B*Real.exp (47*lemma23PaperL D^9) := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp (pow_nonneg hLp.le _)
  have hX : 1≤⌊lemma23PaperP D^2⌋₊ := Nat.le_floor (by exact_mod_cast one_le_pow₀ (n := 2) hP1)
  have hlog : 1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ)≤3*lemma23PaperL D^9 := by
    have hh := Real.log_le_log (by exact_mod_cast hX : (0 : ℝ)<⌊lemma23PaperP D^2⌋₊)
      (Nat.floor_le (sq_nonneg (lemma23PaperP D)))
    simp only [Real.log_pow,lemma23PaperP,Real.log_exp,Nat.cast_ofNat] at hh
    change Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ)≤2*lemma23PaperL D^9 at hh
    linarith only [hh,one_le_pow₀ (n := 9) hL1]
  have hlog0 : 0≤1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ) := by
    have hh := Real.log_nonneg (by exact_mod_cast hX : (1 : ℝ)≤⌊lemma23PaperP D^2⌋₊)
    linarith
  have hL45 : lemma23PaperL D^45≤Real.exp (45*lemma23PaperL D^9) := by
    have hh : lemma23PaperL D≤Real.exp (lemma23PaperL D^9) :=
      (le_self_pow₀ hL1 (by norm_num : (9 : ℕ)≠0)).trans (by linarith [Real.add_one_le_exp (lemma23PaperL D^9)])
    have hp := pow_le_pow_left₀ hLp.le hh 45
    simpa only [←Real.exp_nat_mul,Nat.cast_ofNat] using hp
  apply (proposition71_finite_tau_polynomial_norm hB 5 _ hX c hc ψ hs).trans
  calc
    _≤B*(lemma23PaperP D^2)*(3*lemma23PaperL D^9)^5 := by
      gcongr
      · exact Nat.floor_le (sq_nonneg (lemma23PaperP D))
    _=243*B*(lemma23PaperP D^2)*lemma23PaperL D^45 := by ring
    _≤243*B*(lemma23PaperP D^2)*Real.exp (45*lemma23PaperL D^9) := by gcongr
    _=_ := by
      have he : lemma23PaperP D^2*Real.exp (45*lemma23PaperL D^9)=Real.exp (47*lemma23PaperL D^9) := by
        rw [lemma23PaperP,←Real.exp_nat_mul,←Real.exp_add]
        congr 1
        norm_num
        ring
      calc
        _=(243*B)*(lemma23PaperP D^2*Real.exp (45*lemma23PaperL D^9)) := by ring
        _=_ := by rw [he]

lemma proposition71_short_finite_polynomial_norm {D p : ℕ} {B : ℝ} (hB : 0≤B)
    (X : ℕ) (hX : X≤⌊lemma23PaperP D⌋₊) (a : ℕ → ℂ)
    (ha : ∀n∈Icc 1 X, ‖a n‖≤B) (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : -1≤s.re) :
    ‖lemma81FiniteCharacterPolynomial X a ψ s‖≤B*lemma23PaperP D^2 := by
  have hP := Real.exp_pos (lemma23PaperL D^9)
  have hXP : (X : ℝ)≤lemma23PaperP D :=
    (by exact_mod_cast hX : (X : ℝ)≤⌊lemma23PaperP D⌋₊).trans (Nat.floor_le hP.le)
  unfold lemma81FiniteCharacterPolynomial lemma23FiniteDirichletPolynomial
  have hpoint (n : ℕ) (hn : n∈Icc 1 X) :
      ‖a n*ψ (n : ZMod p)*Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖≤B*lemma23PaperP D := by
    have hnp : 0<(n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
    have hn1 : (1 : ℝ)≤n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnP : (n : ℝ)≤lemma23PaperP D :=
      (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ)≤X).trans hXP
    have hlog := Real.log_nonneg hn1
    have he : ‖Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖≤lemma23PaperP D := by
      rw [Complex.norm_exp]
      have hr : (-s*(Real.log (n : ℝ) : ℂ)).re=-s.re*Real.log (n : ℝ) := by
        simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      rw [hr]
      calc
        _≤Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by nlinarith only [hs,hlog])
        _≤_ := by rw [Real.exp_log hnp]; exact hnP
    rw [norm_mul,norm_mul]
    exact (mul_le_mul (mul_le_mul (ha n hn) (ψ.norm_le_one _) (norm_nonneg _) hB)
      he (norm_nonneg _) (by positivity)).trans_eq (by ring)
  calc
    _≤∑n∈Icc 1 X, ‖a n*ψ (n : ZMod p)*Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖ := norm_sum_le _ _
    _≤∑_n∈Icc 1 X, B*lemma23PaperP D := sum_le_sum hpoint
    _=(X : ℝ)*(B*lemma23PaperP D) := by simp
    _≤lemma23PaperP D*(B*lemma23PaperP D) := mul_le_mul_of_nonneg_right hXP (by positivity)
    _=_ := by ring

end ZhangLS.Spec
