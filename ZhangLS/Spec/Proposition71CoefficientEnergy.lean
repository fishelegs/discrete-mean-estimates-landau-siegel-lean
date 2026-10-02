import ZhangLS.Spec.Proposition71Objects
import ZhangLS.Spec.Lemma34CoefficientEnergy

/-! # Actual κ*a coefficients and the τ₅² energy in (7.5)

The original κ is retained. Bounds come from its actual fourfold Dirichlet
convolution and from the actual bounded sequence, not a model coefficient.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ArithmeticFunction.zeta
set_option maxHeartbeats 2000000

lemma proposition71_convolution_majorant (f g : ArithmeticFunction ℂ)
    (F G : ArithmeticFunction ℕ) {B C : ℝ} (hB : 0≤B) (_hC : 0≤C)
    (hf : ∀ n, ‖f n‖ ≤ B*(F n : ℝ)) (hg : ∀ n, ‖g n‖ ≤ C*(G n : ℝ)) (n : ℕ) :
    ‖(f*g) n‖ ≤ B*C*((F*G) n : ℝ) := by
  rw [ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply,Nat.cast_sum,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro ab hab
  rw [norm_mul,Nat.cast_mul]
  calc
    _ ≤ (B*(F ab.1 : ℝ))*(C*(G ab.2 : ℝ)) :=
      mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma proposition71_power_coefficient_majorant (β : ℂ) (hβ : β.re=0) (n : ℕ) :
    ‖lemma83PowerCoefficient β n‖ ≤ (ArithmeticFunction.zeta n : ℝ) := by
  by_cases hn : n=0
  · subst n; simp [lemma83PowerCoefficient]
  · simp only [lemma83PowerCoefficient,ArithmeticFunction.coe_mk,if_neg hn,
      ArithmeticFunction.zeta_apply_ne hn,Nat.cast_one]
    have hnp : 0<(n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hnp,neg_re,hβ,neg_zero,Real.rpow_zero]

lemma proposition71_moebius_coefficient_majorant (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ (ArithmeticFunction.zeta n : ℝ) := by
  by_cases hn : n=0
  · subst n; simp
  · rw [ArithmeticFunction.zeta_apply_ne hn]
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

/-- The genuine κ coefficient is bounded by τ₄, uniformly in all imaginary shifts. -/
theorem proposition71_actual_kappa_le_tau_four (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) (n : ℕ) :
    ‖lemma83Kappa β n‖ ≤ (lemma34Tau 4 n : ℝ) := by
  have hpow (j : Fin 3) (n : ℕ) :
      ‖lemma83PowerCoefficient (β j) n‖ ≤ 1*(ArithmeticFunction.zeta n : ℝ) := by
    simpa using proposition71_power_coefficient_majorant (β j) (hβ j) n
  have h01 := proposition71_convolution_majorant (B := 1) (C := 1)
    (lemma83PowerCoefficient (β 0)) (lemma83PowerCoefficient (β 1))
    ArithmeticFunction.zeta ArithmeticFunction.zeta (by norm_num) (by norm_num) (hpow 0) (hpow 1)
  have h012 := proposition71_convolution_majorant (B := 1) (C := 1)
    (lemma83PowerCoefficient (β 0)*lemma83PowerCoefficient (β 1))
    (lemma83PowerCoefficient (β 2)) (ArithmeticFunction.zeta*ArithmeticFunction.zeta)
    ArithmeticFunction.zeta (by norm_num) (by norm_num) (by simpa only [one_mul] using h01) (hpow 2)
  have hμ (n : ℕ) : ‖(ArithmeticFunction.moebius : ArithmeticFunction ℂ) n‖ ≤
      1*(ArithmeticFunction.zeta n : ℝ) := by simpa using proposition71_moebius_coefficient_majorant n
  have hh := proposition71_convolution_majorant (B := 1) (C := 1)
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)
    (lemma83PowerCoefficient (β 0)*lemma83PowerCoefficient (β 1)*lemma83PowerCoefficient (β 2))
    ArithmeticFunction.zeta (ArithmeticFunction.zeta*ArithmeticFunction.zeta*ArithmeticFunction.zeta)
    (by norm_num) (by norm_num) hμ (by simpa only [one_mul] using h012) n
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℕ)*
      (ArithmeticFunction.zeta*ArithmeticFunction.zeta*ArithmeticFunction.zeta)=ArithmeticFunction.zeta^4 := by ring
  simpa only [one_mul,he,lemma83Kappa,lemma34Tau] using hh

/-- The positive sequence from (7.2) as an arithmetic function, with the
standard zero convention at 0. Positive coefficients are unchanged. -/
noncomputable def proposition71ArithmeticSequence (a : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n=0 then 0 else a n,by simp⟩

@[simp] lemma proposition71_arithmetic_sequence_positive (a : ℕ → ℂ) {n : ℕ} (hn : 0<n) :
    proposition71ArithmeticSequence a n=a n := by
  simp [proposition71ArithmeticSequence,hn.ne']

/-- Exactly the τ₅ bound invoked in the proof of (7.5). -/
theorem proposition71_actual_convolution_le_tau_five (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) {B : ℝ} (hB : 0≤B) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖≤B) (n : ℕ) :
    ‖(lemma83Kappa β*proposition71ArithmeticSequence a) n‖ ≤ B*(lemma34Tau 5 n : ℝ) := by
  have ha' (n : ℕ) : ‖proposition71ArithmeticSequence a n‖ ≤ B*(ArithmeticFunction.zeta n : ℝ) := by
    by_cases hn : n=0
    · subst n; simp [proposition71ArithmeticSequence]
    · simpa [proposition71ArithmeticSequence,hn,ArithmeticFunction.zeta_apply_ne hn] using ha n
  have hh := proposition71_convolution_majorant (B := 1) (C := B) (lemma83Kappa β) (proposition71ArithmeticSequence a)
    (ArithmeticFunction.zeta^4) ArithmeticFunction.zeta (by norm_num) hB
    (by simpa [lemma34Tau] using proposition71_actual_kappa_le_tau_four β hβ) ha' n
  simpa only [one_mul,←pow_succ,lemma34Tau] using hh

lemma proposition71_multichoose_five_square_le_twentyfive (e : ℕ) :
    Nat.multichoose 5 e^2≤Nat.multichoose 25 e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h5 := lemma34_multichoose_recurrence 5 e (by norm_num)
    have h25 := lemma34_multichoose_recurrence 25 e (by norm_num)
    have hc : (e+5)^2≤(e+1)*(e+25) := by nlinarith
    have hh : (e+1)^2*Nat.multichoose 5 (e+1)^2≤(e+1)^2*Nat.multichoose 25 (e+1) := by
      calc
        _=((e+5)*Nat.multichoose 5 e)^2 := by rw [←mul_pow,h5]
        _≤((e+1)*(e+25))*Nat.multichoose 25 e := by rw [mul_pow]; exact Nat.mul_le_mul hc ih
        _=(e+1)*((e+25)*Nat.multichoose 25 e) := by ring
        _=(e+1)*((e+1)*Nat.multichoose 25 (e+1)) := by rw [←h25]
        _=_ := by ring
    exact (mul_le_mul_iff_right₀ (by positivity : 0<(e+1)^2)).mp hh

lemma proposition71_tau_five_square_le_twentyfive (n : ℕ) :
    lemma34Tau 5 n^2≤lemma34Tau 25 n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  · unfold lemma34Tau
    rw [(lemma34_tau_multiplicative 5).multiplicative_factorization _ hn,
      (lemma34_tau_multiplicative 25).multiplicative_factorization _ hn]
    simp only [Finsupp.prod]
    rw [←prod_pow]
    apply prod_le_prod'
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    change lemma34Tau 5 (p^n.factorization p)^2≤lemma34Tau 25 (p^n.factorization p)
    rw [lemma34_tau_prime_power hp' 4,lemma34_tau_prime_power hp' 24]
    exact proposition71_multichoose_five_square_le_twentyfive _

/-- The actual harmonic energy needed before large-sieve application. -/
theorem proposition71_tau_five_square_harmonic_sum (X : ℕ) (hX : 1≤X) :
    (∑ n ∈ Icc 1 X, (lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹)≤(1+Real.log (X : ℝ))^25 := by
  have hH : 0≤(harmonic X : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_nonneg (fun _ _ => by positivity)
  calc
    _≤∑ n ∈ Icc 1 X, (lemma34Tau 25 n : ℝ)*(n : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast proposition71_tau_five_square_le_twentyfive n
    _≤(harmonic X : ℝ)^25 := lemma34_tau_weighted_sum_le_harmonic_pow 25 X hX
    _≤_ := pow_le_pow_left₀ hH (harmonic_le_one_add_log X) 25

/-- A bounded original sequence gives the actual κ*a harmonic energy. -/
theorem proposition71_actual_convolution_harmonic_energy (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) {B : ℝ} (hB : 0≤B) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖≤B) (X : ℕ) (hX : 1≤X) :
    (∑ n ∈ Icc 1 X, ‖(lemma83Kappa β*proposition71ArithmeticSequence a) n‖^2*(n : ℝ)⁻¹) ≤
      B^2*(1+Real.log (X : ℝ))^25 := by
  calc
    _≤∑ n ∈ Icc 1 X, (B*(lemma34Tau 5 n : ℝ))^2*(n : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (proposition71_actual_convolution_le_tau_five β hβ hB a ha n)
    _=B^2*∑ n ∈ Icc 1 X, (lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹ := by
      simp_rw [mul_pow,mul_assoc]
      rw [mul_sum]
    _≤_ := mul_le_mul_of_nonneg_left (proposition71_tau_five_square_harmonic_sum X hX) (sq_nonneg B)

end ZhangLS.Spec
