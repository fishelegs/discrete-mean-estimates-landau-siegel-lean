import ZhangLS.Spec.Lemma83RegularPerturbation
import ZhangLS.Spec.AppendixBRoughPrimeLog

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- An additive estimate around a nonzero denominator. Numerator zeros are allowed. -/
lemma lemma83_triple_quotient_perturbation (A B C v t : ℂ) (ε : ℝ)
    (hε : 0 ≤ ε) (hA : ‖A‖ ≤ 3/2) (hB : ‖B‖ ≤ 3/2)
    (hv : ‖v‖ ≤ 1) (hAv : ‖A-v‖ ≤ ε) (hBv : ‖B-v‖ ≤ ε)
    (hCv : ‖C-v‖ ≤ ε) (htv : ‖t-v‖ ≤ ε) (ht : 1/2 ≤ ‖t‖) :
    ‖A*B*C/t-v^2‖ ≤ 16*ε := by
  have ht0 : t ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : A*B*C-v^3 = A*B*(C-v)+A*(B-v)*v+(A-v)*v^2 := by ring
  have hp : ‖A*B*C-v^3‖ ≤ 7*ε := by
    rw [he]
    have hn := norm_add_le (A*B*(C-v)+A*(B-v)*v) ((A-v)*v^2)
    have hn' := norm_add_le (A*B*(C-v)) (A*(B-v)*v)
    have h1 : ‖A*B*(C-v)‖ ≤ (3/2:ℝ)*(3/2)*ε := by
      simp only [norm_mul]
      exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by norm_num)) hCv
        (norm_nonneg _) (by norm_num)
    have h2 : ‖A*(B-v)*v‖ ≤ (3/2:ℝ)*ε := by
      simp only [norm_mul]
      calc
        _ ≤ ((3/2:ℝ)*ε)*1 := mul_le_mul
          (mul_le_mul hA hBv (norm_nonneg _) (by norm_num)) hv
          (norm_nonneg _) (by positivity)
        _ = _ := mul_one _
    have h3 : ‖(A-v)*v^2‖ ≤ ε := by
      rw [norm_mul,norm_pow]
      calc
        _ ≤ ε*1 := mul_le_mul hAv (pow_le_one₀ (norm_nonneg _) hv)
          (sq_nonneg _) hε
        _ = _ := mul_one _
    linarith
  have hv2 : ‖v^2*(v-t)‖ ≤ ε := by
    rw [norm_mul,norm_pow,norm_sub_rev]
    calc
      _ ≤ 1*ε := mul_le_mul (pow_le_one₀ (norm_nonneg _) hv) htv
        (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hn : ‖A*B*C-v^2*t‖ ≤ 8*ε := by
    rw [show A*B*C-v^2*t = (A*B*C-v^3)+v^2*(v-t) by ring]
    exact (norm_add_le _ _).trans (by linarith)
  rw [show A*B*C/t-v^2 = (A*B*C-v^2*t)/t by field_simp,norm_div]
  exact (div_le_div₀ (by positivity) hn (by norm_num : (0:ℝ)<1/2) ht).trans_eq (by ring)

/-- Pure imaginary shifts are Lipschitz in the prime phase, including p=2. -/
lemma lemma83_cpow_shift_sub_one_bound {p : ℕ} (hp : 0 < p)
    (β : ℂ) (hβ : β.re = 0) :
    ‖(p:ℂ)^(-β)-1‖ ≤ ‖β‖*Real.log p := by
  rw [norm_sub_rev,← lemma32_prime_monomial_eq_cpow hp]
  exact lemma83_shift_monomial_sub_one_bound hp β hβ

/-- Actual lambda factor, additively compared with `(1-1/p)^2`. -/
lemma lemma83_lambda_prime_small_shift (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (b : ℝ) (hb : 0 ≤ b)
    (hsmall : ∀ i, ‖β i‖ ≤ b) (j : Fin 3) {p : ℕ} (hp : p.Prime) :
    ‖lemma83LambdaFactor β p (1-β j) - (1-(p:ℂ)⁻¹)^2‖ ≤
      32*b*Real.log p/(p:ℝ) := by
  let u : ℂ := (p:ℂ)⁻¹
  let t : ℂ := (p:ℂ)^(-(1-β j))
  let a : Fin 3 → ℂ := fun i => (p:ℂ)^(-β i)
  let E : ℝ := b*Real.log p/(p:ℝ)
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hphase (i : Fin 3) : ‖a i-1‖ ≤ b*Real.log p :=
    (lemma83_cpow_shift_sub_one_bound hp.pos _ (hβ i)).trans
      (mul_le_mul_of_nonneg_right (hsmall i) hlog)
  have ht : ‖t‖ = (p:ℝ)⁻¹ := lemma83_cpow_tail_norm hp.pos _ (hβ j)
  have hu : ‖u‖ ≤ 1/2 := lemma83_prime_reciprocal_norm_le_half hp
  have ht2 : ‖t‖ ≤ 1/2 := lemma83_tail_parameter_norm_le_half _ (hβ j) hp
  have hat : a j*t=u := lemma83_prime_reciprocal_relation _ hp.pos
  have htu : ‖t-u‖ ≤ E := by
    rw [← hat,show t-a j*t = (1-a j)*t by ring,norm_mul,norm_sub_rev,ht]
    simpa [E,div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (hphase j) (by positivity : 0 ≤ (p:ℝ)⁻¹)
  have hau (i : Fin 3) : ‖a i*t-u‖ ≤ 2*E := by
    rw [show a i*t-u = (a i-1)*t+(t-u) by ring]
    have hh : ‖(a i-1)*t‖ ≤ E := by
      rw [norm_mul,ht]
      simpa [E,div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right (hphase i) (by positivity : 0 ≤ (p:ℝ)⁻¹)
    exact (norm_add_le _ _).trans (by linarith)
  have hav (i : Fin 3) : ‖(1-a i*t)-(1-u)‖ ≤ 2*E := by
    simpa only [sub_sub_sub_cancel_left,norm_sub_rev] using hau i
  have hnorm (i : Fin 3) : ‖1-a i*t‖ ≤ 3/2 := by
    have hh := norm_sub_le (1:ℂ) (a i*t)
    rw [norm_one,norm_mul,lemma83_cpow_shift_norm hp.pos _ (hβ i),one_mul] at hh
    linarith
  have hv : ‖1-u‖ ≤ 1 := by
    have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
    have huR : (p:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (Nat.cast_pos.mpr hp.pos)).mpr hpR
    have he : (1:ℂ)-u = ((1-(p:ℝ)⁻¹:ℝ):ℂ) := by simp [u]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) p)]
  have htv : ‖(1-t)-(1-u)‖ ≤ 2*E := by
    simpa only [sub_sub_sub_cancel_left,norm_sub_rev] using htu.trans (by linarith : E ≤ 2*E)
  have hh := lemma83_triple_quotient_perturbation (1-a 0*t) (1-a 1*t)
    (1-a 2*t) (1-u) (1-t) (2*E) (by positivity) (hnorm 0) (hnorm 1) hv
    (hav 0) (hav 1) (hav 2) htv (lemma83_one_sub_norm_ge_half ht2)
  rw [lemma83_lambda_factor_inverse β hp.pos]
  convert hh using 1
  · simp [lemma83ActualKappaRational,lemma83KappaRational,inv_div,a,t,u]
  · dsimp [E]; ring

lemma lemma83_lambda_prime_norm_small_shift (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (b : ℝ) (hb : 0 ≤ b)
    (hsmall : ∀ i, ‖β i‖ ≤ b) (j : Fin 3) {p : ℕ} (hp : p.Prime) :
    ‖lemma83LambdaFactor β p (1-β j)‖ ≤ 1+32*b*Real.log p/(p:ℝ) := by
  have hu : (p:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (Nat.cast_pos.mpr hp.pos)).mpr
    (by exact_mod_cast hp.one_le)
  have hc : ‖(1-(p:ℂ)⁻¹)^2‖ ≤ 1 := by
    rw [norm_pow,show (1:ℂ)-(p:ℂ)⁻¹ = ((1-(p:ℝ)⁻¹:ℝ):ℂ) by simp,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    exact pow_le_one₀ (by linarith) (by linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) p)])
  have hh := norm_sub_norm_le (lemma83LambdaFactor β p (1-β j)) ((1-(p:ℂ)⁻¹)^2)
  linarith [lemma83_lambda_prime_small_shift β hβ b hb hsmall j hp]

/-- Finite-prime bound only: no convergence assertion at real part one. -/
theorem lemma83_lambda_finite_shift_bound (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (b : ℝ) (hb : 0 ≤ b)
    (hsmall : ∀ i, ‖β i‖ ≤ b) (j : Fin 3) (m : ℕ) (hm : 0 < m) :
    ‖lemma83Lambda β m (1-β j)‖ ≤
      Real.exp (32*b*Real.log 4*(2+Real.log (m:ℝ))) := by
  have hsub : m.primeFactors ⊆ (Icc 1 m).filter Nat.Prime := by
    intro p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos,
      Nat.le_of_dvd hm (Nat.dvd_of_mem_primeFactors hp)⟩,Nat.prime_of_mem_primeFactors hp⟩
  have hmass : (∑ p ∈ m.primeFactors, Real.log (p:ℝ)/(p:ℝ)) ≤
      Real.log 4*(2+Real.log (m:ℝ)) := by
    apply le_trans _ (appendixB_prime_log_mass m)
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
      (Nat.cast_nonneg p)
  unfold lemma83Lambda
  rw [norm_prod]
  calc
    _ ≤ ∏ p ∈ m.primeFactors, Real.exp (32*b*(Real.log (p:ℝ)/(p:ℝ))) := by
      apply prod_le_prod (fun _ _ => norm_nonneg _)
      intro p hp
      apply (lemma83_lambda_prime_norm_small_shift β hβ b hb hsmall j
        (Nat.prime_of_mem_primeFactors hp)).trans
      convert Real.add_one_le_exp (32*b*(Real.log (p:ℝ)/(p:ℝ))) using 1 <;> ring
    _ = Real.exp (32*b*(∑ p ∈ m.primeFactors, Real.log (p:ℝ)/(p:ℝ))) := by
      rw [←Real.exp_sum,←mul_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 32*b)
      nlinarith only [hh]

end ZhangLS.Spec
