import ZhangLS.Spec.ActualPhaseTransforms
import ZhangLS.Spec.Proposition71ActualKappaSeries
import Mathlib.NumberTheory.LSeries.Deriv

/-! The actual kappa series and a legal strict finite-plus-tail split.
The series equality is restricted to Re(s)>1. Its finite part is never
identified pointwise with the continued L-product.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set Finset
open scoped Real Classical
set_option maxHeartbeats 2000000

noncomputable def actualPhaseKappa (D : ℕ) (c : ℝ) : ArithmeticFunction ℂ :=
  lemma83Kappa (lemma83PaperBeta D c)

noncomputable def actualPhaseStrictIndices (R : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌈R⌉₊).filter (fun n : ℕ => (n : ℝ) < R)

theorem actualPhase_mem_strict_indices {R : ℝ} {n : ℕ} :
    n ∈ actualPhaseStrictIndices R ↔ 0 < n ∧ (n : ℝ) < R := by
  simp only [actualPhaseStrictIndices,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hn,hr⟩
    have hnceil : n ≤ ⌈R⌉₊ := by exact_mod_cast (hr.le.trans (Nat.le_ceil R))
    exact ⟨⟨hn,hnceil⟩,hr⟩

noncomputable def actualPhaseCRightCutoff (D : ℕ) : ℝ :=
  (lemma23PaperP D)^(1999/2000 : ℝ)

noncomputable def actualPhaseLongCutoff (D : ℕ) : ℝ :=
  (lemma23PaperP D)^(201/200 : ℝ)

/-- The actual finite kappa polynomial at any strict positive cutoff. -/
noncomputable def actualPhaseKappaPolynomial {p : ℕ}
    (D : ℕ) (c R : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑ n ∈ actualPhaseStrictIndices R,
    actualPhaseKappa D c n * ψ (n : ZMod p) / (n : ℂ)^s

/-- The omitted terms of the actual series, including the L-series zero convention. -/
noncomputable def actualPhaseKappaTail {p : ℕ}
    (D : ℕ) (c R : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑' n : {n : ℕ // n ∉ actualPhaseStrictIndices R},
    LSeries.term (fun k => ψ (k : ZMod p) * actualPhaseKappa D c k) s n

theorem actualPhase_kappa_polynomial_eq_exp_sum {p : ℕ}
    (D : ℕ) (c R : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    actualPhaseKappaPolynomial D c R ψ s =
      ∑ n ∈ actualPhaseStrictIndices R, actualPhaseKappa D c n * ψ (n : ZMod p) *
        Complex.exp (-s*(Real.log (n : ℝ) : ℂ)) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (actualPhase_mem_strict_indices.mp hn).1.ne'
  rw [div_eq_mul_inv,Complex.cpow_def_of_ne_zero hn0,←Complex.natCast_log,←Complex.exp_neg]
  congr 2
  ring

theorem actualPhase_kappa_polynomial_analytic {p : ℕ}
    (D : ℕ) (c R : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    AnalyticAt ℂ (actualPhaseKappaPolynomial D c R ψ) s := by
  have he : actualPhaseKappaPolynomial D c R ψ = fun z =>
      ∑ n ∈ actualPhaseStrictIndices R, actualPhaseKappa D c n * ψ (n : ZMod p) *
        Complex.exp (-z*(Real.log (n : ℝ) : ℂ)) := by
    funext z
    exact actualPhase_kappa_polynomial_eq_exp_sum D c R ψ z
  rw [he]
  fun_prop

/-- Analyticity follows from the actual convergent coefficient series. -/
theorem actualPhase_kappa_series_analytic {p : ℕ}
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (LSeries (fun n => ψ (n : ZMod p)*actualPhaseKappa D c n)) s := by
  have hab : LSeries.abscissaOfAbsConv
      (fun n => ψ (n : ZMod p)*actualPhaseKappa D c n) ≤ (1 : ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact proposition71_kappa_twist_summable ψ (lemma83PaperBeta D c)
      (lemma83_beta_re D c) (by simpa using hy)
  exact LSeries_analyticOnNhd _ s (hab.trans_lt (by exact_mod_cast hs))

/-- Exact equality of the genuine kappa series with the actual L-quotient
only on the absolutely convergent half-plane. -/
theorem actualPhase_actual_kappa_series {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ψ (n : ZMod p) * actualPhaseKappa D c n) s =
      actualPhaseLQuotient D c ψ s := by
  have hβ := lemma83_beta_re D c
  have h0 : lemma83PaperBeta D c 0 = lemma52PaperBetaOne D c := by simp [lemma83PaperBeta]
  have h1 : lemma83PaperBeta D c 1 = lemma52PaperBetaTwo D c := by simp [lemma83PaperBeta]
  have h2 : lemma83PaperBeta D c 2 = lemma52PaperBetaThree D c := by simp [lemma83PaperBeta]
  have hs0 : 1 < (s+lemma52PaperBetaOne D c).re := by simpa [lemma52PaperBetaOne] using hs
  have hs1 : 1 < (s+lemma52PaperBetaTwo D c).re := by simpa [lemma52PaperBetaTwo] using hs
  have hs2 : 1 < (s+lemma52PaperBetaThree D c).re := by simpa [lemma52PaperBetaThree] using hs
  unfold actualPhaseKappa
  rw [proposition71_kappa_twist_LSeries_ratio ψ _ hβ hs,h0,h1,h2,
    ← DirichletCharacter.LFunction_eq_LSeries ψ hs0,
    ← DirichletCharacter.LFunction_eq_LSeries ψ hs1,
    ← DirichletCharacter.LFunction_eq_LSeries ψ hs2,
    ← DirichletCharacter.LFunction_eq_LSeries ψ hs]
  rfl

/-- The full quotient splits into the strict finite polynomial plus the
actual omitted series. No smallness of that tail is postulated. -/
theorem actualPhase_actual_kappa_split {D p : ℕ} [NeZero p]
    (c R : ℝ) (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 1 < s.re) :
    actualPhaseLQuotient D c ψ s =
      actualPhaseKappaPolynomial D c R ψ s + actualPhaseKappaTail D c R ψ s := by
  rw [← actualPhase_actual_kappa_series c ψ hs]
  have hsum := proposition71_kappa_twist_summable ψ (lemma83PaperBeta D c)
    (lemma83_beta_re D c) hs
  have he := hsum.sum_add_tsum_subtype_compl (actualPhaseStrictIndices R)
  have hf : (∑ n ∈ actualPhaseStrictIndices R,
      LSeries.term (fun k => ψ (k : ZMod p) * actualPhaseKappa D c k) s n) =
      actualPhaseKappaPolynomial D c R ψ s := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos := (actualPhase_mem_strict_indices.mp hn).1
    rw [LSeries.term_of_ne_zero hnpos.ne']
    ring
  change (∑ n ∈ actualPhaseStrictIndices R,
      LSeries.term (fun k : ℕ => ψ (k : ZMod p)*actualPhaseKappa D c k) s n) +
      actualPhaseKappaTail D c R ψ s =
    LSeries (fun n : ℕ => ψ (n : ZMod p)*actualPhaseKappa D c n) s at he
  rw [hf] at he
  exact he.symm

/-- Multiples of p are still zero in the actual finite polynomial; no unit
kernel is ever required at a nonunit argument. -/
theorem actualPhase_kappa_polynomial_units {D p : ℕ}
    (c R : ℝ) (ψ : DirichletCharacter ℂ p) (hp : p ≠ 1) (s : ℂ) :
    actualPhaseKappaPolynomial D c R ψ s =
      ∑ n ∈ (actualPhaseStrictIndices R).filter (fun n => ¬p ∣ n),
        actualPhaseKappa D c n * ψ (n : ZMod p) / (n : ℂ)^s := by
  rw [actualPhaseKappaPolynomial,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hpn : p ∣ n
  · have hz : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
    simp [hpn,hz,ψ.map_zero' hp]
  · simp [hpn]


theorem actualPhase_power_coefficient_conj (β : ℂ) (n : ℕ) :
    conj (lemma83PowerCoefficient β n) = lemma83PowerCoefficient (conj β) n := by
  by_cases hn : n = 0
  · simp [lemma83PowerCoefficient,hn]
  · simp only [lemma83PowerCoefficient,ArithmeticFunction.coe_mk,if_neg hn]
    have harg : (n : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    simpa only [map_natCast,map_neg] using (Complex.cpow_conj (n : ℂ) (-β) harg).symm

theorem actualPhase_kappa_conj (β : Fin 3 → ℂ) (n : ℕ) :
    conj (lemma83Kappa β n) = lemma83Kappa (fun i => conj (β i)) n := by
  simp only [lemma83Kappa,ArithmeticFunction.mul_apply,map_sum,map_mul,
    actualPhase_power_coefficient_conj,ArithmeticFunction.intCoe_apply,map_intCast]

theorem actualPhase_negative_shift_kappa (D : ℕ) (c : ℝ) (n : ℕ) :
    lemma83Kappa (fun i => -lemma83PaperBeta D c i) n = conj (actualPhaseKappa D c n) := by
  have hb (i : Fin 3) : conj (lemma83PaperBeta D c i) = -lemma83PaperBeta D c i := by
    apply Complex.ext <;> simp [lemma83_beta_re]
  simpa only [actualPhaseKappa,hb] using (actualPhase_kappa_conj (lemma83PaperBeta D c) n).symm

/-- The dual series carries conjugated actual kappa coefficients and the inverse
character, and converges on its own safe side Re(s)<0. -/
theorem actualPhase_actual_dual_kappa_series {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : s.re < 0) :
    LSeries (fun n => ψ⁻¹ (n : ZMod p) * conj (actualPhaseKappa D c n)) (1-s) =
      actualPhaseDualLQuotient D c ψ s := by
  let β : Fin 3 → ℂ := fun i => -lemma83PaperBeta D c i
  have hβ (i : Fin 3) : (β i).re = 0 := by simp [β,lemma83_beta_re]
  have hsafe : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have h0 : β 0 = -lemma52PaperBetaOne D c := by simp [β,lemma83PaperBeta]
  have h1 : β 1 = -lemma52PaperBetaTwo D c := by simp [β,lemma83PaperBeta]
  have h2 : β 2 = -lemma52PaperBetaThree D c := by simp [β,lemma83PaperBeta]
  have hs0 : 1 < (1-s+-lemma52PaperBetaOne D c).re := by simpa [lemma52PaperBetaOne] using hsafe
  have hs1 : 1 < (1-s+-lemma52PaperBetaTwo D c).re := by simpa [lemma52PaperBetaTwo] using hsafe
  have hs2 : 1 < (1-s+-lemma52PaperBetaThree D c).re := by simpa [lemma52PaperBetaThree] using hsafe
  have he : (fun n : ℕ => ψ⁻¹ (n : ZMod p)*lemma83Kappa β n) =
      (fun n : ℕ => ψ⁻¹ (n : ZMod p)*conj (actualPhaseKappa D c n)) := by
    funext n
    rw [actualPhase_negative_shift_kappa]
  have hh := proposition71_kappa_twist_LSeries_ratio ψ⁻¹ β hβ hsafe
  rw [he,h0,h1,h2,←DirichletCharacter.LFunction_eq_LSeries ψ⁻¹ hs0,
    ←DirichletCharacter.LFunction_eq_LSeries ψ⁻¹ hs1,
    ←DirichletCharacter.LFunction_eq_LSeries ψ⁻¹ hs2,
    ←DirichletCharacter.LFunction_eq_LSeries ψ⁻¹ hsafe] at hh
  simpa only [actualPhaseDualLQuotient,sub_eq_add_neg] using hh

noncomputable def actualPhaseDualKappaPolynomial {p : ℕ}
    (D : ℕ) (c R : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑ n ∈ actualPhaseStrictIndices R,
    conj (actualPhaseKappa D c n) * ψ⁻¹ (n : ZMod p) / (n : ℂ)^(1-s)

noncomputable def actualPhaseDualKappaTail {p : ℕ}
    (D : ℕ) (c R : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑' n : {n : ℕ // n ∉ actualPhaseStrictIndices R},
    LSeries.term (fun k => ψ⁻¹ (k : ZMod p) * conj (actualPhaseKappa D c k)) (1-s) n

theorem actualPhase_actual_dual_kappa_split {D p : ℕ} [NeZero p]
    (c R : ℝ) (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : s.re < 0) :
    actualPhaseDualLQuotient D c ψ s =
      actualPhaseDualKappaPolynomial D c R ψ s + actualPhaseDualKappaTail D c R ψ s := by
  rw [←actualPhase_actual_dual_kappa_series c ψ hs]
  have hsafe : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hsum := proposition71_kappa_twist_summable ψ⁻¹
    (fun i => -lemma83PaperBeta D c i) (fun i => by simp [lemma83_beta_re]) hsafe
  have heq : (fun n : ℕ => ψ⁻¹ (n : ZMod p)*
      lemma83Kappa (fun i => -lemma83PaperBeta D c i) n) =
      (fun n : ℕ => ψ⁻¹ (n : ZMod p)*conj (actualPhaseKappa D c n)) := by
    funext n
    rw [actualPhase_negative_shift_kappa]
  rw [heq] at hsum
  have he := hsum.sum_add_tsum_subtype_compl (actualPhaseStrictIndices R)
  have hf : (∑ n ∈ actualPhaseStrictIndices R,
      LSeries.term (fun k => ψ⁻¹ (k : ZMod p) * conj (actualPhaseKappa D c k)) (1-s) n) =
      actualPhaseDualKappaPolynomial D c R ψ s := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos := (actualPhase_mem_strict_indices.mp hn).1
    rw [LSeries.term_of_ne_zero hnpos.ne']
    ring
  change _ + actualPhaseDualKappaTail D c R ψ s = _ at he
  rw [hf] at he
  exact he.symm


theorem actualPhase_dual_kappa_polynomial_units {D p : ℕ}
    (c R : ℝ) (ψ : DirichletCharacter ℂ p) (hp : p ≠ 1) (s : ℂ) :
    actualPhaseDualKappaPolynomial D c R ψ s =
      ∑ n ∈ (actualPhaseStrictIndices R).filter (fun n => ¬p ∣ n),
        conj (actualPhaseKappa D c n) * ψ⁻¹ (n : ZMod p) / (n : ℂ)^(1-s) := by
  rw [actualPhaseDualKappaPolynomial,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hpn : p ∣ n
  · have hz : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
    simp [hpn,hz,(ψ⁻¹).map_zero' hp]
  · simp [hpn]

/-- The hard cutoff is strict even when its real value happens to be integral. -/
theorem actualPhase_regression_kappa_endpoint (R : ℝ) (n : ℕ) (hn : (n : ℝ) = R) :
    n ∉ actualPhaseStrictIndices R := by
  intro hm
  have hh := (actualPhase_mem_strict_indices.mp hm).2
  rw [hn] at hh
  exact (lt_irrefl _) hh


/-- On the central line the finite dual polynomial is the literal conjugate
of the corresponding finite right polynomial, including the same hard cutoff. -/
theorem actualPhase_dual_polynomial_on_critical_line {D p : ℕ}
    (c R : ℝ) (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : s.re = 1/2) :
    actualPhaseDualKappaPolynomial D c R ψ s = conj (actualPhaseKappaPolynomial D c R ψ s) := by
  have he : 1-s = conj s := by
    apply Complex.ext <;> simp [hs] <;> ring
  unfold actualPhaseDualKappaPolynomial actualPhaseKappaPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hchar : conj (ψ (n : ZMod p)) = ψ⁻¹ (n : ZMod p) := MulChar.star_apply' ψ _
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  have hpow : conj ((n : ℂ)^s) = (n : ℂ)^(conj s) := by
    simpa only [map_natCast] using (Complex.cpow_conj (n : ℂ) s harg).symm
  rw [map_div₀,map_mul,hchar,hpow,he]

end ZhangLS.Spec
