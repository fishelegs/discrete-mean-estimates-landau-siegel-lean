import ZhangLS.Spec.Lemma81PolynomialFourthMoment

/-! # Actual §7 polynomial moments for Lemma 8.1

Strict original support is bridged to the full prefix without changing the
sequence. Complex conjugation handles the inverse character in A(a₂;1−s,ψ̄).
Both fourth moments and the required squared product moment are proved.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_cutoff_le_P {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    lemma81Cutoff D ≤ lemma23PaperP D := by
  have hLp : 0 ≤ lemma23PaperL D := by linarith only [hL]
  have hT : 1 ≤ lemma56PaperT D := Real.one_le_exp_iff.mpr (Real.rpow_nonneg hLp _)
  have hinv : lemma56PaperT D ^ (-2 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ hT (by norm_num)
  exact (mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg _)).trans_eq (mul_one _)

lemma lemma81_finite_character_polynomial_eq_cpow_sum {p : ℕ} (X : ℕ) (a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma81FiniteCharacterPolynomial X a ψ s =
      ∑ n ∈ Finset.Icc 1 X, a n * ψ (n : ZMod p)/(n : ℂ)^s := by
  unfold lemma81FiniteCharacterPolynomial lemma23FiniteDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hnp)
  rw [div_eq_mul_inv,Complex.cpow_def_of_ne_zero hn0,← Complex.natCast_log,← Complex.exp_neg]
  congr 2
  ring

lemma lemma81_actual_polynomial_eq_prefix {D p : ℕ} {B : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma81Polynomial D a ψ s = lemma81FiniteCharacterPolynomial ⌊lemma23PaperP D⌋₊ a ψ s := by
  rw [lemma81_finite_character_polynomial_eq_cpow_sum]
  unfold lemma81Polynomial
  have hsub : lemma81PolynomialIndices D ⊆ Finset.Icc 1 ⌊lemma23PaperP D⌋₊ := by
    intro n hn
    have hh := Finset.mem_filter.mp hn
    refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hh.1).1,?_⟩
    exact Nat.le_floor (hh.2.le.trans (lemma81_cutoff_le_P hL))
  apply Finset.sum_subset hsub
  intro n hn hnot
  have hge : lemma81Cutoff D ≤ (n : ℝ) := by
    by_contra hh
    have hlt := lt_of_not_ge hh
    apply hnot
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,?_⟩,hlt⟩
    exact_mod_cast hlt.le.trans (Nat.le_ceil (lemma81Cutoff D))
  simp only [ha.2 n hge,zero_mul,zero_div]

lemma lemma81_conjugate_sequence_involutive (a : ℕ → ℂ) :
    lemma81ConjugateSequence (lemma81ConjugateSequence a) = a := by
  funext n
  simp only [lemma81ConjugateSequence,conj_conj]

/-- The actual original A-polynomial fourth moment with exact strict support. -/
theorem lemma81_actual_A_fourth_moment {D : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hL : 3 ≤ lemma23PaperL D) (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a)
    {s : ℂ} (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma81Polynomial D a ψ.2 s‖^4) ≤
      lemma81FourthMomentConstant * B^4 * lemma23PaperP D^2 * lemma23PaperL D^36 := by
  simp_rw [lemma81_actual_polynomial_eq_prefix hL a ha]
  exact lemma81_actual_polynomial_fourth_moment hB hL _ le_rfl a (fun n _ => ha.1 n) hs

lemma lemma81_product_moment_of_fourth {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    {C A B : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : (∑ i ∈ S, ‖f i‖^4) ≤ C*A^2)
    (hg : (∑ i ∈ S, ‖g i‖^4) ≤ C*B^2) :
    (∑ i ∈ S, ‖f i*g i‖^2) ≤ C*A*B := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖f i‖^2) (fun i => ‖g i‖^2)
  have he : (∑ i ∈ S, ‖f i*g i‖^2)^2 ≤ (C*A*B)^2 := by
    calc
      _ = (∑ i ∈ S, ‖f i‖^2*‖g i‖^2)^2 := by simp only [norm_mul,mul_pow]
      _ ≤ (∑ i ∈ S, ‖f i‖^4) * (∑ i ∈ S, ‖g i‖^4) := by
        simpa only [← pow_mul] using hcs
      _ ≤ (C*A^2)*(C*B^2) := mul_le_mul hf hg
        (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)).mp he

lemma lemma81_actual_A_inverse_fourth_moment {D : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hL : 3 ≤ lemma23PaperL D) (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a)
    {s : ℂ} (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma81Polynomial D a ψ.2⁻¹ (1-s)‖^4) ≤
      lemma81FourthMomentConstant * B^4 * lemma23PaperP D^2 * lemma23PaperL D^36 := by
  have hs' : |(conj (1-s)).re-1/2| ≤ lemma44PaperAlpha D := by
    have he : (conj (1-s)).re-1/2 = -(s.re-1/2) := by simp; ring
    rw [he,abs_neg]
    exact hs
  have he : (∑ ψ ∈ lemma33ActualFamily D, ‖lemma81Polynomial D a ψ.2⁻¹ (1-s)‖^4) =
      ∑ ψ ∈ lemma33ActualFamily D, ‖lemma81Polynomial D (lemma81ConjugateSequence a) ψ.2 (conj (1-s))‖^4 := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    have hh := lemma81_polynomial_conjugate D (lemma81ConjugateSequence a) ψ.2 (conj (1-s))
    rw [lemma81_conjugate_sequence_involutive,conj_conj] at hh
    rw [← hh,Complex.norm_conj]
  rw [he]
  exact lemma81_actual_A_fourth_moment hB hL _ (lemma81_conjugate_sequence_admissible ha) hs'

/-- The second displayed mean bound on page 43, for the actual good family
and both original arbitrary coefficient sequences. -/
theorem lemma81_actual_A_product_second_moment {D : ℕ} {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hL : 3 ≤ lemma23PaperL D)
    (χ : RealPrimitiveCharacter D) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) (ha₂ : Lemma81AdmissibleSequence D B₂ a₂)
    {s : ℂ} (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    (∑ ψ ∈ lemma81GoodFamily χ,
      ‖lemma81Polynomial D a₁ ψ.2 s * lemma81Polynomial D a₂ ψ.2⁻¹ (1-s)‖^2) ≤
      lemma81FourthMomentConstant * B₁^2 * B₂^2 * lemma23PaperP D^2 * lemma23PaperL D^36 := by
  let C := lemma81FourthMomentConstant * lemma23PaperP D^2 * lemma23PaperL D^36
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg lemma81_fourth_moment_constant_pos.le (sq_nonneg _)) (by positivity)
  have h₁ : (∑ ψ ∈ lemma33ActualFamily D, ‖lemma81Polynomial D a₁ ψ.2 s‖^4) ≤ C*(B₁^2)^2 := by
    apply (lemma81_actual_A_fourth_moment hB₁ hL a₁ ha₁ hs).trans_eq
    dsimp [C]
    ring
  have h₂ : (∑ ψ ∈ lemma33ActualFamily D, ‖lemma81Polynomial D a₂ ψ.2⁻¹ (1-s)‖^4) ≤ C*(B₂^2)^2 := by
    apply (lemma81_actual_A_inverse_fourth_moment hB₂ hL a₂ ha₂ hs).trans_eq
    dsimp [C]
    ring
  have hp := lemma81_product_moment_of_fourth (lemma33ActualFamily D)
    (fun ψ => lemma81Polynomial D a₁ ψ.2 s) (fun ψ => lemma81Polynomial D a₂ ψ.2⁻¹ (1-s))
    hC (sq_nonneg B₁) (sq_nonneg B₂) h₁ h₂
  calc
    _ ≤ ∑ ψ ∈ lemma33ActualFamily D,
      ‖lemma81Polynomial D a₁ ψ.2 s * lemma81Polynomial D a₂ ψ.2⁻¹ (1-s)‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)
    _ ≤ C*(B₁^2)*(B₂^2) := hp
    _ = _ := by dsimp [C]; ring

end ZhangLS.Spec
