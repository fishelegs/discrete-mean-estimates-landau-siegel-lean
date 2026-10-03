import ZhangLS.Spec.Proposition71OriginalDeltaReduction
import ZhangLS.Spec.Proposition71Support

/-! # Exact primitive-prime Gauss averaging of the actual Δ₁ mean

Finite character averaging is interchanged with the genuinely summable
infinite series. The short index is proved a unit from the original support;
the long nonunit branch remains explicitly zero.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4000000

lemma proposition71_actual_family_sum_by_prime (D : ℕ)
    (f : lemma33CharacterIndex D → ℂ) :
    (∑ψ∈lemma33ActualFamily D, f ψ)=
      ∑p : lemma33PrimeIndex D, ∑ψ∈(univ : Finset (DirichletCharacter ℂ p.val)).filter
        (fun ψ => ψ.IsPrimitive), f ⟨p,ψ⟩ := by
  unfold lemma33ActualFamily
  rw [sum_filter]
  change (∑ψ : Σp : lemma33PrimeIndex D, DirichletCharacter ℂ p.val,
    if Lemma23InPsi (D := D) ψ.2 then f ψ else 0)=_
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro p hp
  rw [sum_filter]
  apply sum_congr rfl
  intro ψ hψ
  have hiff : Lemma23InPsi (D := D) ψ ↔ ψ.IsPrimitive := by
    have hh := lemma33_mem_prime_window.mp p.property
    exact ⟨fun h => h.2.1,fun h => ⟨hh.1,h,hh.2⟩⟩
  simp only [hiff]

noncomputable def proposition71PrimeGaussDeltaTerm {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m=0 then 0 else ∑n∈lemma81PolynomialIndices D,
    ((lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*
      a₂ n/(n : ℂ)*lemma53PaperDeltaOne D ((m : ℝ)/((p : ℝ)*(n : ℝ))))*
        (∑ψ∈(univ : Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
          gaussSum ψ⁻¹ ZMod.stdAddChar*ψ (m : ZMod p)*ψ⁻¹ (n : ZMod p))

lemma proposition71_actual_gauss_term_interchange {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) (m : ℕ) :
    (∑ψ∈(univ : Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
      gaussSum ψ⁻¹ ZMod.stdAddChar*proposition71DeltaOneDoubleTerm D
        (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*ψ (m : ZMod p))
        (lemma81PolynomialIndices D) (fun n => a₂ n*ψ⁻¹ (n : ZMod p)) (p : ℝ) m)=
      proposition71PrimeGaussDeltaTerm (p := p) D c a₁ a₂ m := by
  by_cases hm : m=0
  · subst m; simp [proposition71DeltaOneDoubleTerm,proposition71PrimeGaussDeltaTerm]
  unfold proposition71DeltaOneDoubleTerm proposition71PrimeGaussDeltaTerm
  simp only [if_neg hm,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro ψ hψ
  ring

/-- Actual finite Gauss averaging and infinite-series interchange, with
absolute convergence proved before the equality is used. -/
theorem proposition71_actual_prime_gauss_average_series {D p : ℕ} [NeZero p]
    (hD : 1<D) {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) :
    Summable (proposition71PrimeGaussDeltaTerm (p := p) D c a₁ a₂) ∧
      (∑ψ∈(univ : Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
        (gaussSum ψ⁻¹ ZMod.stdAddChar/(p : ℂ))*
          (∑'m, proposition71DeltaOneDoubleTerm D
            (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*ψ (m : ZMod p))
            (lemma81PolynomialIndices D) (fun n => a₂ n*ψ⁻¹ (n : ZMod p)) (p : ℝ) m))=
        (p : ℂ)⁻¹*(∑'m, proposition71PrimeGaussDeltaTerm (p := p) D c a₁ a₂ m) := by
  let F := (univ : Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive)
  let T := fun (ψ : DirichletCharacter ℂ p) => proposition71DeltaOneDoubleTerm D
    (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*ψ (m : ZMod p))
    (lemma81PolynomialIndices D) (fun n => a₂ n*ψ⁻¹ (n : ZMod p)) (p : ℝ)
  have hs (ψ : DirichletCharacter ℂ p) : Summable (T ψ) :=
    proposition71_original_delta_one_series_summable hD hB₁ c a₁ a₂ ha₁ ψ
  have hh := hasSum_sum (s := F) (fun ψ hψ => (hs ψ).hasSum.mul_left (gaussSum ψ⁻¹ ZMod.stdAddChar))
  have hsum : HasSum (proposition71PrimeGaussDeltaTerm (p := p) D c a₁ a₂)
      (∑ψ∈F, gaussSum ψ⁻¹ ZMod.stdAddChar*(∑'m, T ψ m)) := by
    apply hh.congr
    intro S
    apply sum_congr rfl
    intro m hm
    exact proposition71_actual_gauss_term_interchange D c a₁ a₂ m
  refine ⟨hsum.summable,?_⟩
  rw [hsum.tsum_eq,mul_sum]
  apply sum_congr rfl
  intro ψ hψ
  dsimp [T]
  ring

/-- The unit-unit formula is used only after proving the original short index
is a unit. The p|m branch is visibly zero and is not restored here. -/
theorem proposition71_actual_prime_gauss_term_branches {D p : ℕ} [NeZero p]
    (hp : p∈lemma56PaperPrimes D) (c : ℝ) (a₁ a₂ : ℕ → ℂ) (m : ℕ) :
    proposition71PrimeGaussDeltaTerm (p := p) D c a₁ a₂ m=
      if m=0 then 0 else ∑n∈lemma81PolynomialIndices D,
        ((lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m*
          a₂ n/(n : ℂ)*lemma53PaperDeltaOne D ((m : ℝ)/((p : ℝ)*(n : ℝ))))*
            (if IsUnit (m : ZMod p) then
              (p.totient : ℂ)*ZMod.stdAddChar ((m : ZMod p)*(n : ZMod p)⁻¹)+1 else 0) := by
  unfold proposition71PrimeGaussDeltaTerm
  by_cases hm : m=0
  · simp only [if_pos hm]
  · simp only [if_neg hm]
    apply sum_congr rfl
    intro n hn
    have hs := (proposition71_mem_indices D n).mp hn
    have hnu := proposition71_short_index_unit hp hs.1 hs.2
    rw [proposition71_primitive_gauss_average_all ((lemma56_mem_paper_primes D p).mp hp).1]
    simp only [hnu,and_true]

noncomputable def proposition71PrimeAveragedDeltaMean (D : ℕ) (c : ℝ)
    (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑p : lemma33PrimeIndex D,
    (-I*(((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)*
      (p.val : ℂ)⁻¹*(∑'m, proposition71PrimeGaussDeltaTerm (p := p.val) D c a₁ a₂ m)

/-- Exact character-averaged form of the already attached actual Gauss mean. -/
theorem proposition71_original_delta_mean_eq_prime_average {D : ℕ} (hD : 1<D)
    {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) :
    proposition71OriginalDeltaOneMean D c a₁ a₂=proposition71PrimeAveragedDeltaMean D c a₁ a₂ := by
  unfold proposition71OriginalDeltaOneMean proposition71PrimeAveragedDeltaMean
  rw [proposition71_actual_family_sum_by_prime]
  apply sum_congr rfl
  intro p hp
  dsimp only
  rw [←mul_sum,(proposition71_actual_prime_gauss_average_series (p := p.val) hD hB₁ c a₁ a₂ ha₁).2]
  ring

end ZhangLS.Spec
