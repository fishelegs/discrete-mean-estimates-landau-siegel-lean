import ZhangLS.Spec.Lemma81
import ZhangLS.Spec.Lemma112

/-! Actual positive weighted energies for Proposition 2.6. The indices are
exactly Ψ₁ and the distinct L(s,ψ)-zeros in (2.14); the branch, three shifts,
and Gaussian are unchanged. This module does not assert a mean bound. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex ComplexConjugate Finset MeasureTheory Set
open scoped Classical

/-- The original Gaussian restricted to the critical line. -/
noncomputable def proposition26RealOmega (D : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt Real.pi / lemma23PaperL D ^ 400 *
    Real.exp (-(t - (lemma23PaperCenter D).im)^2 /
      (4 * (lemma23PaperL D ^ 400)^2))

lemma proposition26_omega_critical {D : ℕ} {s : ℂ} (hs : s.re = 1/2) :
    lemma81Omega D s = (proposition26RealOmega D s.im : ℂ) := by
  have he : s - lemma23PaperCenter D =
      I * ((s.im - (lemma23PaperCenter D).im : ℝ) : ℂ) := by
    have hcenter : (lemma23PaperCenter D).re = 1/2 := by simp [lemma23PaperCenter]
    apply Complex.ext <;> simp [hs,hcenter]
  unfold lemma81Omega proposition26RealOmega
  rw [he]
  push_cast
  congr 1
  congr 1
  rw [mul_pow, I_sq]
  ring

lemma proposition26_real_omega_nonneg (D : ℕ) (t : ℝ) :
    0 ≤ proposition26RealOmega D t := by
  unfold proposition26RealOmega
  positivity

noncomputable def proposition26Weight {D : ℕ} (c : ℝ)
    (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ)
    (ψ : lemma33CharacterIndex D) (ρ : ℂ) : ℝ :=
  (lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ).re * proposition26RealOmega D ρ.im

noncomputable def proposition26Energy {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ)
    (F : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) : ℝ :=
  ∑ ψ ∈ lemma81GoodFamily χ, ∑ ρ ∈ lemma81ZeroFinset D ψ.2,
    proposition26Weight c Y ψ ρ * ‖F ψ ρ‖^2

/-- A uniform threshold yields both actual critical-line location and
nonnegative weights. No hypothesis about a weighted norm is used. -/
theorem proposition26_actual_weight_data {c : ℝ} (hc : Lemma52CompatibleConstant c) :
    ∃ N : ℕ, ∀ D : ℕ, N ≤ D → ∀ χ : RealPrimitiveCharacter D,
      ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
      (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
      ∀ ψ ∈ lemma81GoodFamily χ, ∀ ρ ∈ lemma81ZeroFinset D ψ.2,
        ρ.re = 1/2 ∧ 0 ≤ proposition26Weight c Y ψ ρ ∧
        lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ * lemma81Omega D ρ =
          (proposition26Weight c Y ψ ρ : ℂ) := by
  obtain ⟨Nc,hc⟩ := hc
  obtain ⟨C,hC,Nz,hz⟩ := proposition22_proved
  refine ⟨max Nc Nz,?_⟩
  intro D hD χ Y hY ψ hψ ρ hρ
  have hg := (lemma81_mem_good_family χ ψ).mp hψ
  have hn := lemma33_primitive_nonprincipal hg.1.1 ψ.2 hg.1.2.1
  have hzero := (lemma81_mem_original_zero_finset ψ.2 hn ρ).mp hρ
  have hcoef := (hc χ ψ.2 ((le_max_left _ _).trans hD) hg).2.2
    (Y ψ) (hY ψ hψ) ρ hzero.1 hzero.2
  have hprod : lemma48ActualProduct χ ψ.2 ρ = 0 := by
    simp only [lemma48ActualProduct,hzero.2,zero_mul]
  have hcrit := ((hz χ ψ.2 ((le_max_right _ _).trans hD) hg).1 ρ
    (lemma23_zero_window_subset_omega hzero.1) hprod).1
  refine ⟨hcrit,mul_nonneg hcoef.2.2 (proposition26_real_omega_nonneg D ρ.im),?_⟩
  rw [proposition26_omega_critical hcrit]
  have he : lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ =
      ((lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ).re : ℂ) := by
    apply Complex.ext <;> simp [hcoef.2.1]
  rw [he]
  simp only [proposition26Weight, Complex.ofReal_mul]

/-- Exact weighted energy equals the real part of the original discrete mean
for a polynomial and its coefficientwise conjugate. -/
theorem proposition26_polynomial_energy_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) (a : ℕ → ℂ)
    (hdata : ∀ ψ ∈ lemma81GoodFamily χ, ∀ ρ ∈ lemma81ZeroFinset D ψ.2,
      ρ.re = 1/2 ∧ lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ * lemma81Omega D ρ =
        (proposition26Weight c Y ψ ρ : ℂ)) :
    proposition26Energy χ c Y (fun ψ s => lemma81Polynomial D a ψ.2 s) =
      (lemma81DiscreteMean χ c Y a (lemma81ConjugateSequence a)).re := by
  unfold proposition26Energy lemma81DiscreteMean
  simp only [Complex.re_sum]
  apply sum_congr rfl
  intro ψ hψ
  apply sum_congr rfl
  intro ρ hρ
  have hd := hdata ψ hψ ρ hρ
  have he : conj ρ = 1-ρ := by
    apply Complex.ext <;> norm_num [hd.1]
  have hp := lemma81_polynomial_conjugate D a ψ.2 ρ
  rw [he] at hp
  rw [← hp]
  have hprod : lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ *
      lemma81Polynomial D a ψ.2 ρ * conj (lemma81Polynomial D a ψ.2 ρ) *
      lemma81Omega D ρ = (proposition26Weight c Y ψ ρ : ℂ) *
        (lemma81Polynomial D a ψ.2 ρ * conj (lemma81Polynomial D a ψ.2 ρ)) := by
    rw [← hd.2]
    ring
  rw [hprod, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]

end ZhangLS.Spec
