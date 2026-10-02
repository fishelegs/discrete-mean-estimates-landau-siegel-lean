import ZhangLS.Spec.Lemma56MangoldtPositivity
import ZhangLS.Spec.Lemma56PrincipalBoundary

/-! # Original Lemma 5.6: faithful target and actual prime window

All prime bounds are strict, the height endpoints are closed, and the
primitive modulus-one character is retained. The full exponential prime
sum estimate is a target here; it has not yet been proved.
-/

namespace ZhangLS.Spec
open Complex Finset
set_option maxHeartbeats 1000000

noncomputable def lemma56PaperT (D : ℕ) : ℝ :=
  Real.exp (lemma23PaperL D ^ (11 / 10 : ℝ))

noncomputable def lemma56PrimeUpper (D : ℕ) : ℝ :=
  lemma23PaperP D * (1 + lemma23PaperL D ^ (-68 : ℤ))

noncomputable def lemma56PaperPrimes (D : ℕ) : Finset ℕ :=
  (range ⌈lemma56PrimeUpper D⌉₊).filter
    (fun p => p.Prime ∧ lemma23PaperP D < (p : ℝ) ∧ (p : ℝ) < lemma56PrimeUpper D)

noncomputable def lemma56PrimeMass (D : ℕ) : ℝ :=
  ∑ p ∈ lemma56PaperPrimes D, (p : ℝ)

noncomputable def lemma56PrimeSum {r : ℕ} (D : ℕ)
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℂ :=
  ∑ p ∈ lemma56PaperPrimes D, θ (p : ZMod r) *
    (p : ℂ) ^ (1 + Complex.I * (t : ℂ))

noncomputable def lemma56Decay (D : ℕ) : ℝ :=
  Real.exp (-(lemma23PaperL D ^ (9 / 2 : ℝ)))

def Lemma56AtConstant (C : ℝ) : Prop :=
  0 < C ∧ ∃ D₀ : ℕ, ∀ {D r : ℕ} [NeZero r]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive →
    (r : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod r)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ t : ℝ, |t| ≤ (D : ℝ) →
      ‖lemma56PrimeSum D θ t‖ ≤ C * lemma56PrimeMass D * lemma56Decay D

def Lemma56Target : Prop := ∃ C : ℝ, Lemma56AtConstant C

lemma lemma56_mem_paper_primes (D p : ℕ) :
    p ∈ lemma56PaperPrimes D ↔
      p.Prime ∧ lemma23PaperP D < (p : ℝ) ∧ (p : ℝ) < lemma56PrimeUpper D := by
  simp only [lemma56PaperPrimes, mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨Nat.lt_ceil.mpr h.2.2, h⟩

lemma lemma56_paper_prime_family {D p : ℕ} (ψ : DirichletCharacter ℂ p) :
    Lemma23InPsi (D := D) ψ ↔ p ∈ lemma56PaperPrimes D ∧ ψ.IsPrimitive := by
  rw [lemma56_mem_paper_primes]
  unfold Lemma23InPsi lemma56PrimeUpper
  tauto

lemma lemma56_prime_mass_nonneg (D : ℕ) : 0 ≤ lemma56PrimeMass D := by
  unfold lemma56PrimeMass
  exact sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma lemma56_paper_T_pos (D : ℕ) : 0 < lemma56PaperT D := Real.exp_pos _

lemma lemma56_decay_pos (D : ℕ) : 0 < lemma56Decay D := Real.exp_pos _

lemma lemma56_principal_paper_sum_zero_height (D : ℕ) :
    ‖lemma56PrimeSum D (1 : DirichletCharacter ℂ 1) 0‖ = lemma56PrimeMass D :=
  lemma56_principal_zero_height_prime_sum_norm (lemma56PaperPrimes D)

lemma lemma56_principal_paper_decay_requires_absorption {D : ℕ} {C : ℝ}
    (hmass : 0 < lemma56PrimeMass D)
    (hbound : ‖lemma56PrimeSum D (1 : DirichletCharacter ℂ 1) 0‖ ≤
      C * lemma56PrimeMass D * lemma56Decay D) :
    1 ≤ C * lemma56Decay D :=
  lemma56_principal_decay_requires_absorption (lemma56PaperPrimes D) hmass hbound

end ZhangLS.Spec
