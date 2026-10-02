import ZhangLS.Spec.Lemma51ShiftEstimates

/-! # Lemma 5.1: all four actual functional-equation factor shifts

The family is the paper's Ψ, with no good-set restriction. The entire
original closed real strip and strict height/shift windows are retained.
One absolute constant and one computable modulus threshold work uniformly.
-/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

noncomputable def lemma51ErrorConstant : ℝ := 22 * Real.exp (600 * Real.pi)

theorem lemma51_error_constant_pos : 0 < lemma51ErrorConstant := by
  unfold lemma51ErrorConstant
  positivity

def Lemma51Estimates {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s w : ℂ) (C : ℝ) : Prop :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  ‖(lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
      (((p : ℝ) * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w‖ ≤
        C * lemma23PaperL D ^ (-114 : ℤ) ∧
  ‖(lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
      ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w‖ ≤
        C * lemma23PaperL D ^ (-68 : ℤ) ∧
  ‖(lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) -
      lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      ((((D * p : ℕ) : ℝ) * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w‖ ≤
        C * lemma23PaperL D ^ (-114 : ℤ) ∧
  ‖(lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) -
      lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      (((D : ℝ) * lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w‖ ≤
        C * lemma23PaperL D ^ (-68 : ℤ)

theorem lemma51_actual_shift_estimates {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s w : ℂ} (hs : Lemma51InRegion D s)
    (hwre : w.re = 0) (hwim : |w.im| < lemma23PaperL D ^ 20) :
    Lemma51Estimates χ ψ s w lemma51ErrorConstant := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpne : p ≠ 1 := hψ.1.ne_one
  have hDpne : D * p ≠ 1 := by
    intro h
    exact hpne (Nat.dvd_one.mp (h ▸ Nat.dvd_mul_left p D))
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  have hlog := lemma51_family_conductor_logs χ ψ hL hψ
  have hfamily := lemma51_family_log_error ψ hψ
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hDp : (0 : ℝ) < (D * p : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero χ.modulus_ne_zero)
      (Nat.pos_of_ne_zero (NeZero.ne p))
  have hDr : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero χ.modulus_ne_zero
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hqerror : |Real.log (p : ℝ) - Real.log (lemma23PaperP D)| ≤
      lemma23PaperL D ^ (-68 : ℤ) := by
    rw [abs_of_nonneg hfamily.1]
    exact hfamily.2
  have htwisterror : |Real.log ((D * p : ℕ) : ℝ) -
      Real.log ((D : ℝ) * lemma23PaperP D)| ≤ lemma23PaperL D ^ (-68 : ℤ) := by
    rw [Nat.cast_mul, Real.log_mul hDr.ne' hp.ne', Real.log_mul hDr.ne' hP.ne']
    convert hqerror using 1
    congr 1
    ring
  have h114 : Real.exp (600 * Real.pi) * (21 * lemma23PaperL D ^ (-114 : ℤ) + 0) ≤
      lemma51ErrorConstant * lemma23PaperL D ^ (-114 : ℤ) := by
    unfold lemma51ErrorConstant
    nlinarith [Real.exp_pos (600 * Real.pi),
      zpow_nonneg (by linarith : 0 ≤ lemma23PaperL D) (-114 : ℤ)]
  have h68 : Real.exp (600 * Real.pi) *
      (21 * lemma23PaperL D ^ (-114 : ℤ) + lemma23PaperL D ^ (-68 : ℤ)) ≤
      lemma51ErrorConstant * lemma23PaperL D ^ (-68 : ℤ) := by
    have hz : lemma23PaperL D ^ (-114 : ℤ) ≤ lemma23PaperL D ^ (-68 : ℤ) :=
      zpow_le_zpow_right₀ hL1 (by norm_num)
    unfold lemma51ErrorConstant
    nlinarith [mul_le_mul_of_nonneg_left hz (Real.exp_nonneg (600 * Real.pi))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (lemma51_actual_shift_at_real_conductor ψ hψ.2.1 hpne hlog.1 hp
      (E := 0) le_rfl (by simp) hL hs hwre hwim).trans h114
  · exact (lemma51_actual_shift_at_real_conductor ψ hψ.2.1 hpne hlog.1 hP
      (by positivity) hqerror hL hs hwre hwim).trans h68
  · exact (lemma51_actual_shift_at_real_conductor (lemma44CharacterTwist χ ψ) htwist hDpne
      hlog.2 hDp (E := 0) le_rfl (by simp) hL hs hwre hwim).trans h114
  · exact (lemma51_actual_shift_at_real_conductor (lemma44CharacterTwist χ ψ) htwist hDpne
      hlog.2 (mul_pos hDr hP) (by positivity) htwisterror hL hs hwre hwim).trans h68

def Lemma51AtConstant (C : ℝ) (D₀ : ℕ) : Prop :=
  ∀ (D p : ℕ) [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi (D := D) ψ →
    ∀ (s w : ℂ), Lemma51InRegion D s → w.re = 0 → |w.im| < lemma23PaperL D ^ 20 →
      Lemma51Estimates χ ψ s w C

def Lemma51Target : Prop := ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, Lemma51AtConstant C D₀

theorem lemma51_proved : Lemma51Target := by
  refine ⟨lemma51ErrorConstant, lemma51_error_constant_pos,
    lemma23SectionFourModulusThreshold, ?_⟩
  intro D p hp χ ψ hD hψ s w hs hwre hwim
  exact lemma51_actual_shift_estimates χ ψ hD hψ hs hwre hwim

end ZhangLS.Spec
