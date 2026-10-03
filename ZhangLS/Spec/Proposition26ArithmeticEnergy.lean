import ZhangLS.Spec.Proposition26EnergyObjects
import ZhangLS.Spec.Proposition71FinalAssembly

/-! A proved uniform source arithmetic bound for the actual weighted
polynomial norm. The complete Section 7 S_j remain explicit, including all
d,r,m,n, μ(r), φ(r), λ and ξ factors. No desired norm estimate is an input.
To finish Proposition 2.6 one must still bound these source arithmetic sums
for the actual smoothing errors and obtain the Section 9 H₂ bound. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex ComplexConjugate Finset
open scoped Classical

lemma proposition26_main_term_norm {D : ℕ} (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (hα : 0<lemma44PaperAlpha D) :
    ‖proposition71MainTerm D c a₁ a₂‖ ≤
      (2/lemma44PaperAlpha D) *
        (∑ j : Fin 3, ‖proposition71ArithmeticSum D c j a₁ a₂‖) *
          lemma33ActualPrimeMass D := by
  let S := fun j : Fin 3 => proposition71ArithmeticSum D c j a₁ a₂
  have hs : ∑ j : Fin 3, ‖S j‖ = ‖S 0‖+‖S 1‖+‖S 2‖ := by
    simp [Fin.sum_univ_succ]
    ring
  have hb : ‖(1/2:ℂ)*S 0+2*S 1+(3/2:ℂ)*S 2‖ ≤
      2*(∑ j : Fin 3, ‖S j‖) := by
    have ht := (norm_add_le ((1/2:ℂ)*S 0+2*S 1) ((3/2:ℂ)*S 2)).trans
      (add_le_add (norm_add_le ((1/2:ℂ)*S 0) (2*S 1)) le_rfl)
    simp only [norm_mul,norm_div,norm_one,norm_ofNat] at ht
    rw [hs]
    nlinarith only [ht,norm_nonneg (S 0),norm_nonneg (S 2)]
  have hM : 0≤lemma33ActualPrimeMass D := by
    unfold lemma33ActualPrimeMass
    positivity
  unfold proposition71MainTerm
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hα,
    abs_of_nonneg hM]
  change (lemma44PaperAlpha D)⁻¹ * ‖(1/2:ℂ)*S 0+2*S 1+(3/2:ℂ)*S 2‖ * _ ≤ _
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hα.le)) hM).trans_eq (by ring)

/-- Actual weighted energy, obtained from the completed original L8.1 and
P7.1, with C fixed before ε and every bounded sequence. This is an estimate
in original arithmetic S_j, not a statement assuming the desired mean. -/
theorem proposition26_polynomial_energy_arithmetic :
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
      ∀ B : ℝ, 0<B → ∃ C : ℝ, 0<C ∧
        ∀ ε : ℝ, 0<ε → ∃ N : ℕ, 2≤N ∧
          ∀ D : ℕ, N≤D → ∀ χ : RealPrimitiveCharacter D,
            NormalizedAssumptionA χ → ∀ a : ℕ → ℂ,
              Lemma81AdmissibleSequence D B a →
              ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
                (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
                0≤proposition26Energy χ c Y (fun ψ s => lemma81Polynomial D a ψ.2 s) ∧
                proposition26Energy χ c Y (fun ψ s => lemma81Polynomial D a ψ.2 s) ≤
                  lemma33ActualPrimeMass D *
                    ((4/lemma44PaperAlpha D+C*lemma23PaperL D^2)*
                      (∑ j : Fin 3, ‖proposition71ArithmeticSum D c j a
                        (lemma81ConjugateSequence a)‖)+ε) := by
  obtain ⟨c,hc,hcompat,h81⟩ := lemma81_proved
  refine ⟨c,hc,hcompat,?_⟩
  intro B hB
  obtain ⟨C,hC,h71⟩ := proposition71_at_every_positive_constant hc B B hB hB
  refine ⟨2*C,by positivity,?_⟩
  intro ε hε
  obtain ⟨N81,hN81⟩ := h81 B B hB hB (ε/2) (by positivity)
  obtain ⟨N71,hN71,h71⟩ := h71 (ε/4) (by positivity)
  obtain ⟨Nw,hw⟩ := proposition26_actual_weight_data hcompat
  refine ⟨max 2 (max N81 (max N71 (max Nw lemma23SectionFourModulusThreshold))),
    le_max_left _ _,?_⟩
  intro D hD χ hA a ha Y hY
  have hDN := (le_max_right _ _).trans hD
  have hD81 := (le_max_left _ _).trans hDN
  have hDN' := (le_max_right _ _).trans hDN
  have hD71 := (le_max_left _ _).trans hDN'
  have hDN'' := (le_max_right _ _).trans hDN'
  have hDw := (le_max_left _ _).trans hDN''
  have hsection := (le_max_right _ _).trans hDN''
  have hdata := hw D hDw χ Y hY
  have hnonneg : 0≤proposition26Energy χ c Y (fun ψ s => lemma81Polynomial D a ψ.2 s) := by
    apply sum_nonneg
    intro ψ hψ
    apply sum_nonneg
    intro ρ hρ
    exact mul_nonneg (hdata ψ hψ ρ hρ).2.1 (sq_nonneg _)
  refine ⟨hnonneg,?_⟩
  have he := proposition26_polynomial_energy_eq χ c Y a
    (fun ψ hψ ρ hρ => ⟨(hdata ψ hψ ρ hρ).1,(hdata ψ hψ ρ hρ).2.2⟩)
  have hconj := lemma81_conjugate_sequence_admissible ha
  have hm := hN81 D hD81 χ a (lemma81ConjugateSequence a) ha hconj Y hY
  rw [lemma81_conjugate_sequence_involutive] at hm
  have hp := h71 D hD71 χ hA a (lemma81ConjugateSequence a) ha hconj
  have hα := (lemma44_alpha_pos_le_one
    (lemma44_parameters_at_explicit_threshold hsection).1).1
  have hmain := proposition26_main_term_norm c a (lemma81ConjugateSequence a) hα
  let Θ := lemma81ThetaOne χ c a (lemma81ConjugateSequence a)
  let M := lemma81DiscreteMean χ c Y a (lemma81ConjugateSequence a)
  have ht : ‖Θ‖ ≤ ‖proposition71MainTerm D c a (lemma81ConjugateSequence a)‖+
      (C*proposition71ErrorScale D c a (lemma81ConjugateSequence a)+
        (ε/4)*lemma33ActualPrimeMass D) := by
    have h := norm_add_le (Θ-proposition71MainTerm D c a (lemma81ConjugateSequence a))
      (proposition71MainTerm D c a (lemma81ConjugateSequence a))
    rw [sub_add_cancel] at h
    linarith only [h,hp]
  have hsum : ‖M‖ ≤ (ε/2)*lemma33ActualPrimeMass D+2*‖Θ‖ := by
    have h := norm_add_le (M-Θ-conj Θ) (Θ+conj Θ)
    have hid : M-Θ-conj Θ+(Θ+conj Θ)=M := by ring
    rw [hid] at h
    have ht := norm_add_le Θ (conj Θ)
    rw [Complex.norm_conj] at ht
    linarith only [hm,h,ht]
  rw [he]
  apply (Complex.re_le_norm _).trans
  dsimp only [M] at hsum
  apply hsum.trans
  unfold proposition71ErrorScale at ht
  calc
    _ ≤ (ε/2)*lemma33ActualPrimeMass D+
        2*(‖proposition71MainTerm D c a (lemma81ConjugateSequence a)‖+
          (C*(lemma33ActualPrimeMass D*lemma23PaperL D^2*
            (∑ j : Fin 3, ‖proposition71ArithmeticSum D c j a (lemma81ConjugateSequence a)‖))+
            (ε/4)*lemma33ActualPrimeMass D)) := by gcongr
    _ ≤ (ε/2)*lemma33ActualPrimeMass D+
        2*((2/lemma44PaperAlpha D)*
          (∑ j : Fin 3, ‖proposition71ArithmeticSum D c j a (lemma81ConjugateSequence a)‖)*
            lemma33ActualPrimeMass D+
          (C*(lemma33ActualPrimeMass D*lemma23PaperL D^2*
            (∑ j : Fin 3, ‖proposition71ArithmeticSum D c j a (lemma81ConjugateSequence a)‖))+
            (ε/4)*lemma33ActualPrimeMass D)) := by gcongr
    _ = _ := by ring

end ZhangLS.Spec
