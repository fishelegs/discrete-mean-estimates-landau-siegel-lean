import ZhangLS.Spec.PrimitiveConductorGaussBound
import ZhangLS.Spec.Proposition141OffDiagonal

/-! Exact principal and actual χ-induced removals from the full character
family, with conductor-one and off-diagonal branches retained literally. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition141_chi_induced_ne_principal {D N:ℕ} [NeZero N]
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hDN:D∣N) : χ.chi.changeLevel hDN≠1 := by
  intro h
  exact χ.nontrivial_of_one_lt_modulus hD ((DirichletCharacter.changeLevel_eq_one_iff hDN).mp h)

/-- Literal principal, χ-induced (only when D divides the actual level),
and remaining character contributions form an exact partition. -/
theorem proposition141_character_main_partition {D N:ℕ} [NeZero N]
    (χ:RealPrimitiveCharacter D) (hD:1<D) (F:DirichletCharacter ℂ N→ℂ) :
    (∑θ:DirichletCharacter ℂ N,F θ)=F 1+
      (if hDN:D∣N then F (χ.chi.changeLevel hDN) else 0)+
      ∑θ∈(univ:Finset (DirichletCharacter ℂ N)).filter
        (fun θ=>θ≠1 ∧ ∀hDN:D∣N,θ≠χ.chi.changeLevel hDN),F θ := by
  rw [sum_filter]
  by_cases hDN:D∣N
  · rw [dif_pos hDN]
    let η := χ.chi.changeLevel hDN
    have hη:η≠1 := proposition141_chi_induced_ne_principal χ hD hDN
    have hx (θ:DirichletCharacter ℂ N) : (∀h:D∣N,θ≠χ.chi.changeLevel h)↔θ≠η := by
      constructor
      · exact fun h=>h hDN
      · exact fun h _=>h
    simp_rw [hx]
    have hpoint (θ:DirichletCharacter ℂ N) : F θ=
        (if θ=1 then F θ else 0)+(if θ=η then F θ else 0)+
          (if θ≠1 ∧ θ≠η then F θ else 0) := by
      by_cases h1:θ=1
      · subst θ; simp [Ne.symm hη]
      · by_cases he:θ=η <;> simp [h1,he,hη]
    calc
      _=(∑θ:DirichletCharacter ℂ N,if θ=1 then F θ else 0)+
          (∑θ:DirichletCharacter ℂ N,if θ=η then F θ else 0)+
          ∑θ:DirichletCharacter ℂ N,if θ≠1 ∧ θ≠η then F θ else 0 := by
        rw [←sum_add_distrib,←sum_add_distrib]
        exact sum_congr rfl (fun θ _=>hpoint θ)
      _=_ := by simp [η]
  · rw [dif_neg hDN]
    simp only [hDN,IsEmpty.forall_iff,and_true,add_zero]
    have he := sum_erase_add (univ:Finset (DirichletCharacter ℂ N)) F (mem_univ 1)
    have hf : (univ:Finset (DirichletCharacter ℂ N)).filter (fun θ=>θ≠1)=univ.erase 1 := by
      ext θ
      simp [ne_comm]
    rw [←sum_filter,hf]
    exact he.symm.trans (add_comm _ _)

/-- The source D₁>1 coprimality condition rules out an actual χ-induced
term, so no main character is merely discarded in that branch. -/
theorem proposition141_off_diagonal_chi_term_zero {D D₁ D₂ k:ℕ} [NeZero (D₂*k)]
    (χ:RealPrimitiveCharacter D) (hDD:D=D₁*D₂) (hD₂:0<D₂) (hD₁:1<D₁)
    (hk:k.Coprime D₁) (F:DirichletCharacter ℂ (D₂*k)→ℂ) :
    (if hDN:D∣D₂*k then F (χ.chi.changeLevel hDN) else 0)=0 := by
  rw [dif_neg (proposition141_off_diagonal_not_dvd hDD hD₂ hD₁ hk.symm)]

end ZhangLS.Spec
