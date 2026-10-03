import ZhangLS.Spec.Proposition71PrincipalEulerBounds
import ZhangLS.Spec.Proposition71ZetaRegularizedReciprocal
import ZhangLS.Spec.Lemma81FiniteRectangleResidues
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Set
open scoped Classical Topology
set_option maxHeartbeats 2500000

/-- The actual three distinct numerator poles. -/
noncomputable def proposition71PrincipalPoleSet (β : Fin 3 → ℂ) : Finset ℂ :=
  univ.image (fun j => 1-β j)

noncomputable def proposition71PrincipalPolePolynomial (β : Fin 3 → ℂ) (s : ℂ) : ℂ :=
  (s-(1-β 0))*(s-(1-β 1))*(s-(1-β 2))

/-- A genuine analytic numerator: all three numerator poles are removed, and
the reciprocal is regularized at s=1 rather than evaluating totalized ζ(1). -/
noncomputable def proposition71PrincipalContourNumerator (D : ℕ) (β : Fin 3 → ℂ)
    (d m : ℕ) (q : ℝ) (s : ℂ) : ℂ :=
  lemma83ModifiedKappa β d m s*lemma83Lambda β (d*m) s*(q : ℂ)^s*
    lemma54PaperDeltaMellin D s*proposition71RegularizedZetaReciprocal s*
    zetaPoleRemoved (s+β 0)*zetaPoleRemoved (s+β 1)*zetaPoleRemoved (s+β 2)

lemma proposition71_principal_polynomial_zeros (β : Fin 3 → ℂ) (s : ℂ) :
    proposition71PrincipalPolePolynomial β s=0 ↔ s∈proposition71PrincipalPoleSet β := by
  unfold proposition71PrincipalPolePolynomial proposition71PrincipalPoleSet
  simp only [mul_eq_zero,sub_eq_zero,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
  · rintro ⟨j,rfl⟩
    fin_cases j <;> simp

lemma proposition71_principal_polynomial_analytic (β : Fin 3 → ℂ) (s : ℂ) :
    AnalyticAt ℂ (proposition71PrincipalPolePolynomial β) s := by
  unfold proposition71PrincipalPolePolynomial
  fun_prop

lemma proposition71_principal_polynomial_deriv (β : Fin 3 → ℂ) (j : Fin 3) :
    deriv (proposition71PrincipalPolePolynomial β) (1-β j)=
      (β (j+1)-β j)*(β (j+2)-β j) := by
  have hh (s : ℂ) : HasDerivAt (proposition71PrincipalPolePolynomial β)
      ((s-(1-β 1))*(s-(1-β 2))+(s-(1-β 0))*(s-(1-β 2))+
        (s-(1-β 0))*(s-(1-β 1))) s := by
    convert (((hasDerivAt_id s).sub_const (1-β 0)).mul
      ((hasDerivAt_id s).sub_const (1-β 1))).mul
      ((hasDerivAt_id s).sub_const (1-β 2)) using 1 <;>
      (try simp only [id_eq,Pi.mul_apply]) <;> ring
  rw [(hh (1-β j)).deriv]
  fin_cases j
  · change ((1-β 0-(1-β 1))*(1-β 0-(1-β 2))+
      (1-β 0-(1-β 0))*(1-β 0-(1-β 2))+
      (1-β 0-(1-β 0))*(1-β 0-(1-β 1))) = (β 1-β 0)*(β 2-β 0)
    ring
  · change ((1-β 1-(1-β 1))*(1-β 1-(1-β 2))+
      (1-β 1-(1-β 0))*(1-β 1-(1-β 2))+
      (1-β 1-(1-β 0))*(1-β 1-(1-β 1))) = (β 2-β 1)*(β 0-β 1)
    ring
  · change ((1-β 2-(1-β 1))*(1-β 2-(1-β 2))+
      (1-β 2-(1-β 0))*(1-β 2-(1-β 2))+
      (1-β 2-(1-β 0))*(1-β 2-(1-β 1))) = (β 0-β 2)*(β 1-β 2)
    ring

lemma proposition71_principal_polynomial_simple (β : Fin 3 → ℂ) (hinj : Function.Injective β)
    (j : Fin 3) : deriv (proposition71PrincipalPolePolynomial β) (1-β j)≠0 := by
  rw [proposition71_principal_polynomial_deriv]
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (fun h => (show j+1≠j by fin_cases j <;> decide) (hinj h))
  · exact sub_ne_zero.mpr (fun h => (show j+2≠j by fin_cases j <;> decide) (hinj h))

lemma proposition71_principal_numerator_analytic {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (β : Fin 3 → ℂ) (hβ : ∀j, (β j).re=0)
    {d : ℕ} (hd : d≠0) (m : ℕ) {q : ℝ} (hq : 0<q) {s : ℂ}
    (hs : 0<s.re) (hR : zetaPoleRemoved s≠0) :
    AnalyticAt ℂ (proposition71PrincipalContourNumerator D β d m q) s := by
  have hZ (j : Fin 3) : AnalyticAt ℂ (fun z => zetaPoleRemoved (z+β j)) s :=
    (lemma55_actual_zeta_pole_removed_analyticAt (by simpa [hβ j] using hs)).comp
      (f := fun z : ℂ => z+β j) (x := s) (by fun_prop)
  exact (((((proposition71_principal_weight_analytic β hβ hd m hq hs).mul
    (lemma54_mellin_analyticOnNhd hD hL s hs)).mul
    (proposition71_regularized_zeta_reciprocal_analytic hs hR)).mul (hZ 0)).mul (hZ 1)).mul (hZ 2)

lemma proposition71_removed_shift_quotient (β s : ℂ) (hpos : 0<(s+β).re)
    (hne : s≠1-β) :
    zetaPoleRemoved (s+β)/(s-(1-β))=riemannZeta (s+β) := by
  have h0 : s+β≠0 := by intro h; rw [h] at hpos; simp at hpos
  have h1 : s+β≠1 := by intro h; apply hne; linear_combination h
  rw [zetaPoleRemoved_eq_mul_riemannZeta h0 h1,
    show s+β-1=s-(1-β) by ring,mul_div_cancel_left₀ _ (sub_ne_zero.mpr hne)]

/-- Agreement with the original integrand off its actual poles and s=1.
Only this boundary agreement will be used in the finite contour shift. -/
theorem proposition71_principal_numerator_quotient (D : ℕ) (β : Fin 3 → ℂ)
    (hβ : ∀j, (β j).re=0) (d m : ℕ) (q : ℝ) {s : ℂ}
    (hs : 0<s.re) (hs1 : s≠1) (hp : ∀ j : Fin 3, s≠1-β j) :
    proposition71PrincipalContourNumerator D β d m q s/proposition71PrincipalPolePolynomial β s=
      proposition71PrincipalMellinIntegrand D β d m q s := by
  have hs0 : s≠0 := by intro h; rw [h] at hs; simp at hs
  have hz (j : Fin 3) : zetaPoleRemoved (s+β j)/(s-(1-β j))=riemannZeta (s+β j) :=
    proposition71_removed_shift_quotient _ _ (by simpa [hβ j] using hs) (hp j)
  calc
    _=lemma83ModifiedKappa β d m s*lemma83Lambda β (d*m) s*(q : ℂ)^s*
        lemma54PaperDeltaMellin D s*proposition71RegularizedZetaReciprocal s*
        (zetaPoleRemoved (s+β 0)/(s-(1-β 0)))*
        (zetaPoleRemoved (s+β 1)/(s-(1-β 1)))*
        (zetaPoleRemoved (s+β 2)/(s-(1-β 2))) := by
      unfold proposition71PrincipalContourNumerator proposition71PrincipalPolePolynomial
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _=_ := by
      rw [hz 0,hz 1,hz 2,proposition71_regularized_zeta_reciprocal_eq hs0 hs1]
      unfold proposition71PrincipalMellinIntegrand
      ring

/-- At s=1 the genuine numerator vanishes, independently of any totalized ζ value. -/
lemma proposition71_principal_numerator_at_one (D : ℕ) (β : Fin 3 → ℂ)
    (d m : ℕ) (q : ℝ) : proposition71PrincipalContourNumerator D β d m q 1=0 := by
  simp [proposition71PrincipalContourNumerator,proposition71_regularized_zeta_reciprocal_at_one]

end ZhangLS.Spec
