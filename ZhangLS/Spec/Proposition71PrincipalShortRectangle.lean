import ZhangLS.Spec.Proposition71PrincipalContourResidues
import ZhangLS.Spec.Proposition71PrincipalShortGeometry
import ZhangLS.Spec.Lemma84ContourBridge
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Set
open scoped Classical Topology
set_option maxHeartbeats 3500000

/-- Exact finite contour identity on the genuinely shorter H/2 rectangle.
The source integrand is used on every edge; its three actual residue values
are proved, and the totalized ζ value at 1 is never used inside the contour. -/
theorem proposition71_principal_short_rectangle_at_threshold :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → 2000≤lemma23PaperL D →
      ∀ c : ℝ, 0<c → c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 →
      ∀ d m : ℕ, d≠0 → ∀ q : ℝ, 0<q →
      lemma81RectangleIntegral (proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q)
        (1-1/lemma23PaperL D) (1+lemma44PaperAlpha D)
        (-proposition71ZetaAuxHeight D/2) (proposition71ZetaAuxHeight D/2)=
      2*(Real.pi : ℂ)*I*∑j : Fin 3,
        proposition71ActualR D c j*
          lemma83ModifiedKappa (lemma83PaperBeta D c) d m (1-lemma83PaperBeta D c j)*
          lemma83Lambda (lemma83PaperBeta D c) (d*m) (1-lemma83PaperBeta D c j)*
          (q : ℂ)^(1-lemma83PaperBeta D c j) := by
  obtain ⟨D₀,hD₀,hstrip⟩ := proposition71_zeta_auxiliary_strip
  refine ⟨D₀,hD₀,?_⟩
  intro D hDN hL c hc hsmall d m hd q hq
  have hD : 1<D := by omega
  let β := lemma83PaperBeta D c
  let a := 1-1/lemma23PaperL D
  let b := 1+lemma44PaperAlpha D
  let T := proposition71ZetaAuxHeight D/2
  let N := proposition71PrincipalContourNumerator D β d m q
  let M := proposition71PrincipalPolePolynomial β
  let S := proposition71PrincipalPoleSet β
  have hLp : 0<lemma23PaperL D := by linarith
  have hα := (proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)).1
  have hLi : 0<1/lemma23PaperL D := by positivity
  have hab : a<b := by dsimp [a,b]; linarith
  have hT : 0<T := div_pos (proposition71_zeta_aux_height_pos D) (by norm_num)
  have hdata := section15_actual_shift_data (by linarith : 3≤lemma23PaperL D) hc hsmall
  have hinside (j : Fin 3) : 1-β j∈Ioo a b ×ℂ Ioo (-T) T := by
    simpa only [β,a,b,T,neg_div] using proposition71_short_rectangle_pole_inside hL hc hsmall j
  have hmargin {s : ℂ} (hs : s∈Icc a b ×ℂ Icc (-T) T) :
      0<s.re ∧ s.re≤2 ∧ |s.im|≤proposition71ZetaAuxHeight D := by
    have hh := proposition71_short_rectangle_shift_margin hL hc hsmall
      (s := s) (by simpa only [a,b,T,neg_div] using hs)
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have hN : AnalyticOnNhd ℂ N (Icc a b ×ℂ Icc (-T) T) := by
    intro s hs
    have hmarg := hmargin hs
    have hR := ((hstrip D hDN).2.2 s hs.1.1 hmarg.2.1 hmarg.2.2).1
    exact proposition71_principal_numerator_analytic hD hL β (lemma83_beta_re D c) hd m hq hmarg.1 hR
  have hM : AnalyticOnNhd ℂ M (Icc a b ×ℂ Icc (-T) T) := fun s _ =>
    proposition71_principal_polynomial_analytic β s
  have hz (s : ℂ) (_hs : s∈Icc a b ×ℂ Icc (-T) T) : M s=0 ↔ s∈S :=
    proposition71_principal_polynomial_zeros β s
  have hi (ρ : ℂ) (hρ : ρ∈S) : ρ∈Ioo a b ×ℂ Ioo (-T) T := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hρ
    exact hinside j
  have hdM (ρ : ℂ) (hρ : ρ∈S) : deriv M ρ≠0 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hρ
    exact proposition71_principal_polynomial_simple β hdata.2 j
  have hrect := lemma81_finite_rectangle_residue_theorem N M S hab (by linarith : -T<T) hN hM hz hi hdM
  have hpi : Function.Injective (fun j : Fin 3 => 1-β j) := by
    intro j k he
    apply hdata.2
    dsimp [β] at he ⊢
    linear_combination -he
  have hsum : (∑ρ∈S,N ρ/deriv M ρ)=∑j : Fin 3,
      proposition71ActualR D c j*
        lemma83ModifiedKappa β d m (1-β j)*lemma83Lambda β (d*m) (1-β j)*
        (q : ℂ)^(1-β j) := by
    dsimp only [S,proposition71PrincipalPoleSet]
    rw [Finset.sum_image (fun j _ k _ he => hpi he)]
    apply Finset.sum_congr rfl
    intro j _
    exact proposition71_principal_numerator_residue hD hL hc hsmall hd m hq j
  have hboundary : EqOn (fun s => N s/M s) (proposition71PrincipalMellinIntegrand D β d m q)
      (lemma84RectangleBoundary a b T) := by
    intro s hs
    have hmarg := hmargin hs.1
    have hs1 : s≠1 := by
      intro he
      subst s
      rcases hs.2 with h | h | h | h
      · change (1 : ℝ)=a at h
        dsimp [a] at h
        linarith
      · change (1 : ℝ)=b at h
        dsimp [b] at h
        linarith
      · change (0 : ℝ)=-T at h
        linarith
      · change (0 : ℝ)=T at h
        linarith
    exact proposition71_principal_numerator_quotient D β (lemma83_beta_re D c) d m q hmarg.1 hs1
      (fun j => lemma84_boundary_ne_pole (hinside j) hs)
  have he := lemma84_boundary_integral_congr hab.le hT.le hboundary
  rw [←lemma84_rectangle_operator_eq,←lemma84_rectangle_operator_eq] at he
  rw [he,hsum] at hrect
  simpa only [β,a,b,T,neg_div] using hrect

/-- Uniform original-shift finite rectangle transfer, with a c-dependent
threshold and no zeta-zero, residue, or contour hypothesis. -/
theorem proposition71_actual_principal_short_rectangle {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ d m : ℕ, d≠0 → ∀ q : ℝ, 0<q →
      lemma81RectangleIntegral (proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q)
        (1-1/lemma23PaperL D) (1+lemma44PaperAlpha D)
        (-proposition71ZetaAuxHeight D/2) (proposition71ZetaAuxHeight D/2)=
      2*(Real.pi : ℂ)*I*∑j : Fin 3,
        proposition71ActualR D c j*
          lemma83ModifiedKappa (lemma83PaperBeta D c) d m (1-lemma83PaperBeta D c j)*
          lemma83Lambda (lemma83PaperBeta D c) (d*m) (1-lemma83PaperBeta D c j)*
          (q : ℂ)^(1-lemma83PaperBeta D c j) := by
  obtain ⟨N,hN,hrect⟩ := proposition71_principal_short_rectangle_at_threshold
  obtain ⟨K,_,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max N (max K ⌈Real.exp 2000⌉₊),hN.trans (le_max_left _ _),?_⟩
  intro D hD d m hd q hq
  have hND := (le_max_left _ _).trans hD
  have hKD := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  exact hrect D hND hL c hc (hsmall D hKD) d m hd q hq

end ZhangLS.Spec
