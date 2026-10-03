import ZhangLS.Spec.Proposition71PrincipalContourNumerator
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Set
open scoped Classical Topology
set_option maxHeartbeats 2500000

lemma proposition71_principal_quotient_eventually (D : ℕ) (β : Fin 3 → ℂ)
    (hβ : ∀j, (β j).re=0) (hinj : Function.Injective β)
    (d m : ℕ) (q : ℝ) (j : Fin 3) (hb : β j≠0) :
    (fun s => proposition71PrincipalContourNumerator D β d m q s/
      proposition71PrincipalPolePolynomial β s) =ᶠ[𝓝[≠] (1-β j)]
        proposition71PrincipalMellinIntegrand D β d m q := by
  have hp : ∀ᶠ s : ℂ in 𝓝 (1-β j), 0<s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp [hβ j])
  have h1 : ∀ᶠ s : ℂ in 𝓝 (1-β j), s≠1 :=
    continuousAt_id.eventually_ne (by
      intro he
      apply hb
      change 1-β j=1 at he
      linear_combination -he)
  have hne (k : Fin 3) : ∀ᶠ s : ℂ in 𝓝[≠] (1-β j), s≠1-β k := by
    by_cases hk : k=j
    · subst k
      exact self_mem_nhdsWithin
    · have he : 1-β j≠1-β k := by
        intro he
        apply hk
        apply hinj
        linear_combination he
      exact (continuousAt_id.eventually_ne he).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,h1.filter_mono nhdsWithin_le_nhds,
    hne 0,hne 1,hne 2] with s hs hs1 h0 h1 h2
  apply proposition71_principal_numerator_quotient D β hβ d m q hs hs1
  intro k
  fin_cases k <;> assumption

/-- All three derivative-quotient coefficients in the actual rectangle theorem
are the already defined punctured residues times the genuine finite factors. -/
theorem proposition71_principal_numerator_residue {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    {d : ℕ} (hd : d≠0) (m : ℕ) {q : ℝ} (hq : 0<q) (j : Fin 3) :
    proposition71PrincipalContourNumerator D (lemma83PaperBeta D c) d m q
        (1-lemma83PaperBeta D c j)/
      deriv (proposition71PrincipalPolePolynomial (lemma83PaperBeta D c))
        (1-lemma83PaperBeta D c j)=
      proposition71ActualR D c j*
        lemma83ModifiedKappa (lemma83PaperBeta D c) d m (1-lemma83PaperBeta D c j)*
        lemma83Lambda (lemma83PaperBeta D c) (d*m) (1-lemma83PaperBeta D c j)*
        (q : ℂ)^(1-lemma83PaperBeta D c j) := by
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hdata := section15_actual_shift_data hL3 hc hsmall
  have hR := (proposition71_actual_zeta_denominator_nonzero hL3 hc hsmall j).1
  have hN := proposition71_principal_numerator_analytic hD hL (lemma83PaperBeta D c)
    (lemma83_beta_re D c) hd m hq (s := 1-lemma83PaperBeta D c j)
    (by simp [lemma83_beta_re]) hR
  have hM := proposition71_principal_polynomial_analytic (lemma83PaperBeta D c)
    (1-lemma83PaperBeta D c j)
  have hzero : proposition71PrincipalPolePolynomial (lemma83PaperBeta D c)
      (1-lemma83PaperBeta D c j)=0 := by
    rw [proposition71_principal_polynomial_zeros]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have hsimple := proposition71_principal_polynomial_simple (lemma83PaperBeta D c) hdata.2 j
  have ht := lemma81_simple_zero_residue_tendsto hN.continuousAt hM.differentiableAt.hasDerivAt hzero hsimple
  have he := proposition71_principal_quotient_eventually D (lemma83PaperBeta D c)
    (lemma83_beta_re D c) hdata.2 d m q j (hdata.1 j)
  have ht' : Tendsto (fun s => (s-(1-lemma83PaperBeta D c j))*
      proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q s)
      (𝓝[≠] (1-lemma83PaperBeta D c j))
      (𝓝 (proposition71PrincipalContourNumerator D (lemma83PaperBeta D c) d m q
        (1-lemma83PaperBeta D c j)/
        deriv (proposition71PrincipalPolePolynomial (lemma83PaperBeta D c))
          (1-lemma83PaperBeta D c j))) := by
    apply ht.congr'
    filter_upwards [he] with s hs
    rw [hs]
  exact tendsto_nhds_unique ht'
    (proposition71_principal_integrand_residue_limit hD hL hc hsmall hd m hq j)

end ZhangLS.Spec
