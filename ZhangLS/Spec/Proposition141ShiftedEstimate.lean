import ZhangLS.Spec.Proposition141ComplexShift

/-! # Actual nonprincipal prime estimate for the full complex β disk

The real shift is treated by the proved finite Abel transformation. The
imaginary shift is retained in the height premise, and a separate D/2
corollary supplies honest room for it. These are prime estimates only;
no unproved Mellin-tail or averaged error is hidden in their hypotheses.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped ComplexConjugate

/-- Absolute shifted prime bound, from actual uniform sharp prime-log prefixes. -/
theorem proposition141_uniform_shifted_primitive_prime_absolute_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
      D₀≤D → 1<D → NormalizedAssumptionA χ → θ.IsPrimitive → 1<q →
      (q:ℝ)<lemma56PaperT D →
      (fun n : ℕ => θ (n:ZMod q)) ≠ (fun n : ℕ => χ.chi (n:ZMod D)) →
      ∀ β : ℂ, ‖β‖<5*lemma44PaperAlpha D → ∀ τ : ℝ, |τ+β.im|≤D →
        ‖proposition141ShiftedPrimeSum D θ β τ‖ ≤ C*lemma23PaperP D^2*
          Real.exp (-((7/6:ℝ)*lemma23PaperL D^(9/2:ℝ))) := by
  obtain ⟨Cp,hCp,Np,hprefix⟩ := lemma56_uniform_primitive_sharp_prime_log_window_bound
  obtain ⟨Nr,hr⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨4*Real.exp 40*Cp,by positivity,max Np Nr,?_⟩
  intro D q _ χ θ hDN hD hA hθ hq hqT hne β hβ τ hτ
  have hL := (hr D ((le_max_right Np Nr).trans hDN)).1
  let A := Cp*lemma23PaperP D*Real.exp (-((7/6:ℝ)*lemma23PaperL D^(9/2:ℝ)))
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hA0 : 0≤A := by dsimp [A]; positivity
  have hc : ∀ {x : ℝ}, 1≤x → x≤2*lemma23PaperP D →
      ‖lemma56SharpPrimeLogSum θ x (τ+β.im)‖ ≤ A := by
    intro x hx hxhi
    exact hprefix χ θ ((le_max_left Np Nr).trans hDN) hD hA hθ hq hqT hne hx hxhi hτ
  have hh := proposition141_actual_shifted_prime_weight_budget θ hL β hβ τ hA0 hc
  dsimp [A] at hh
  convert hh using 1 <;> ring

/-- Normalization is by the actual prime mass, not a substituted P² scale. -/
theorem proposition141_uniform_shifted_primitive_prime_normalized_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
      D₀≤D → 1<D → NormalizedAssumptionA χ → θ.IsPrimitive → 1<q →
      (q:ℝ)<lemma56PaperT D →
      (fun n : ℕ => θ (n:ZMod q)) ≠ (fun n : ℕ => χ.chi (n:ZMod D)) →
      ∀ β : ℂ, ‖β‖<5*lemma44PaperAlpha D → ∀ τ : ℝ, |τ+β.im|≤D →
        ‖proposition141ShiftedPrimeSum D θ β τ‖ ≤
          C*lemma56PrimeMass D*lemma56Decay D := by
  obtain ⟨Ca,hCa,Na,habs⟩ := proposition141_uniform_shifted_primitive_prime_absolute_bound
  obtain ⟨Nm,hmass⟩ := lemma56_uniform_actual_prime_mass_lower
  obtain ⟨Ns,hs⟩ := lemma56_uniform_actual_prime_mass_threshold
  refine ⟨4*Ca,by positivity,max Na (max Nm Ns),?_⟩
  intro D q _ χ θ hDN hD hA hθ hq hqT hne β hβ τ hτ
  have hL : 2000≤lemma23PaperL D := by
    have hh := (hs D ((le_max_right Nm Ns).trans ((le_max_right Na _).trans hDN))).1
    linarith
  have hL0 : 0<lemma23PaperL D := by linarith
  have hL77 : 0<lemma23PaperL D^77 := pow_pos hL0 _
  have hm := hmass χ ((le_max_left Nm Ns).trans ((le_max_right Na _).trans hDN)) hD hA
  have hm' : (1/4:ℝ)*lemma23PaperP D^2 ≤ lemma56PrimeMass D*lemma23PaperL D^77 :=
    (div_le_iff₀ hL77).mp hm
  have hratio : lemma23PaperP D^2 ≤ 4*lemma56PrimeMass D*lemma23PaperL D^77 := by
    nlinarith only [hm']
  have hdecay := lemma56_prime_mass_polynomial_absorption hL
  have hM : 0≤lemma56PrimeMass D := lemma56_prime_mass_nonneg D
  have he := habs χ θ ((le_max_left Na _).trans hDN) hD hA hθ hq hqT hne β hβ τ hτ
  calc
    _ ≤ Ca*lemma23PaperP D^2*Real.exp (-((7/6:ℝ)*lemma23PaperL D^(9/2:ℝ))) := he
    _ ≤ Ca*(4*lemma56PrimeMass D*lemma23PaperL D^77)*
        Real.exp (-((7/6:ℝ)*lemma23PaperL D^(9/2:ℝ))) := by gcongr
    _ = (4*Ca)*lemma56PrimeMass D*(lemma23PaperL D^77*
        Real.exp (-((7/6:ℝ)*lemma23PaperL D^(9/2:ℝ)))) := by ring
    _ ≤ (4*Ca)*lemma56PrimeMass D*Real.exp (-(lemma23PaperL D^(9/2:ℝ))) := by gcongr
    _ = _ := rfl

noncomputable def proposition141ShiftedProductPrimeSum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N) (β : ℂ) (τ : ℝ) : ℂ :=
  ∑ p ∈ lemma56PaperPrimes D, χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*
    (p:ℂ)^(1+I*(τ:ℂ)+β)

/-- The actual shifted χconjθ sum equals the primitive-inducer sum only
after establishing the prime-window unit condition. -/
theorem proposition141_shifted_product_prime_sum_eq_inducer {D N : ℕ} [NeZero N]
    (χ : RealPrimitiveCharacter D) (hd : D∣N) (θ : DirichletCharacter ℂ N)
    (hNP : (N:ℝ)≤lemma23PaperP D) (β : ℂ) (τ : ℝ) :
    proposition141ShiftedProductPrimeSum χ θ β τ =
      proposition141ShiftedPrimeSum D (proposition141PrimeCharacter χ hd θ).primitiveCharacter β τ := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpp,hpP,_⟩ := (lemma56_mem_paper_primes D p).mp hp
  have hNp : N<p := by exact_mod_cast hNP.trans_lt hpP
  have hc : p.Coprime N := hpp.coprime_iff_not_dvd.mpr (by
    intro hdiv
    exact (not_le_of_gt hNp) (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdiv))
  rw [proposition141_product_inducer_eval χ hd θ p hc]

/-- The original complex β disk is retained. The central height D/2 has
proved margin for Im β; the outer Mellin tail remains a separate obligation. -/
theorem proposition141_uniform_small_shifted_product_prime_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ {D N : ℕ} [NeZero N] (χ : RealPrimitiveCharacter D)
      (hd : D∣N) (θ : DirichletCharacter ℂ N),
      D₀≤D → NormalizedAssumptionA χ → (N:ℝ)≤lemma23PaperP D →
      θ≠1 → θ≠χ.chi.changeLevel hd → θ.conductor<D^3 →
      ∀ β : ℂ, ‖β‖<5*lemma44PaperAlpha D → ∀ τ : ℝ, |τ|≤(D:ℝ)/2 →
        ‖proposition141ShiftedProductPrimeSum χ θ β τ‖ ≤
          C*lemma56PrimeMass D*lemma56Decay D := by
  obtain ⟨C,hC,Nc,hbound⟩ := proposition141_uniform_shifted_primitive_prime_normalized_bound
  obtain ⟨Nt,hNt,hT⟩ := proposition141_uniform_fourth_lt_T
  obtain ⟨Nr,hr⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨C,hC,max Nc (max Nt Nr),hNt.trans ((le_max_left Nt Nr).trans (le_max_right _ _)),?_⟩
  intro D N _ χ hd θ hDN hA hNP hθ hne hcond β hβ τ hτ
  have hDt := (le_max_left Nt Nr).trans ((le_max_right Nc _).trans hDN)
  have hD2 : 2≤D := hNt.trans hDt
  have hL := (hr D ((le_max_right Nt Nr).trans ((le_max_right Nc _).trans hDN))).1
  have hb := proposition141_complex_shift_parameters hL hβ
  have hh : |τ+β.im|≤D := proposition141_shifted_height_margin hD2 (by linarith [hb.2.1]) hτ
  let ξ := proposition141PrimeCharacter χ hd θ
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  have hc := proposition141_actual_product_inducer_admissible χ hd θ hθ hne
  have hqT : (ξ.conductor:ℝ)<lemma56PaperT D := by
    have hf : (ξ.conductor:ℝ)<(D:ℝ)^4 := by
      exact_mod_cast proposition141_small_product_conductor_lt_fourth χ hd θ hcond
    exact hf.trans (hT D hDt)
  rw [proposition141_shifted_product_prime_sum_eq_inducer χ hd θ hNP β τ]
  exact hbound χ ξ.primitiveCharacter ((le_max_left Nc _).trans hDN)
    (by omega) hA hc.2.1 hc.1 hqT hc.2.2 β hβ τ hh

end ZhangLS.Spec
