import ZhangLS.Spec.Proposition141PrimeGaussAttachment

/-! Exact actual prime-Gauss arithmetic mean versus its source additive main term. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Arithmetic mean after the genuine Mellin/functional-equation Gauss transform. -/
noncomputable def proposition141PrimeGaussArithmetic {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (κ a:ℕ→ℂ) : ℂ :=
  (D:ℂ)⁻¹*∑n∈proposition141Indices D,(a n/(n:ℂ))*
    ∑'m:ℕ,proposition141PrimeGaussSingle (p:=p) χ n κ m

/-- Exactly the additive source expression before the gcd substitution in (14.4). -/
noncomputable def proposition141PrimeAdditiveArithmetic {D p:ℕ}
    (χ:RealPrimitiveCharacter D) (κ a:ℕ→ℂ) : ℂ :=
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))/(D:ℂ)*
    ∑n∈proposition141Indices D,(a n/(n:ℂ))*
      ∑'m:ℕ,proposition141DeltaOneTerm D κ (proposition141PrimePhase D p n) 1
        ((D:ℝ)*(p:ℝ)*(n:ℝ)) m

/-- Literal source difference, with exact two correction terms and no residual definition. -/
theorem proposition141_prime_source_corrections_identity {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ}
    (hκ:Proposition141KappaBound B κ) (a:ℕ→ℂ) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    proposition141PrimeGaussArithmetic (p:=p) χ κ a-
      proposition141PrimeAdditiveArithmetic (p:=p) χ κ a=
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))/(D:ℂ)*
        ((p:ℂ)⁻¹*proposition141PrimeSmallCorrection D p κ a-
          proposition141PrimeDivisibleCorrection D p κ a) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  let A := fun n=>∑'m:ℕ,proposition141DeltaOneTerm D κ (proposition141PrimePhase D p n) 1
    ((D:ℝ)*(p:ℝ)*(n:ℝ)) m
  let C := fun n=>∑'m:ℕ,proposition141DeltaOneTerm D κ (fun m=>1-proposition141PrimePhase D p n m) 1
    ((D:ℝ)*(p:ℝ)*(n:ℝ)) m
  let V := fun n=>∑'j:ℕ,proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)) j
  let τ := gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D)
  have hs : (∑n∈proposition141Indices D,(a n/(n:ℂ))*(∑'m:ℕ,proposition141PrimeGaussSingle (p:=p) χ n κ m))=
      τ*(∑n∈proposition141Indices D,(a n/(n:ℂ))*(A n+(p:ℂ)⁻¹*C n-V n)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [(proposition141_prime_gauss_single_sum χ hD hL hmod hp hn hB hκ).2]
    dsimp [τ,A,C,V]
    ring
  have hsplit : (∑n∈proposition141Indices D,(a n/(n:ℂ))*(A n+(p:ℂ)⁻¹*C n-V n))=
      (∑n∈proposition141Indices D,(a n/(n:ℂ))*A n)+
        (p:ℂ)⁻¹*proposition141PrimeSmallCorrection D p κ a-
          proposition141PrimeDivisibleCorrection D p κ a := by
    unfold proposition141PrimeSmallCorrection proposition141PrimeDivisibleCorrection
    rw [mul_sum,←sum_add_distrib,←sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    dsimp [C,V]
    ring
  unfold proposition141PrimeGaussArithmetic proposition141PrimeAdditiveArithmetic
  rw [hs,hsplit]
  dsimp [τ,A]
  ring

/-- Fully prime-summed arithmetic identity, with actual β and all χ-Gauss factors. -/
theorem proposition141_prime_source_total_identity {D:ℕ} (χ:RealPrimitiveCharacter D)
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (a:ℕ→ℂ) (β:ℂ) :
    (∑p∈lemma33PrimeWindow D,if hp:0<p then
      letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
      proposition141ShiftWeight D p β*(proposition141PrimeGaussArithmetic (p:=p) χ κ a-
        proposition141PrimeAdditiveArithmetic (p:=p) χ κ a) else 0)=
      proposition141PrimeFrontCorrectionTotal χ β κ a := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  unfold proposition141PrimeFrontCorrectionTotal
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  have hpp:p∈lemma56PaperPrimes D := by simpa only [proposition141_prime_windows_equal] using hp
  have hpos:0<p := ((lemma56_mem_paper_primes D p).mp hpp).1.pos
  letI : NeZero p := ⟨Nat.ne_of_gt hpos⟩
  rw [dif_pos hpos,proposition141_prime_source_corrections_identity χ hD hL hmod hpp hB hκ a]
  ring

/-- Negligibility of the actual source arithmetic difference, not merely a named majorant. -/
theorem proposition141_uniform_actual_prime_source_saving (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ‖∑p∈lemma33PrimeWindow D,if hp:0<p then
          letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
          proposition141ShiftWeight D p β*(proposition141PrimeGaussArithmetic (p:=p) χ κ a-
            proposition141PrimeAdditiveArithmetic (p:=p) χ κ a) else 0‖≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨N,hN2,hN⟩ := proposition141_uniform_prime_front_saving Bκ Ba hBκ hBa ε hε
  obtain ⟨Ns,hNs2,hNs⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max N (max Ns ⌈Real.exp 2000⌉₊)
  refine ⟨D₀,hN2.trans (le_max_left _ _),?_⟩
  intro D χ hlarge β hβ κ a hκ ha
  have hND:N≤D := by dsimp [D₀] at hlarge; omega
  have hNsD:Ns≤D := by dsimp [D₀] at hlarge; omega
  have hNe:⌈Real.exp 2000⌉₊≤D := by dsimp [D₀] at hlarge; omega
  have hD:1<D := by have := hN2.trans hND; omega
  have hL:2000≤lemma23PaperL D := by
    have hh:Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos _) hh
  rw [proposition141_prime_source_total_identity χ hD hL (hNs D hNsD) hBκ.le hκ]
  exact hN χ hND β hβ κ a hκ ha

/-- Expanded functional-equation Gauss denominator is exactly 1/(D*p). -/
theorem proposition141_prime_gauss_single_literal {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (n m:ℕ) (κ:ℕ→ℂ) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (D:ℂ)⁻¹*proposition141PrimeGaussSingle (p:=p) χ n κ m=
      if 0<m then ((D*p:ℕ):ℂ)⁻¹*κ m*
        lemma53PaperDeltaOne D ((m:ℝ)/((D:ℝ)*(p:ℝ)*(n:ℝ)))*
          (∑ψ∈(univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ=>ψ.IsPrimitive),
            gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*
              ψ (m:ZMod p)*ψ⁻¹ (n:ZMod p)) else 0 := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  unfold proposition141PrimeGaussSingle
  split_ifs
  · simp only [Nat.cast_mul,mul_inv_rev]
    ring
  · simp

/-- One uniform budget for the principal branch and both front Gauss corrections. -/
theorem proposition141_uniform_source_corrections_saving (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ‖proposition141PrincipalTotal χ β κ a+proposition141PrimeFrontCorrectionTotal χ β κ a‖≤
          ε*lemma33ActualPrimeMass D := by
  have hhalf:0<ε/2 := by positivity
  obtain ⟨Np,hNp2,hNp⟩ := proposition141_uniform_principal_saving Bκ Ba hBκ hBa (ε/2) hhalf
  obtain ⟨Nf,hNf2,hNf⟩ := proposition141_uniform_prime_front_saving Bκ Ba hBκ hBa (ε/2) hhalf
  refine ⟨max Np Nf,hNp2.trans (le_max_left _ _),?_⟩
  intro D χ hlarge β hβ κ a hκ ha
  have hp := hNp χ ((le_max_left _ _).trans hlarge) β hβ κ a hκ ha
  have hf := hNf χ ((le_max_right _ _).trans hlarge) β hβ κ a hκ ha
  exact (norm_add_le _ _).trans ((add_le_add hp hf).trans_eq (by ring))

end ZhangLS.Spec
