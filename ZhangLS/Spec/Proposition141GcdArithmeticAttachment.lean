import ZhangLS.Spec.Proposition141OriginalAdditiveReduction
import ZhangLS.Spec.ReciprocalDeltaFiniteGcd

/-! Exact specialization of the genuine pair-gcd and additive-reciprocity
bijection to the original Dp front and closed Section14 support. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition141_closed_product_indices {D d k:ℕ} (hd:0<d) (hk:0<k)
    (hdk:d*k∈proposition141Indices D) : d∈proposition141Indices D ∧ k∈proposition141Indices D := by
  have hc := proposition141_mem_indices D (d*k) |>.mp hdk
  have hdd:d≤d*k := by nlinarith
  have hkd:k≤d*k := by nlinarith
  rw [proposition141_mem_indices,proposition141_mem_indices]
  exact ⟨⟨hd,(by exact_mod_cast hdd : (d:ℝ)≤((d*k:ℕ):ℝ)).trans hc.2⟩,
    ⟨hk,(by exact_mod_cast hkd : (k:ℝ)≤((d*k:ℕ):ℝ)).trans hc.2⟩⟩

lemma proposition141_additive_positive_series {D p n:ℕ} [NeZero p]
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) (hn:n∈proposition141Indices D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) :
    (∑'m:ℕ,proposition141DeltaOneTerm D κ (proposition141PrimePhase D p n) 1
      ((D:ℝ)*(p:ℝ)*(n:ℝ)) m)=
    ∑'m:ℕ+,κ (m:ℕ)*lemma53PaperDeltaOne D ((m:ℝ)/((D:ℝ)*(p:ℝ)*(n:ℝ)))*
      ZMod.stdAddChar ((m:ZMod p)*((D*n:ℕ):ZMod p)⁻¹) := by
  have hscl := proposition141_prime_correction_scales hD hL hmod hp hn
  have hs := (proposition141_actual_deltaOne_weighted_sum hD hL hB hκ
    (by norm_num : (0:ℝ)≤1) (fun m _=>proposition141_prime_phase_norm D p n m)
    (by norm_num : 0<(1:ℕ)) hscl.2.2.1 hscl.2.2.2).1
  have he : (∑'m:ℕ+,proposition141DeltaOneTerm D κ (proposition141PrimePhase D p n) 1
      ((D:ℝ)*(p:ℝ)*(n:ℝ)) (m:ℕ))=
      ∑'m:ℕ,proposition141DeltaOneTerm D κ (proposition141PrimePhase D p n) 1
        ((D:ℝ)*(p:ℝ)*(n:ℝ)) m := by
    simpa only [proposition141DeltaOneTerm,lt_self_iff_false,if_false,zero_add] using tsum_zero_pnat_eq_tsum_nat hs
  rw [←he]
  apply tsum_congr
  intro m
  rw [proposition141DeltaOneTerm,if_pos (show 0<(m:ℕ) from m.property)]
  simp only [Nat.one_mul,proposition141_prime_phase_value]
  ring

/-- Actual additive source attached to the genuine all-positive gcd mean. -/
theorem proposition141_additive_finite_gcd {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ}
    (hκ:Proposition141KappaBound B κ) (a:ℕ→ℂ) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    proposition141PrimeAdditiveArithmetic (p:=p) χ κ a=
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))/(D:ℂ)*
        reciprocalDeltaFiniteGcdMean D D p (proposition141Indices D) (proposition141Indices D) κ a := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  unfold proposition141PrimeAdditiveArithmetic
  congr 1
  have he := reciprocalDelta_source_finite_gcd hD hL χ.modulus_pos
    (proposition141Indices D) (proposition141Indices D)
    (fun n hn=>(proposition141_mem_indices D n |>.mp hn).1) κ a hB hκ
    (fun n hn=>(proposition141_prime_short_unit hD hmod hp hn).1.symm)
    (fun n hn=>⟨(proposition141_prime_correction_scales hD hL hmod hp hn).2.2.1,
      (proposition141_prime_correction_scales hD hL hmod hp hn).2.2.2⟩)
    (fun d k hd hk hdk=>proposition141_closed_product_indices hd hk hdk)
  rw [←he]
  apply sum_congr rfl
  intro n hn
  rw [proposition141_additive_positive_series hD hL hmod hp hn hB hκ]

noncomputable def proposition141ReciprocalInner (D p d k:ℕ) (κ:ℕ→ℂ) : ℂ :=
  ∑'l:ℕ+,if (l:ℕ).Coprime k then
    κ (d*l)*deltaReciprocalWeight p (l:ℕ) (D*k)*
      lemma53PaperDelta D ((l:ℝ)/((D:ℝ)*(p:ℝ)*(k:ℝ))) else 0

/-- The coefficient's actual closed support removes the generic d*k guard,
without discarding the boundary value a*(2P₄). -/
theorem proposition141_finite_gcd_literal {D p:ℕ} {Ba:ℝ} {a:ℕ→ℂ}
    (ha:Proposition141AdmissibleSequence D Ba a) (κ:ℕ→ℂ) :
    reciprocalDeltaFiniteGcdMean D D p (proposition141Indices D) (proposition141Indices D) κ a=
      ∑d∈proposition141Indices D,(d:ℂ)⁻¹*∑k∈proposition141Indices D,
        (a (d*k)/(k:ℂ))*proposition141ReciprocalInner D p d k κ := by
  unfold reciprocalDeltaFiniteGcdMean proposition141ReciprocalInner
  simp only [mul_sum]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro k hk
  have hd0 := (proposition141_mem_indices D d |>.mp hd).1
  have hk0 := (proposition141_mem_indices D k |>.mp hk).1
  rw [dif_pos hd0,dif_pos hk0,←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro l
  unfold reciprocalDeltaGcdTerm
  simp only [PNat.mk_coe]
  by_cases hdk:d*k∈proposition141Indices D
  · simp only [if_pos hdk]
    split_ifs <;> ring
  · have hz:a (d*k)=0 := ha.2 (d*k) (lt_of_not_ge (fun hb=>hdk
      ((proposition141_mem_indices D (d*k)).mpr ⟨Nat.mul_pos hd0 hk0,hb⟩)))
    simp only [if_neg hdk,hz,zero_div,zero_mul,mul_zero,ite_self]

noncomputable def proposition141ReciprocalGcdMean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  (gaussSum χ.chi ZMod.stdAddChar/(D:ℂ))*
    ∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
      ∑d∈proposition141Indices D,(d:ℂ)⁻¹*∑k∈proposition141Indices D,
        (a (d*k)/(k:ℂ))*proposition141ReciprocalInner D p d k κ

/-- Exactly the paper's (14.4) arithmetic source after both positive-pair
reindexing and reciprocal phase reduction, with no arithmetic error. -/
theorem proposition141_additive_reciprocal_gcd_mean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {B Ba:ℝ} (hB:0≤B) {κ a:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (ha:Proposition141AdmissibleSequence D Ba a) (β:ℂ) :
    proposition141AdditiveSourceMean χ β κ a=proposition141ReciprocalGcdMean χ β κ a := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  unfold proposition141AdditiveSourceMean proposition141ReciprocalGcdMean
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  have hpp:p∈lemma56PaperPrimes D := by rw [←proposition141_prime_windows_equal]; exact hp
  letI : NeZero p := ⟨(lemma56_mem_paper_primes D p |>.mp hpp).1.ne_zero⟩
  rw [proposition141_additive_finite_gcd χ hD hL hmod hpp hB hκ a,
    proposition141_finite_gcd_literal ha κ]
  ring

/-- The unchanged original Θ₂ is reduced to the literal (14.4) reciprocal
gcd mean, with the full original uniform quantifier order. -/
theorem proposition141_original_reciprocal_gcd_reduction (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
          ‖proposition141ThetaTwo χ β κ a-proposition141ReciprocalGcdMean χ β κ a‖≤
            ε*lemma33ActualPrimeMass D := by
  obtain ⟨N,hN,hfront⟩ := proposition141_original_additive_reduction Bκ Ba hBκ hBa ε hε
  obtain ⟨Ns,hNs,hmod⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max N (max Ns ⌈Real.exp 2000⌉₊)
  refine ⟨D₀,hN.trans (le_max_left _ _),?_⟩
  intro D hlarge χ hA κ a hκ ha β hβ
  have hND:N≤D := by dsimp [D₀] at hlarge; omega
  have hNsD:Ns≤D := by dsimp [D₀] at hlarge; omega
  have hNe:⌈Real.exp 2000⌉₊≤D := by dsimp [D₀] at hlarge; omega
  have hD:1<D := by have := hN.trans hND; omega
  have hL:2000≤lemma23PaperL D := by
    have he:Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  rw [←proposition141_additive_reciprocal_gcd_mean χ hD hL (hmod D hNsD) hBκ.le hκ ha β]
  exact hfront D hND χ hA κ a hκ ha β hβ

end ZhangLS.Spec
