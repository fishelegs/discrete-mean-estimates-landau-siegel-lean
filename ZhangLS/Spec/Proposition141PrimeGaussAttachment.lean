import ZhangLS.Spec.Proposition141PrimeCorrectionSaving
import ZhangLS.Spec.Proposition71NatMultiples

/-! Exact attachment of the literal primitive χψ Gauss source to the two bounded corrections. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition141_prime_short_unit {D p n:ℕ} (hD:1<D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) (hn:n∈proposition141Indices D) :
    (D*n).Coprime p ∧ D.Coprime p := by
  have hn' := (proposition141_mem_indices D n).mp hn
  have hp' := (lemma56_mem_paper_primes D p).mp hp
  have hD1:(1:ℝ)≤D := by exact_mod_cast (by omega : 1≤D)
  have hDsq:(D:ℝ)≤(D:ℝ)^2 := le_self_pow₀ hD1 (by norm_num)
  have hP4:0≤lemma61PaperP4 D := (lemma61_P4_pos hD).le
  have hcut:((D*n:ℕ):ℝ)<(p:ℝ) := by
    rw [Nat.cast_mul]
    calc
      _≤(D:ℝ)*(2*lemma61PaperP4 D) := mul_le_mul_of_nonneg_left hn'.2 (Nat.cast_nonneg _)
      _≤2*(D:ℝ)^2*lemma61PaperP4 D := by nlinarith
      _≤lemma23PaperP D := hmod
      _<_ := hp'.2.1
  have hlt:D*n<p := by exact_mod_cast hcut
  have hcop:p.Coprime (D*n) := hp'.1.coprime_iff_not_dvd.mpr (by
    intro hd
    exact (not_le_of_gt hlt) (Nat.le_of_dvd (Nat.mul_pos (by omega) hn'.1) hd))
  exact ⟨hcop.symm,hcop.symm.of_dvd_left (D.dvd_mul_right n)⟩

noncomputable def proposition141PrimeDivisibleTerm (D p n:ℕ) (κ:ℕ→ℂ) (m:ℕ) : ℂ :=
  if p∣m then proposition141DeltaOneTerm D κ (fun _=>1) 1 ((D:ℝ)*(p:ℝ)*(n:ℝ)) m else 0

lemma proposition141_divisible_reindexed {D p n:ℕ} (hp:0<p)
    (κ:ℕ→ℂ) (j:ℕ) :
    proposition141DeltaOneTerm D κ (fun _=>1) 1 ((D:ℝ)*(p:ℝ)*(n:ℝ)) (p*j)=
      proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)) j := by
  unfold proposition141DeltaOneTerm
  by_cases hj:0<j
  · rw [if_pos (Nat.mul_pos hp hj),if_pos hj,Nat.one_mul,mul_one]
    have hpr:(p:ℝ)≠0 := by exact_mod_cast hp.ne'
    congr 2
    push_cast
    field_simp
  · have hj0:j=0 := by omega
    subst j
    simp

/-- Exact sparse branch and its independent summability obligation. -/
theorem proposition141_divisible_original_sum {D p n:ℕ} (hp:0<p) (κ:ℕ→ℂ)
    (hs:Summable (proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)))) :
    Summable (proposition141PrimeDivisibleTerm D p n κ) ∧
      (∑'m:ℕ,proposition141PrimeDivisibleTerm D p n κ m)=
        ∑'j:ℕ,proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)) j := by
  have he:(fun j:ℕ=>proposition141DeltaOneTerm D κ (fun _=>1) 1
      ((D:ℝ)*(p:ℝ)*(n:ℝ)) (p*j))=
      proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)) :=
    funext (proposition141_divisible_reindexed hp κ)
  constructor
  · unfold proposition141PrimeDivisibleTerm
    rw [proposition71_nat_multiples_summable_iff hp,he]
    exact hs
  · unfold proposition141PrimeDivisibleTerm
    rw [proposition71_nat_multiples_tsum hp,he]

noncomputable def proposition141PrimeGaussSingle {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (n:ℕ) (κ:ℕ→ℂ) (m:ℕ) : ℂ :=
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  if 0<m then κ m*lemma53PaperDeltaOne D ((m:ℝ)/((D:ℝ)*(p:ℝ)*(n:ℝ)))*
    ((∑ψ∈(univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ=>ψ.IsPrimitive),
      gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*
        ψ (m:ZMod p)*ψ⁻¹ (n:ZMod p))/(p:ℂ)) else 0

/-- Pointwise source identity for arbitrary m, including m=0 and every p|m. -/
theorem proposition141_prime_gauss_single_identity {D p n:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (hD:1<D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) (hn:n∈proposition141Indices D) (κ:ℕ→ℂ) (m:ℕ) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    proposition141PrimeGaussSingle (p:=p) χ n κ m=
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))*
        (proposition141DeltaOneTerm D κ (proposition141PrimePhase D p n) 1
            ((D:ℝ)*(p:ℝ)*(n:ℝ)) m+
          (p:ℂ)⁻¹*proposition141DeltaOneTerm D κ (fun m=>1-proposition141PrimePhase D p n m) 1
            ((D:ℝ)*(p:ℝ)*(n:ℝ)) m-
          proposition141PrimeDivisibleTerm D p n κ m) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hu := proposition141_prime_short_unit hD hmod hp hn
  have hnunit:IsUnit ((D*n:ℕ):ZMod p) := by simpa only [ZMod.isUnit_iff_coprime] using hu.1
  have hpprime := ((lemma56_mem_paper_primes D p).mp hp).1
  unfold proposition141PrimeGaussSingle proposition141PrimeDivisibleTerm proposition141DeltaOneTerm
  by_cases hm:0<m
  · simp only [if_pos hm,Nat.one_mul]
    rw [proposition141_actual_normalized_gauss_decomposition χ hpprime hu.2 hnunit m]
    by_cases hpm:p∣m <;> simp only [hpm,if_true,if_false] <;> ring
  · simp only [if_neg hm,mul_zero,zero_add,ite_self,sub_self]

/-- Actual infinite Gauss sum identity, after all three series are proved summable. -/
theorem proposition141_prime_gauss_single_sum {D p n:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) (hn:n∈proposition141Indices D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    Summable (proposition141PrimeGaussSingle (p:=p) χ n κ) ∧
      (∑'m:ℕ,proposition141PrimeGaussSingle (p:=p) χ n κ m)=
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))*
        ((∑'m:ℕ,proposition141DeltaOneTerm D κ (proposition141PrimePhase D p n) 1
            ((D:ℝ)*(p:ℝ)*(n:ℝ)) m)+
          (p:ℂ)⁻¹*(∑'m:ℕ,proposition141DeltaOneTerm D κ (fun m=>1-proposition141PrimePhase D p n m) 1
            ((D:ℝ)*(p:ℝ)*(n:ℝ)) m)-
          ∑'j:ℕ,proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)) j) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hpprime := ((lemma56_mem_paper_primes D p).mp hp).1
  have hsc := proposition141_prime_correction_scales hD hL hmod hp hn
  have hA := (proposition141_actual_deltaOne_weighted_sum (w:=proposition141PrimePhase D p n)
    hD hL hB hκ (by norm_num : (0:ℝ)≤1) (fun m _=>proposition141_prime_phase_norm D p n m)
    (by norm_num : 0<(1:ℕ)) hsc.2.2.1 hsc.2.2.2).1
  have hC := proposition141_prime_correction_summable hD hL hmod hp hn hB hκ
  have hV := proposition141_divisible_original_sum hpprime.pos κ hC.2
  let F := fun m=>proposition141DeltaOneTerm D κ (proposition141PrimePhase D p n) 1
      ((D:ℝ)*(p:ℝ)*(n:ℝ)) m+
    (p:ℂ)⁻¹*proposition141DeltaOneTerm D κ (fun m=>1-proposition141PrimePhase D p n m) 1
      ((D:ℝ)*(p:ℝ)*(n:ℝ)) m-proposition141PrimeDivisibleTerm D p n κ m
  have hF:Summable F := (hA.add (hC.1.mul_left _)).sub hV.1
  have he:proposition141PrimeGaussSingle (p:=p) χ n κ=
      (fun m=>(gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))*F m) :=
    funext (proposition141_prime_gauss_single_identity χ hD hmod hp hn κ)
  refine ⟨he ▸ (hF.mul_left _),?_⟩
  rw [he,tsum_mul_left]
  apply congrArg ((gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))* ·)
  dsimp [F]
  rw [(hA.add (hC.1.mul_left _)).tsum_sub hV.1,hA.tsum_add (hC.1.mul_left _),tsum_mul_left,hV.2]

end ZhangLS.Spec
