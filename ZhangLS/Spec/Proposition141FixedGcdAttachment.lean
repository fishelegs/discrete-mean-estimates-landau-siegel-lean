import ZhangLS.Spec.Proposition141GcdArithmeticAttachment
import ZhangLS.Spec.Proposition141FixedGcdFinite

/-! The actual fixed-D gcd split of the Section14 reciprocal source, with
its coefficient dilation and inverse phase transported without extra hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141FixedReciprocalInner (D D₁ D₂ p d k:ℕ) (κ:ℕ→ℂ) : ℂ :=
  ∑'l:ℕ+,if (l:ℕ).Coprime (D₂*k) then
    κ (D₁*d*l)*deltaReciprocalWeight p (l:ℕ) (D₂*k)*
      lemma53PaperDelta D ((l:ℝ)/((D₂:ℝ)*(p:ℝ)*(k:ℝ))) else 0

lemma proposition141_fixed_reciprocal_term {D D₁ p d k:ℕ} [NeZero D] [NeZero D₁] [NeZero k]
    (hdiv:D₁∣D) (hp:p.Coprime (D*k)) (κ:ℕ→ℂ) (l:ℕ) :
    κ (d*(D₁*l))*deltaReciprocalWeight p (D₁*l) (D*k)*
      lemma53PaperDelta D (((D₁*l:ℕ):ℝ)/((D:ℝ)*(p:ℝ)*(k:ℝ)))=
    κ (D₁*d*l)*deltaReciprocalWeight p l ((D/D₁)*k)*
      lemma53PaperDelta D ((l:ℝ)/(((D/D₁:ℕ):ℝ)*(p:ℝ)*(k:ℝ))) := by
  have hD0:0<D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hk0:0<k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hD₂:0<D/D₁ := fixedDGcd_divisor_quotient_pos hdiv
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne k)⟩
  letI : NeZero ((D/D₁)*k) := ⟨Nat.mul_ne_zero hD₂.ne' (NeZero.ne k)⟩
  simp only [deltaReciprocalWeight,dif_pos (Nat.mul_pos hD0 hk0),dif_pos (Nat.mul_pos hD₂ hk0)]
  rw [fixedDGcd_divisor_inverse_phase hdiv hp l,fixedDGcd_scaled_kernel_argument hdiv]
  rw [show d*(D₁*l)=D₁*d*l by ring]

/-- The literal sum over D₁|D and (D₁,k)=1 in the paper, before applying
character orthogonality at the now-coprime smaller modulus D₂*k. -/
theorem proposition141_reciprocal_fixed_gcd_split {D p d k:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) (hk:k∈proposition141Indices D) (hd:0<d)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) :
    proposition141ReciprocalInner D p d k κ=
      ∑D₁∈D.divisors,if k.Coprime D₁ then
        proposition141FixedReciprocalInner D D₁ (D/D₁) p d k κ else 0 := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hk0 := (proposition141_mem_indices D k |>.mp hk).1
  letI : NeZero k := ⟨hk0.ne'⟩
  let F := fun l:ℕ+=>κ (d*l)*deltaReciprocalWeight p (l:ℕ) (D*k)*
    lemma53PaperDelta D ((l:ℝ)/((D:ℝ)*(p:ℝ)*(k:ℝ)))
  have hscl := proposition141_prime_correction_scales hD hL hmod hp hk
  have hnorm (l:ℕ) (_:0<l) : ‖deltaReciprocalWeight p l (D*k)‖≤1 :=
    (deltaReciprocalWeight_norm p l (Nat.mul_pos χ.modulus_pos hk0)).le
  have hs := (tauDelta_actual_dilated_character_sum hD hL κ
    (fun l=>deltaReciprocalWeight p l (D*k)) hB hκ hnorm hd hscl.2.2.1 hscl.2.2.2).1
  have hsF:Summable F := by
    have hh := hs.subtype (fun l:ℕ=>0<l)
    apply hh.congr
    intro l
    dsimp only [Function.comp_apply,tauDeltaDilatedTerm,F]
    rw [if_pos l.property]
    rfl
  have hsFc := hsF.subtype (fun l:ℕ+=>(l:ℕ).Coprime k)
  unfold proposition141ReciprocalInner
  rw [proposition141_fixed_gcd_finite_tsum χ.modulus_pos k F hsFc]
  apply sum_congr rfl
  intro D₁ hD₁
  have hdiv := (Nat.mem_divisors.mp hD₁).1
  have hD₁0:0<D₁ := Nat.pos_of_dvd_of_pos hdiv χ.modulus_pos
  letI : NeZero D₁ := ⟨hD₁0.ne'⟩
  rw [dif_pos hD₁0]
  have hc:D₁.Coprime k↔k.Coprime D₁ := Nat.coprime_comm
  simp only [hc]
  by_cases hcop:k.Coprime D₁
  · rw [if_pos hcop,if_pos hcop]
    unfold proposition141FixedReciprocalInner
    apply tsum_congr
    intro l
    by_cases hl:(l:ℕ).Coprime ((D/D₁)*k)
    · rw [if_pos hl,if_pos hl]
      dsimp only [F,PNat.mul_coe]
      have he := proposition141_fixed_reciprocal_term (d:=d) hdiv
        (proposition141_prime_short_unit hD hmod hp hk).1.symm κ (l:ℕ)
      simpa only [Nat.cast_mul] using he
    · rw [if_neg hl,if_neg hl]
  · rw [if_neg hcop,if_neg hcop]

noncomputable def proposition141FixedGcdMean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  (gaussSum χ.chi ZMod.stdAddChar/(D:ℂ))*
    ∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
      ∑D₁∈D.divisors,∑d∈proposition141Indices D,∑k∈proposition141Indices D,
        if k.Coprime D₁ then (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*
          proposition141FixedReciprocalInner D D₁ (D/D₁) p d k κ else 0

/-- Complete literal fixed-D split, with every original exterior coefficient
and finite outer reordering accounted for. -/
theorem proposition141_reciprocal_fixed_gcd_mean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (a:ℕ→ℂ) (β:ℂ) :
    proposition141ReciprocalGcdMean χ β κ a=proposition141FixedGcdMean χ β κ a := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  unfold proposition141ReciprocalGcdMean proposition141FixedGcdMean
  congr 1
  apply sum_congr rfl
  intro p hp
  congr 1
  have hpp:p∈lemma56PaperPrimes D := by rw [←proposition141_prime_windows_equal]; exact hp
  let F := fun (D₁ d k:ℕ)=>if k.Coprime D₁ then (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*
    proposition141FixedReciprocalInner D D₁ (D/D₁) p d k κ else 0
  calc
    _=∑d∈proposition141Indices D,∑k∈proposition141Indices D,∑D₁∈D.divisors,F D₁ d k := by
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [proposition141_reciprocal_fixed_gcd_split χ hD hL hmod hpp hk
        (proposition141_mem_indices D d |>.mp hd).1 hB hκ,mul_sum,mul_sum]
      apply sum_congr rfl
      intro D₁ hD₁
      dsimp [F]
      split_ifs <;> ring
    _=∑d∈proposition141Indices D,∑D₁∈D.divisors,∑k∈proposition141Indices D,F D₁ d k := by
      apply sum_congr rfl
      intro d hd
      exact sum_comm
    _=_ := sum_comm

end ZhangLS.Spec
