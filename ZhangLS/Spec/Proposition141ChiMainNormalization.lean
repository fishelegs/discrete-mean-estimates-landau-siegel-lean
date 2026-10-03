import ZhangLS.Spec.InducedGaussMainCharacters
import ZhangLS.Spec.Proposition141MainSeriesConvergence
import ZhangLS.Spec.Proposition141PrimeGaussAttachment

/-! Exact χ-induced source main term and its genuine real primitive Gauss
normalization. No k coprimality with D is added to the source sums. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

lemma proposition141_real_character_unit_square {D p:ℕ} (χ:RealPrimitiveCharacter D)
    (hp:p.Coprime D) : χ.chi (p:ZMod D)*χ.chi (p:ZMod D)=1 := by
  have hq := congrArg (fun θ:DirichletCharacter ℂ D=>θ (p:ZMod D)) χ.quadratic
  have hu:IsUnit (p:ZMod D) := (ZMod.isUnit_iff_coprime _ _).mpr hp
  simpa only [pow_two,MulChar.mul_apply,MulChar.one_apply hu] using hq

/-- The exact normalized χ-induced phase for every l, including nonunits.
The φ(Dk) denominator is converted by the proved vanishing χ(k) branch. -/
theorem proposition141_chi_induced_normalized_phase {D k p l:ℕ} [NeZero k]
    (χ:RealPrimitiveCharacter D) (hD:D≠1) (hp:p.Coprime (D*k)) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
    let θ := χ.chi.changeLevel (D.dvd_mul_right k)
    (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))/(D:ℂ)*
      (gaussSum θ⁻¹ ZMod.stdAddChar*θ (-(l:ZMod (D*k)))*conj (θ (p:ZMod (D*k))))/
        ((D*k).totient:ℂ)=
      ((ArithmeticFunction.moebius k:ℂ)*χ.chi (k:ZMod D))/
        ((D.totient:ℂ)*(k.totient:ℂ))*(if l.Coprime k then χ.chi (l:ZMod D) else 0) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
  dsimp only
  have hconj : conj ((χ.chi.changeLevel (D.dvd_mul_right k)) (p:ZMod (D*k)))=
      (χ.chi.changeLevel (D.dvd_mul_right k))⁻¹ (p:ZMod (D*k)) :=
    MulChar.star_apply' _ _
  rw [hconj]
  by_cases hl:l.Coprime k
  · rw [inducedGauss_real_phase_product χ p l (hp.of_dvd_right (k.dvd_mul_left D)) hl,if_pos hl]
    have hsq := inducedGauss_real_square χ hD
    have hp2 := proposition141_real_character_unit_square χ (hp.of_dvd_right (D.dvd_mul_right k))
    have hval : χ.chi (-(p:ZMod D)*(l:ZMod D))=
        χ.chi (-1:ZMod D)*χ.chi (p:ZMod D)*χ.chi (l:ZMod D) := by
      rw [←map_mul,←map_mul]
      congr 1
      ring
    rw [hval]
    calc
      _=((ArithmeticFunction.moebius k:ℂ)*χ.chi (k:ZMod D))/((D*k).totient:ℂ)*
          χ.chi (l:ZMod D)*
          ((χ.chi (-1:ZMod D)*(gaussSum χ.chi ZMod.stdAddChar)^2)/(D:ℂ))*
          (χ.chi (p:ZMod D)*χ.chi (p:ZMod D)) := by ring
      _=_ := by
        rw [hsq,div_self (by exact_mod_cast χ.modulus_ne_zero),hp2,mul_one,mul_one,
          inducedGauss_totient_denominator]
  · have hu:¬IsUnit (-(l:ZMod (D*k))) := by
      intro h
      have hu' : IsUnit (l:ZMod (D*k)) := by simpa only [neg_neg] using h.neg
      exact hl (((ZMod.isUnit_iff_coprime _ _).mp hu').of_dvd_right (k.dvd_mul_left D))
    rw [MulChar.map_nonunit _ hu,if_neg hl]
    simp

/-- Literal χ-induced character contribution, with positive l exactly as in
Section14 and its full Gauss factor before the exterior normalization. -/
noncomputable def proposition141ChiInducedInner {D:ℕ} (χ:RealPrimitiveCharacter D)
    (κ:ℕ→ℂ) (p d k:ℕ) : ℂ :=
  if hk:0<k then
    letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
    letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
    let θ := χ.chi.changeLevel (D.dvd_mul_right k)
    gaussSum θ⁻¹ ZMod.stdAddChar*
      ∑'l:ℕ+,κ (d*l)*θ (-((l:ℕ):ZMod (D*k)))*conj (θ (p:ZMod (D*k)))*
        lemma53PaperDelta D ((l:ℝ)/((D:ℝ)*(p:ℝ)*(k:ℝ)))
  else 0

/-- The full χ-induced row equals the original main row after the true
τχ²χ(-1)=D normalization, including k sharing prime factors with D. -/
theorem proposition141_chi_induced_normalized_row {D p d k:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:D≠1) (hk:0<k) (hp:p.Coprime (D*k))
    (κ a:ℕ→ℂ) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))/(D:ℂ)*
      ((d:ℂ)⁻¹*(a (d*k)/((k:ℂ)*((D*k).totient:ℂ)))*
        proposition141ChiInducedInner χ κ p d k)=
      (D.totient:ℂ)⁻¹*(d:ℂ)⁻¹*
        (((ArithmeticFunction.moebius k:ℂ)*χ.chi (k:ZMod D)*a (d*k))/
          ((k:ℂ)*(k.totient:ℂ))*proposition141InnerMain χ κ p d k) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
  unfold proposition141ChiInducedInner proposition141InnerMain
  rw [dif_pos hk]
  simp only
  simp_rw [←tsum_mul_left]
  apply tsum_congr
  intro l
  have he := proposition141_chi_induced_normalized_phase (l:=(l:ℕ)) χ hD hp
  try dsimp only at he
  by_cases hl:(l:ℕ).Coprime k
  · rw [if_pos hl] at he ⊢
    calc
      _=(d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*κ (d*l)*
          lemma53PaperDelta D ((l:ℝ)/((D:ℝ)*(p:ℝ)*(k:ℝ)))*
          ((gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))/(D:ℂ)*
            (gaussSum (χ.chi.changeLevel (D.dvd_mul_right k))⁻¹ ZMod.stdAddChar*
              (χ.chi.changeLevel (D.dvd_mul_right k)) (-((l:ℕ):ZMod (D*k)))*
              conj ((χ.chi.changeLevel (D.dvd_mul_right k)) (p:ZMod (D*k))))/
                ((D*k).totient:ℂ)) := by ring
      _=_ := by rw [he]; ring
  · rw [if_neg hl] at he ⊢
    have hz := congrArg (fun z:ℂ=>(d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*κ (d*l)*
      lemma53PaperDelta D ((l:ℝ)/((D:ℝ)*(p:ℝ)*(k:ℝ)))*z) he
    convert hz using 1 <;> ring

/-- The complete literal χ-induced contribution of the D₁=1 branch. -/
noncomputable def proposition141ChiInducedTotal {D:ℕ} (χ:RealPrimitiveCharacter D)
    (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  (gaussSum χ.chi ZMod.stdAddChar/(D:ℂ))*
    ∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
      ∑d∈proposition141Indices D,∑k∈proposition141Indices D,
        (d:ℂ)⁻¹*(a (d*k)/((k:ℂ)*((D*k).totient:ℂ)))*
          proposition141ChiInducedInner χ κ p d k

/-- Exact original main term, including the full prime weight and every
original d,k index. The source normalization is proved, not stipulated. -/
theorem proposition141_chi_induced_total_eq_main {D:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (β:ℂ) (κ a:ℕ→ℂ) :
    proposition141ChiInducedTotal χ β κ a=proposition141MainTerm χ β κ a := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  unfold proposition141ChiInducedTotal proposition141MainTerm
  simp only [mul_sum]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro k hk
  have hpp:p∈lemma56PaperPrimes D := by rw [←proposition141_prime_windows_equal]; exact hp
  have hcop:p.Coprime (D*k) := (proposition141_prime_short_unit hD hmod hpp hk).1.symm
  have he := proposition141_chi_induced_normalized_row (d:=d) χ (by omega)
    (proposition141_mem_indices D k |>.mp hk).1 hcop κ a
  try dsimp only at he
  calc
    _=proposition141ShiftWeight D p β*
        ((gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))/(D:ℂ)*
          ((d:ℂ)⁻¹*(a (d*k)/((k:ℂ)*((D*k).totient:ℂ)))*
            proposition141ChiInducedInner χ κ p d k)) := by ring
    _=_ := by rw [he]; ring

end ZhangLS.Spec
