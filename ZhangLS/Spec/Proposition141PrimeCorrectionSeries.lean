import ZhangLS.Spec.Proposition141PrincipalAttachment
import ZhangLS.Spec.Proposition71GaussDecomposition
import ZhangLS.Spec.CoprimeGaussPrimeAverage

/-! Absolute Δ₁ sums and the exact finite Gauss correction for arbitrary Section14 κ*. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

lemma proposition141_deltaOne_norm (D:ℕ) (x:ℝ) :
    ‖lemma53PaperDeltaOne D x‖=‖lemma53PaperDelta D x‖ := by
  unfold lemma53PaperDelta
  rw [norm_mul]
  have he : ‖Complex.exp ((2*Real.pi:ℂ)*I*(x:ℂ))‖=1 := by
    rw [Complex.norm_exp]
    simp
  rw [he,mul_one]

noncomputable def proposition141DeltaOneTerm (D:ℕ) (κ w:ℕ→ℂ) (d:ℕ) (q:ℝ) (m:ℕ) : ℂ :=
  if 0<m then κ (d*m)*w m*lemma53PaperDeltaOne D ((m:ℝ)/q) else 0

lemma proposition141_deltaOne_term_bound (D:ℕ) (κ w:ℕ→ℂ) (d:ℕ) (q A:ℝ)
    (hA:0≤A) (hw:∀m:ℕ,0<m→‖w m‖≤A) (m:ℕ) :
    ‖proposition141DeltaOneTerm D κ w d q m‖≤A*tauDeltaDilatedAbsolute D κ d q m := by
  unfold proposition141DeltaOneTerm tauDeltaDilatedAbsolute
  split_ifs with hm
  · rw [norm_mul,norm_mul,proposition141_deltaOne_norm]
    have hb := mul_le_mul_of_nonneg_left (hw m hm) (norm_nonneg (κ (d*m)))
    have hc := mul_le_mul_of_nonneg_right hb (norm_nonneg (lemma53PaperDelta D ((m:ℝ)/q)))
    convert hc using 1 <;> ring
  · simp

/-- Actual Δ₁ series with any proved bounded weight and all dilation factors. -/
theorem proposition141_actual_deltaOne_weighted_sum {D d:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) {κ w:ℕ→ℂ} {B A q:ℝ}
    (hB:0≤B) (hκ:Proposition141KappaBound B κ) (hA:0≤A)
    (hw:∀m:ℕ,0<m→‖w m‖≤A) (hd:0<d) (hq:1≤q) (hqP:q≤lemma23PaperP D^10) :
    Summable (proposition141DeltaOneTerm D κ w d q) ∧
      ‖∑'m:ℕ,proposition141DeltaOneTerm D κ w d q m‖≤
        A*tauDeltaAbsoluteConstant*B*(lemma34Tau 5 d:ℝ)*q*lemma23PaperL D^575 := by
  have ha := tauDelta_actual_dilated_absolute_sum hD hL κ hB hκ hd hq hqP
  have hb := proposition141_deltaOne_term_bound D κ w d q A hA hw
  have hs := Summable.of_norm_bounded (ha.1.mul_left A) hb
  refine ⟨hs,?_⟩
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  apply (hs.norm.tsum_le_tsum hb (ha.1.mul_left A)).trans
  rw [tsum_mul_left]
  have hh := mul_le_mul_of_nonneg_left ha.2 hA
  convert hh using 1 <;> ring

noncomputable def proposition141PrimePhase (D p n m:ℕ) : ℂ :=
  if hp:0<p then
    letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
    ZMod.stdAddChar ((m:ZMod p)*((D*n:ℕ):ZMod p)⁻¹)
  else 0

lemma proposition141_prime_phase_value {D p n m:ℕ} [NeZero p] :
    proposition141PrimePhase D p n m=
      ZMod.stdAddChar ((m:ZMod p)*((D*n:ℕ):ZMod p)⁻¹) := by
  unfold proposition141PrimePhase
  rw [dif_pos (Nat.pos_of_ne_zero (NeZero.ne p))]

lemma proposition141_prime_phase_norm (D p n m:ℕ) : ‖proposition141PrimePhase D p n m‖≤1 := by
  unfold proposition141PrimePhase
  split_ifs with hp
  · letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
    exact (proposition71_additive_character_norm _ _).le
  · simp

lemma proposition141_prime_correction_weight_norm (D p n m:ℕ) :
    ‖1-proposition141PrimePhase D p n m‖≤2 := by
  have hn := norm_sub_le (1:ℂ) (proposition141PrimePhase D p n m)
  have hp := proposition141_prime_phase_norm D p n m
  rw [norm_one] at hn
  linarith

/-- Genuine CRT χ-Gauss factor and all-m source signs, including the nonunit branch. -/
theorem proposition141_actual_normalized_gauss_decomposition {D p n:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (hp:p.Prime) (hcop:D.Coprime p)
    (hn:IsUnit ((D*n:ℕ):ZMod p)) (m:ℕ) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (∑ψ∈(univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ=>ψ.IsPrimitive),
      gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*
        ψ (m:ZMod p)*ψ⁻¹ (n:ZMod p))/(p:ℂ)=
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))*
        (proposition141PrimePhase D p n m+(p:ℂ)⁻¹*(1-proposition141PrimePhase D p n m)-
          if p∣m then 1 else 0) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  simp_rw [coprimeGauss_prime_average_summand χ hcop]
  rw [←mul_sum,mul_div_assoc]
  have hk:IsUnit ((D:ZMod p)*(n:ZMod p)) := by simpa only [Nat.cast_mul] using hn
  rw [proposition71_normalized_gauss_decomposition hp _ _ hk,proposition141_prime_phase_value]
  simp only [Nat.cast_mul,ZMod.natCast_eq_zero_iff m p]

end ZhangLS.Spec
