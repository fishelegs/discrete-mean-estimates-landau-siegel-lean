import ZhangLS.Spec.TauWeightedDeltaCoefficients
import ZhangLS.Spec.InducedGaussMainCharacters
import ZhangLS.Spec.Proposition141GlobalShift
import ZhangLS.Spec.Proposition141NormalizedLargeAggregate
import ZhangLS.Spec.DivisorSmallPowerBudget

/-! Literal principal-character correction from (14.7), including general D₂.
The positive-index convention leaves κ(0) unrestricted. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate ArithmeticFunction.zeta

noncomputable def proposition141PrincipalWeight (N p l:ℕ) : ℂ :=
  (1:DirichletCharacter ℂ N) (-(l:ZMod N)) *
    conj ((1:DirichletCharacter ℂ N) (p:ZMod N))

noncomputable def proposition141PrincipalTerm (D D₁ D₂ p d k:ℕ) (κ:ℕ→ℂ) : ℕ→ℂ :=
  tauDeltaDilatedTerm D κ (proposition141PrincipalWeight (D₂*k) p)
    (D₁*d) ((D₂:ℝ)*(p:ℝ)*(k:ℝ))

noncomputable def proposition141PrincipalInner (D D₁ D₂ p d k:ℕ) (κ:ℕ→ℂ) : ℂ :=
  (ArithmeticFunction.moebius (D₂*k):ℂ) * ∑'l:ℕ,proposition141PrincipalTerm D D₁ D₂ p d k κ l

noncomputable def proposition141PrincipalRow (D D₁ D₂ p d k:ℕ) (κ a:ℕ→ℂ) : ℂ :=
  (d:ℂ)⁻¹ * (a (d*k) / ((k:ℂ)*(Nat.totient (D₂*k):ℂ))) *
    proposition141PrincipalInner D D₁ D₂ p d k κ

noncomputable def proposition141PrincipalCorrection (D D₁ D₂ p:ℕ) (κ a:ℕ→ℂ) : ℂ :=
  ∑d∈proposition141Indices D,∑k∈proposition141Indices D,
    if k.Coprime D₁ then proposition141PrincipalRow D D₁ D₂ p d k κ a else 0

lemma proposition141_principal_weight_norm (N p l:ℕ) :
    ‖proposition141PrincipalWeight N p l‖≤1 := by
  unfold proposition141PrincipalWeight
  rw [norm_mul,RCLike.norm_conj]
  exact (mul_le_mul ((1:DirichletCharacter ℂ N).norm_le_one _)
    ((1:DirichletCharacter ℂ N).norm_le_one _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- This is the actual Gauss summand with its negative-l and conjugated-p phases. -/
theorem proposition141_principal_literal_gauss {D D₁ D₂ p d k:ℕ} [NeZero (D₂*k)]
    (κ:ℕ→ℂ) :
    proposition141PrincipalInner D D₁ D₂ p d k κ =
      gaussSum (1:DirichletCharacter ℂ (D₂*k))⁻¹ ZMod.stdAddChar *
        ∑'l:ℕ,if 0<l then
          κ ((D₁*d)*l) *
            (1:DirichletCharacter ℂ (D₂*k)) (-(l:ZMod (D₂*k))) *
              conj ((1:DirichletCharacter ℂ (D₂*k)) (p:ZMod (D₂*k))) *
                lemma53PaperDelta D ((l:ℝ)/((D₂:ℝ)*(p:ℝ)*(k:ℝ))) else 0 := by
  unfold proposition141PrincipalInner
  rw [inv_one,inducedGauss_principal_value]
  apply congrArg ((ArithmeticFunction.moebius (D₂*k):ℂ) * ·)
  apply tsum_congr
  intro l
  simp only [proposition141PrincipalTerm,tauDeltaDilatedTerm,proposition141PrincipalWeight]
  split_ifs <;> ring

lemma proposition141_moebius_norm_le_one (N:ℕ) :
    ‖(ArithmeticFunction.moebius N:ℂ)‖≤1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=N))

/-- Absolute convergence and the complete D₁,d dilation factors. -/
theorem proposition141_principal_inner_bound {D D₁ D₂ p d k:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) {B:ℝ} (hB:0≤B)
    {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) (hD₁:0<D₁) (hd:0<d)
    (hq:1≤(D₂:ℝ)*(p:ℝ)*(k:ℝ))
    (hqP:(D₂:ℝ)*(p:ℝ)*(k:ℝ)≤lemma23PaperP D^10) :
    Summable (proposition141PrincipalTerm D D₁ D₂ p d k κ) ∧
      ‖proposition141PrincipalInner D D₁ D₂ p d k κ‖≤
        tauDeltaAbsoluteConstant*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*
          ((D₂:ℝ)*(p:ℝ)*(k:ℝ))*lemma23PaperL D^575 := by
  have hb := tauDelta_actual_dilated_character_sum hD hL κ
    (proposition141PrincipalWeight (D₂*k) p) hB hκ
    (fun l _=>proposition141_principal_weight_norm _ _ l) (Nat.mul_pos hD₁ hd) hq hqP
  refine ⟨hb.1,?_⟩
  have ht : (lemma34Tau 5 (D₁*d):ℝ)≤(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ) := by
    exact_mod_cast proposition71_tau_submultiplicative 5 D₁ d
  unfold proposition141PrincipalInner
  rw [norm_mul]
  calc
    _≤1*‖∑'l:ℕ,proposition141PrincipalTerm D D₁ D₂ p d k κ l‖ :=
      mul_le_mul_of_nonneg_right (proposition141_moebius_norm_le_one _) (norm_nonneg _)
    _≤tauDeltaAbsoluteConstant*B*(lemma34Tau 5 (D₁*d):ℝ)*
        ((D₂:ℝ)*(p:ℝ)*(k:ℝ))*lemma23PaperL D^575 := by simpa using hb.2
    _≤_ := by
      have := tauDelta_absolute_constant_pos.le
      calc
        _≤tauDeltaAbsoluteConstant*B*((lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))*
          ((D₂:ℝ)*(p:ℝ)*(k:ℝ))*lemma23PaperL D^575 := by gcongr
        _=_ := by ring

/-- All original scalar weights, including φ(D₂k), have been paid for. -/
theorem proposition141_principal_row_bound {D D₁ D₂ p d k:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) {Bκ Ba:ℝ} (hBκ:0≤Bκ) (hBa:0≤Ba)
    {κ a:ℕ→ℂ} (hκ:Proposition141KappaBound Bκ κ)
    (ha:Proposition141AdmissibleSequence D Ba a) (hD₁:0<D₁) (hD₂:0<D₂)
    (hd:0<d) (hk:0<k) (hq:1≤(D₂:ℝ)*(p:ℝ)*(k:ℝ))
    (hqP:(D₂:ℝ)*(p:ℝ)*(k:ℝ)≤lemma23PaperP D^10) :
    ‖proposition141PrincipalRow D D₁ D₂ p d k κ a‖≤
      (tauDeltaAbsoluteConstant*Bκ*Ba*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 2 D₂:ℝ)*
        (p:ℝ)*lemma23PaperL D^575)*
          ((lemma34Tau 5 d:ℝ)/(d:ℝ))*((lemma34Tau 2 k:ℝ)/(k:ℝ)) := by
  have hi := (proposition141_principal_inner_bound hD hL hBκ hκ hD₁ hd hq hqP).2
  have ht := proposition71_reciprocal_product_totient hD₂ hk
  have hc := tauDelta_absolute_constant_pos.le
  have hdp:0<(d:ℝ) := by exact_mod_cast hd
  have hkp:0<(k:ℝ) := by exact_mod_cast hk
  have hD₂p:0<(D₂:ℝ) := by exact_mod_cast hD₂
  unfold proposition141PrincipalRow
  rw [norm_mul,norm_mul,norm_inv,norm_div,norm_mul,Complex.norm_natCast,
    Complex.norm_natCast,Complex.norm_natCast]
  calc
    _≤(d:ℝ)⁻¹*(Ba/((k:ℝ)*(Nat.totient (D₂*k):ℝ)))*
        (tauDeltaAbsoluteConstant*Bκ*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*
          ((D₂:ℝ)*(p:ℝ)*(k:ℝ))*lemma23PaperL D^575) := by
      gcongr
      exact ha.1 _ (Nat.mul_pos hd hk)
    _=(d:ℝ)⁻¹*(Ba/(k:ℝ))*(Nat.totient (D₂*k):ℝ)⁻¹*
        (tauDeltaAbsoluteConstant*Bκ*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*
          ((D₂:ℝ)*(p:ℝ)*(k:ℝ))*lemma23PaperL D^575) := by ring
    _≤(d:ℝ)⁻¹*(Ba/(k:ℝ))*
        ((lemma34Tau 2 D₂:ℝ)*(lemma34Tau 2 k:ℝ)/((D₂:ℝ)*(k:ℝ)))*
        (tauDeltaAbsoluteConstant*Bκ*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*
          ((D₂:ℝ)*(p:ℝ)*(k:ℝ))*lemma23PaperL D^575) := by gcongr
    _=_ := by field_simp

end ZhangLS.Spec
