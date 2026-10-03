import ZhangLS.Spec.Proposition26ArithmeticInner
import ZhangLS.Spec.Proposition26OuterWeight

/-! Section 7 arithmetic norm assembly for actual χ-twisted BV profiles.
The only coefficient inputs still to attach are local Λ and the finite
μ*ξ harmonic envelope. No mean over zeros or final estimate is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex ComplexConjugate Finset
open scoped Classical

lemma proposition26_outer_coefficient_norm {D : ℕ} (c : ℝ) (j : Fin 3)
    {d r : ℕ} (hd : 0<d) (hr : 0<r) {K : ℝ}
    (hl : ‖lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j)‖≤K) :
    ‖(↑|ArithmeticFunction.moebius r|:ℂ)*
      lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j)/
        ((d:ℂ)*(r:ℂ)*(Nat.totient r:ℂ))‖ ≤
      K/((d:ℝ)*(r:ℝ)*(Nat.totient r:ℝ)) := by
  have hm : ‖(↑|ArithmeticFunction.moebius r|:ℂ)‖≤1 := by
    rcases ArithmeticFunction.moebius_eq_or r with h|h|h <;> rw [h] <;> norm_num
  simp only [norm_div,norm_mul,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (mul_le_mul hm hl (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)

/-- A purely scalar cancellation preserves both totient denominators: the
r/φ(r) from ξ combines with 1/(drφ(r)) to give 1/(dφ(r)^2). -/
lemma proposition26_totient_cancellation (K Q H : ℝ) {d r : ℕ}
    (hd : 0<d) (hr : 0<r) :
    (K/((d:ℝ)*(r:ℝ)*(Nat.totient r:ℝ)))*H*(H*(Q*(r:ℝ)/(Nat.totient r:ℝ))) =
      (K*Q*H^2)*(d:ℝ)⁻¹*((Nat.totient r:ℝ)⁻¹)^2 := by
  have hd0 : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hr0 : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  have hp0 : (Nat.totient r:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr hr).ne'
  field_simp

/-- The original S_j is bounded using actual χ cancellation and the finite
μ*ξ majorant. Every sequence, totient and source shift remains literal. -/
theorem proposition26_arithmetic_bv_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 8≤lemma23PaperL D) (c v : ℝ) (j : Fin 3)
    {w : ℕ→ℂ} {V : ℝ} (hw : Proposition26VariationBound w V)
    (hcut : ∀n:ℕ,lemma81Cutoff D≤(n:ℝ) → w n=0)
    (hfirst : ‖1-lemma83PaperBeta D c j+I*(v:ℂ)‖≤(D:ℝ))
    (hsecond : ‖1+I*((-v:ℝ):ℂ)‖≤(D:ℝ))
    (K Q : ℝ) (hK : 0≤K) (hQ : 0≤Q)
    (hlambda : ∀d∈lemma81PolynomialIndices D,∀r∈lemma81PolynomialIndices D,
      ‖lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j)‖≤K)
    (b : ℕ→ℕ→ℕ→ℂ)
    (hxi : ∀d∈lemma81PolynomialIndices D,∀r∈lemma81PolynomialIndices D,∀n:ℕ,0<n →
      lemma83Xi (lemma83PaperBeta D c) j n d r=
        ∑ab∈n.divisorsAntidiagonal,b d r ab.1)
    (hb : ∀d∈lemma81PolynomialIndices D,∀r∈lemma81PolynomialIndices D,
      (∑k∈Icc 1 ⌊lemma23PaperP D⌋₊,‖b d r k‖/(k:ℝ))≤Q*(r:ℝ)/(Nat.totient r:ℝ)) :
    ‖proposition71ArithmeticSum D c j (proposition26TwistedCoefficient χ v w)
      (lemma81ConjugateSequence (proposition26TwistedCoefficient χ v w))‖ ≤
      (K*Q*(((14*Real.exp 16+2)*lemma23PaperL D)*V)^2)*
        (1+Real.log (⌊lemma23PaperP D⌋₊:ℝ))*proposition26TotientSquareMass := by
  let H := ((14*Real.exp 16+2)*lemma23PaperL D)*V
  have hH : 0≤H := by dsimp [H]; positivity [hw.1]
  have hP : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (by positivity [hL])
  have hN : 1≤⌊lemma23PaperP D⌋₊ := (Nat.one_le_floor_iff _).mpr hP
  have hsub : lemma81PolynomialIndices D⊆Icc 1 ⌊lemma23PaperP D⌋₊ := by
    intro n hn
    have hm := (proposition71_mem_indices D n).mp hn
    exact mem_Icc.mpr ⟨hm.1,Nat.le_floor (hm.2.le.trans
      (lemma81_cutoff_le_P (by linarith : 3≤lemma23PaperL D)))⟩
  have houter := proposition26_outer_totient_sum (lemma81PolynomialIndices D) _ hN hsub
  unfold proposition71ArithmeticSum
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑d∈lemma81PolynomialIndices D, ∑r∈lemma81PolynomialIndices D,
        (K*Q*H^2)*(d:ℝ)⁻¹*((Nat.totient r:ℝ)⁻¹)^2 := by
      apply sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro r hr
      have hdp := ((proposition71_mem_indices D d).mp hd).1
      have hrp := ((proposition71_mem_indices D r).mp hr).1
      have hc : ‖χ.evalNat (d*r)‖≤1 := χ.evalNat_norm_le_one _
      have hF := proposition26_actual_first_inner_norm χ hD hL c v j hw hcut hfirst hdp hrp
      have hG := proposition26_actual_second_inner_norm χ hD hL c v j hw hcut hsecond hdp hrp
        (b d r) (hxi d hd r hr)
      have hF' : ‖∑ m∈lemma81PolynomialIndices D,
          proposition26TwistedCoefficient χ v w (d*r*m)/(m:ℂ)^(1-lemma83PaperBeta D c j)‖≤H := by
        apply hF.trans
        calc
          _ = ‖χ.evalNat (d*r)‖*H := by dsimp [H]; ring
          _ ≤ H := mul_le_of_le_one_left hH hc
      have hG' : ‖∑ n∈lemma81PolynomialIndices D,
          (lemma81ConjugateSequence (proposition26TwistedCoefficient χ v w)) (d*r*n)*
            lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ)‖≤H*(Q*(r:ℝ)/(Nat.totient r:ℝ)) := by
        apply hG.trans
        have hch : ‖χ.evalNat (d*r)‖*H≤H := mul_le_of_le_one_left hH hc
        exact mul_le_mul hch (hb d hd r hr)
          (sum_nonneg (fun n hn => by positivity)) hH
      have hwgt := proposition26_outer_coefficient_norm c j hdp hrp (hlambda d hd r hr)
      simp only [norm_mul]
      exact (mul_le_mul (mul_le_mul hwgt hF' (norm_nonneg _) (by positivity)) hG'
        (norm_nonneg _) (by positivity)).trans_eq
          (proposition26_totient_cancellation K Q H hdp hrp)
    _ = (K*Q*H^2)*(∑d∈lemma81PolynomialIndices D,∑r∈lemma81PolynomialIndices D,
        (d:ℝ)⁻¹*((Nat.totient r:ℝ)⁻¹)^2) := by
      simp only [Finset.mul_sum,mul_assoc]
    _ ≤ (K*Q*H^2)*((1+Real.log (⌊lemma23PaperP D⌋₊:ℝ))*proposition26TotientSquareMass) :=
      mul_le_mul_of_nonneg_left houter (by positivity)
    _ = _ := by dsimp [H]; ring

end ZhangLS.Spec
