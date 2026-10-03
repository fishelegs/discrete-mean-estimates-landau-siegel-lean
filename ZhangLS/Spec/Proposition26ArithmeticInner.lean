import ZhangLS.Spec.Proposition26ConvolutionBV
import ZhangLS.Spec.Lemma81ActualPolynomialMoments

/-! Exact strict-index attachment for the two actual Section 7 arithmetic
inner sums. The positive χ(dr) factors are retained in the norm bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex ComplexConjugate Finset
open scoped Classical

lemma proposition26_strict_indices_extend {D : ℕ} {B : ℝ}
    (hL : 3≤lemma23PaperL D) (a : ℕ→ℂ) (ha : Lemma81AdmissibleSequence D B a)
    {q : ℕ} (hq : 0<q) (F : ℕ→ℂ) :
    (∑ n∈lemma81PolynomialIndices D,a (q*n)*F n)=
      ∑ n∈Icc 1 ⌊lemma23PaperP D⌋₊,a (q*n)*F n := by
  have hsub : lemma81PolynomialIndices D⊆Icc 1 ⌊lemma23PaperP D⌋₊ := by
    intro n hn
    have hm := (proposition71_mem_indices D n).mp hn
    exact mem_Icc.mpr ⟨hm.1,Nat.le_floor (hm.2.le.trans (lemma81_cutoff_le_P hL))⟩
  apply sum_subset hsub
  intro n hn hnot
  have hge : lemma81Cutoff D≤(n:ℝ) := by
    by_contra h
    exact hnot ((proposition71_mem_indices D n).mpr
      ⟨(mem_Icc.mp hn).1,lt_of_not_ge h⟩)
  have hqn : (n:ℝ)≤((q*n:ℕ):ℝ) := by exact_mod_cast Nat.le_mul_of_pos_left n hq
  rw [ha.2 (q*n) (hge.trans hqn),zero_mul]

/-- The exact first source factor over its original strict index set. -/
theorem proposition26_actual_first_inner_norm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1<D) (hL : 8≤lemma23PaperL D)
    (c v : ℝ) (j : Fin 3) {w : ℕ→ℂ} {V : ℝ}
    (hw : Proposition26VariationBound w V)
    (hcut : ∀n:ℕ,lemma81Cutoff D≤(n:ℝ) → w n=0)
    (hs : ‖1-lemma83PaperBeta D c j+I*(v:ℂ)‖≤(D:ℝ))
    {d r : ℕ} (hd : 0<d) (hr : 0<r) :
    ‖∑ m∈lemma81PolynomialIndices D,
      proposition26TwistedCoefficient χ v w (d*r*m)/(m:ℂ)^(1-lemma83PaperBeta D c j)‖ ≤
      ‖χ.evalNat (d*r)‖*((14*Real.exp 16+2)*lemma23PaperL D)*V := by
  have ha := proposition26_twisted_coefficient_admissible χ v hw hcut
  have he := proposition26_strict_indices_extend (by linarith : 3≤lemma23PaperL D)
    _ ha (Nat.mul_pos hd hr) (fun m => ((m:ℂ)^(1-lemma83PaperBeta D c j))⁻¹)
  simp only [←div_eq_mul_inv] at he
  rw [he]
  exact proposition26_twisted_first_inner χ hD hL v hw _ (lemma83_beta_re D c j) hs
    (Nat.mul_pos hd hr) _

/-- Exact finite convolution attachment for a twisted profile, before any
bound for b is introduced. -/
theorem proposition26_twisted_convolution_inner {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1<D) (hL : 8≤lemma23PaperL D)
    (v : ℝ) {w : ℕ→ℂ} {V : ℝ} (hw : Proposition26VariationBound w V)
    (hs : ‖1+I*(v:ℂ)‖≤(D:ℝ)) (b ξ : ℕ→ℂ)
    (hξ : ∀n:ℕ,0<n → ξ n=∑ab∈n.divisorsAntidiagonal,b ab.1)
    {q : ℕ} (hq : 0<q) (N : ℕ) :
    ‖∑ n∈Icc 1 N,proposition26TwistedCoefficient χ v w (q*n)*ξ n/(n:ℂ)‖ ≤
      ‖χ.evalNat q‖*(((14*Real.exp 16+2)*lemma23PaperL D)*V)*
        (∑ k∈Icc 1 N,‖b k‖/(k:ℝ)) := by
  have he : (∑ n∈Icc 1 N,proposition26TwistedCoefficient χ v w (q*n)*ξ n/(n:ℂ))=
      (χ.evalNat q*(q:ℂ)^(-I*(v:ℂ)))*
        (∑ n∈Icc 1 N,ξ n*(χ.evalNat n*(n:ℂ)^(-(1+I*(v:ℂ))))*w (q*n)) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro n hn
    have ht := proposition26_twisted_first_term χ v w 0 hq (mem_Icc.mp hn).1
    simp only [sub_zero,Complex.cpow_one] at ht
    calc
      _ = (proposition26TwistedCoefficient χ v w (q*n)/(n:ℂ))*ξ n := by ring
      _ = _ := by rw [ht]; ring
  have hb := proposition26_convolution_profile_norm χ hD hL
    (s:=1+I*(v:ℂ)) (by simp) hs hw b ξ hq N hξ
  have hp : ‖(q:ℂ)^(-I*(v:ℂ))‖=1 := by rw [Complex.norm_natCast_cpow_of_pos hq]; simp
  rw [he,norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)

/-- The original second factor, including inverse frequency, conjugated
profile, actual ξ, the strict cutoff and its χ(dr) factor. -/
theorem proposition26_actual_second_inner_norm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1<D) (hL : 8≤lemma23PaperL D)
    (c v : ℝ) (j : Fin 3) {w : ℕ→ℂ} {V : ℝ}
    (hw : Proposition26VariationBound w V)
    (hcut : ∀n:ℕ,lemma81Cutoff D≤(n:ℝ) → w n=0)
    (hs : ‖1+I*((-v:ℝ):ℂ)‖≤(D:ℝ))
    {d r : ℕ} (hd : 0<d) (hr : 0<r) (b : ℕ→ℂ)
    (hξ : ∀n:ℕ,0<n → lemma83Xi (lemma83PaperBeta D c) j n d r=
      ∑ab∈n.divisorsAntidiagonal,b ab.1) :
    ‖∑ n∈lemma81PolynomialIndices D,
      (lemma81ConjugateSequence (proposition26TwistedCoefficient χ v w)) (d*r*n)*
        lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ)‖ ≤
      ‖χ.evalNat (d*r)‖*(((14*Real.exp 16+2)*lemma23PaperL D)*V)*
        (∑ k∈Icc 1 ⌊lemma23PaperP D⌋₊,‖b k‖/(k:ℝ)) := by
  have hconj := proposition26_conjugate_variation hw
  have hcut' : ∀n:ℕ,lemma81Cutoff D≤(n:ℝ) → conj (w n)=0 := by
    intro n hn
    simp only [hcut n hn,map_zero]
  have ha := proposition26_twisted_coefficient_admissible χ (-v) hconj hcut'
  rw [proposition26_twisted_coefficient_conjugate]
  have he := proposition26_strict_indices_extend (by linarith : 3≤lemma23PaperL D)
    _ ha (Nat.mul_pos hd hr)
    (fun n => lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ))
  simp only [←mul_div_assoc] at he
  rw [he]
  exact proposition26_twisted_convolution_inner χ hD hL (-v) hconj hs b _ hξ
    (Nat.mul_pos hd hr) _

end ZhangLS.Spec
