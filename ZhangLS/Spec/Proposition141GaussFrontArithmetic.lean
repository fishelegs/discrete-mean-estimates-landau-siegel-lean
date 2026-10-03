import ZhangLS.Spec.Proposition141OriginalGaussReduction
import ZhangLS.Spec.Proposition141PrimeSourceMean

/-! Exact finite-family and absolutely-convergent-series attachment of the
original functional-equation front to the literal prime Gauss arithmetic. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition141_actual_family_primitive_sum {D:ℕ} (f:lemma33CharacterIndex D→ℂ) :
    (∑ψ∈lemma33ActualFamily D,f ψ)=
      ∑p:lemma33PrimeIndex D,∑ψ∈(univ:Finset (DirichletCharacter ℂ p.val)).filter
        (fun ψ=>ψ.IsPrimitive),f ⟨p,ψ⟩ := by
  unfold lemma33ActualFamily
  rw [sum_filter]
  change (∑ψ:Σp:lemma33PrimeIndex D,DirichletCharacter ℂ p.val,
    if Lemma23InPsi (D:=D) ψ.2 then f ψ else 0)=_
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro p hp
  rw [sum_filter]
  apply sum_congr rfl
  intro ψ hψ
  have hwin := lemma33_mem_prime_window.mp p.property
  simp only [Lemma23InPsi,hwin.1,hwin.2.1,hwin.2.2,and_true,true_and]

lemma proposition141_front_character_series_summable {D p n:ℕ}
    (ψ:DirichletCharacter ℂ p) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) (hn:n∈proposition141Indices D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) :
    Summable (proposition141DeltaOneTerm D κ (fun m=>ψ (m:ZMod p)) 1
      ((D:ℝ)*(p:ℝ)*(n:ℝ))) := by
  have hscale := proposition141_prime_correction_scales hD hL hmod hp hn
  exact (proposition141_actual_deltaOne_weighted_sum hD hL hB hκ
    (by norm_num : (0:ℝ)≤1) (fun m _=>ψ.norm_le_one _) (by norm_num : 0<(1:ℕ))
    hscale.2.2.1 hscale.2.2.2).1

/-- Finite-short expansion of the actual front, justified for each original
character by a proved absolutely convergent positive-index series. -/
theorem proposition141_gauss_front_character_expansion {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (ψ:DirichletCharacter ℂ p)
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ}
    (hκ:Proposition141KappaBound B κ) (a:ℕ→ℂ) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    proposition141GaussDeltaOneTerm χ κ a ψ=
      ∑n∈proposition141Indices D,
        (gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar/((D*p:ℕ):ℂ))*
          (a n*ψ⁻¹ (n:ZMod p)/(n:ℂ))*
            ∑'m:ℕ,proposition141DeltaOneTerm D κ (fun m=>ψ (m:ZMod p)) 1
              ((D:ℝ)*(p:ℝ)*(n:ℝ)) m := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let G := fun (n m:ℕ)=>proposition141DeltaOneTerm D κ (fun m=>ψ (m:ZMod p)) 1
    ((D:ℝ)*(p:ℝ)*(n:ℝ)) m
  have hs (n:ℕ) (hn:n∈proposition141Indices D) : Summable (G n) :=
    proposition141_front_character_series_summable ψ hD hL hmod hp hn hB hκ
  have he (m:ℕ) : proposition71DeltaOneDoubleTerm D (fun m=>κ m*ψ (m:ZMod p))
      (proposition141Indices D) (fun n=>a n*ψ⁻¹ (n:ZMod p)) ((D*p:ℕ):ℝ) m=
      ∑n∈proposition141Indices D,(a n*ψ⁻¹ (n:ZMod p)/(n:ℂ))*G n m := by
    by_cases hm:m=0
    · subst m; simp [proposition71DeltaOneDoubleTerm,G,proposition141DeltaOneTerm]
    · have hmpos:0<m := Nat.pos_of_ne_zero hm
      simp only [proposition71DeltaOneDoubleTerm,if_neg hm,G,proposition141DeltaOneTerm,
        if_pos hmpos,Nat.one_mul,Nat.cast_mul,mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
  unfold proposition141GaussDeltaOneTerm
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun n hn=>(hs n hn).mul_left _)]
  simp only [tsum_mul_left,mul_sum,mul_assoc,G]

/-- Exact averaging over the genuine primitive prime family. No m-unit
restriction is imposed and all zero/nonunit branches remain in the source. -/
theorem proposition141_gauss_front_prime_arithmetic {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ}
    (hκ:Proposition141KappaBound B κ) (a:ℕ→ℂ) :
    (∑ψ∈(univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ=>ψ.IsPrimitive),
      proposition141GaussDeltaOneTerm χ κ a ψ)=proposition141PrimeGaussArithmetic (p:=p) χ κ a := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let S := (univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ=>ψ.IsPrimitive)
  let G := fun (ψ:DirichletCharacter ℂ p) (n m:ℕ)=>
    proposition141DeltaOneTerm D κ (fun m=>ψ (m:ZMod p)) 1 ((D:ℝ)*(p:ℝ)*(n:ℝ)) m
  let C := fun (ψ:DirichletCharacter ℂ p) (n:ℕ)=>
    (gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar/((D*p:ℕ):ℂ))*
      (a n*ψ⁻¹ (n:ZMod p)/(n:ℂ))
  simp_rw [proposition141_gauss_front_character_expansion χ _ hD hL hmod hp hB hκ a]
  rw [sum_comm]
  unfold proposition141PrimeGaussArithmetic
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  change (∑ψ∈S,C ψ n*(∑'m:ℕ,G ψ n m))=_
  have hs (ψ:DirichletCharacter ℂ p) (_:ψ∈S) : Summable (fun m=>C ψ n*G ψ n m) :=
    (proposition141_front_character_series_summable ψ hD hL hmod hp hn hB hκ).mul_left _
  calc
    _=∑'m:ℕ,∑ψ∈S,C ψ n*G ψ n m := by
      rw [Summable.tsum_finsetSum hs]
      simp only [tsum_mul_left]
    _=(D:ℂ)⁻¹*((a n/(n:ℂ))*(∑'m:ℕ,proposition141PrimeGaussSingle (p:=p) χ n κ m)) := by
      rw [←tsum_mul_left,←tsum_mul_left]
      apply tsum_congr
      intro m
      dsimp [C,G,S]
      unfold proposition141PrimeGaussSingle proposition141DeltaOneTerm
      by_cases hm:0<m
      · simp only [if_pos hm,Nat.one_mul,Nat.cast_mul]
        simp only [mul_sum,sum_mul,div_eq_mul_inv,mul_inv_rev]
        apply sum_congr rfl
        intro ψ hψ
        ring
      · simp only [if_neg hm,mul_zero,sum_const_zero]

/-- Exact prime-by-prime arithmetic mean attached to the original Ψ front. -/
theorem proposition141_gauss_front_arithmetic_mean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (a:ℕ→ℂ) (β:ℂ) :
    proposition141GaussDeltaOneMean χ β κ a=
      ∑p:lemma33PrimeIndex D,proposition141ShiftWeight D p.val β*
        proposition141PrimeGaussArithmetic (p:=p.val) χ κ a := by
  unfold proposition141GaussDeltaOneMean
  rw [proposition141_actual_family_primitive_sum]
  apply sum_congr rfl
  intro p hp
  simp only [←mul_sum]
  congr 1
  have hpp:p.val∈lemma56PaperPrimes D := by
    rw [←proposition141_prime_windows_equal]
    exact p.property
  exact proposition141_gauss_front_prime_arithmetic χ hD hL hmod hpp hB hκ a

/-- The original additive mean prior to the two genuine gcd reindexings. -/
noncomputable def proposition141AdditiveSourceMean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  ∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*
    proposition141PrimeAdditiveArithmetic (p:=p) χ κ a

/-- The front-to-additive difference is the two literal signed prime
corrections, with the actual β weight and conductor Dp unchanged. -/
theorem proposition141_gauss_front_additive_difference {D:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (a:ℕ→ℂ) (β:ℂ) :
    proposition141GaussDeltaOneMean χ β κ a-proposition141AdditiveSourceMean χ β κ a=
      proposition141PrimeFrontCorrectionTotal χ β κ a := by
  rw [proposition141_gauss_front_arithmetic_mean χ hD hL hmod hB hκ a β]
  unfold proposition141AdditiveSourceMean
  rw [Finset.sum_subtype (lemma33PrimeWindow D) (fun _=>Iff.rfl)
    (fun p=>proposition141ShiftWeight D p β*proposition141PrimeAdditiveArithmetic (p:=p) χ κ a)]
  change (∑p:lemma33PrimeIndex D,proposition141ShiftWeight D p.val β*proposition141PrimeGaussArithmetic (p:=p.val) χ κ a)-
    (∑p:lemma33PrimeIndex D,proposition141ShiftWeight D p.val β*proposition141PrimeAdditiveArithmetic (p:=p.val) χ κ a)=_
  rw [←sum_sub_distrib]
  have he : (∑p:lemma33PrimeIndex D,
      (proposition141ShiftWeight D p.val β*proposition141PrimeGaussArithmetic (p:=p.val) χ κ a-
      proposition141ShiftWeight D p.val β*proposition141PrimeAdditiveArithmetic (p:=p.val) χ κ a))=
      ∑p∈lemma33PrimeWindow D,if hp:0<p then
        letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
        proposition141ShiftWeight D p β*(proposition141PrimeGaussArithmetic (p:=p) χ κ a-
          proposition141PrimeAdditiveArithmetic (p:=p) χ κ a) else 0 := by
    rw [Finset.sum_subtype (lemma33PrimeWindow D) (fun _=>Iff.rfl)]
    apply sum_congr rfl
    intro p hp
    have hpos:0<p.val := (lemma33_mem_prime_window.mp p.property).1.pos
    rw [dif_pos hpos]
    ring
  rw [he,proposition141_prime_source_total_identity χ hD hL hmod hB hκ a β]

end ZhangLS.Spec
