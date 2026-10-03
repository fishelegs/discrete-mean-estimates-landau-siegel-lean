import ZhangLS.Spec.Proposition141SigmaArithmeticAttachment
import ZhangLS.Spec.PrimitiveConductorFamily

/-! Attachment at the original level N, using its actual primitive divisor
r and exact quotient N/r rather than a renamed character. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

noncomputable def proposition141LevelPrimeRow {D N:ℕ}
    (θ:DirichletCharacter ℂ N) (κ:ℕ→ℂ) (D₁ d p:ℕ) : ℂ :=
  ∑'l:ℕ,if 0<l then κ (D₁*d*l)*θ (-(l:ZMod N))*conj (θ (p:ZMod N))*
    lemma53PaperDelta D ((l:ℝ)/((p:ℝ)*(N:ℝ))) else 0

lemma proposition141_level_product_row {D r h:ℕ} [NeZero r] [NeZero h]
    (θ:DirichletCharacter ℂ r) (κ:ℕ→ℂ) (D₁ d p:ℕ) :
    proposition141LevelPrimeRow (D:=D) (θ.changeLevel (r.dvd_mul_right h)) κ D₁ d p=
      proposition141InducedPrimeRow (D:=D) (h:=h) θ κ D₁ d p := by
  unfold proposition141LevelPrimeRow proposition141InducedPrimeRow
  simp only
  apply tsum_congr
  intro l
  by_cases hl:0<l
  · rw [if_pos hl,if_pos hl]
    congr 2
    push_cast
    ring
  · rw [if_neg hl,if_neg hl]

/-- Complete original-level Gauss source bound, with h=N/r and actual
changeLevel preserved. Every nonunit long index is handled by induction. -/
theorem proposition141_level_primitive_source_bound {D N r D₁ d:ℕ} [NeZero N] [NeZero r]
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (hθ:θ.IsPrimitive)
    (hrN:r∣N) (β:ℂ) (hD:1<D) (hL:2000≤lemma23PaperL D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hp:∀p∈lemma56PaperPrimes D,p.Coprime (N/r)) :
    ‖gaussSum (θ.changeLevel hrN)⁻¹ ZMod.stdAddChar*
      (∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
        proposition141LevelPrimeRow (D:=D) (θ.changeLevel hrN) κ D₁ d p)‖≤
      ‖(lemma51PaperT0 D:ℂ)^β‖*Real.sqrt (r:ℝ)*‖proposition141Sigma χ θ β κ D₁ d (N/r)‖ := by
  obtain ⟨h,rfl⟩ := hrN
  have hr:0<r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hh:0<h := by
    have hn := NeZero.ne (r*h)
    by_contra hn'; have hz:h=0 := by omega
    exact hn (by rw [hz,mul_zero])
  letI : NeZero h := ⟨hh.ne'⟩
  have hquot:r*h/r=h := Nat.mul_div_cancel_left h hr
  simp only [hquot] at hp ⊢
  simp_rw [proposition141_level_product_row]
  exact proposition141_induced_gauss_source_bound χ θ hθ β hD hL hB hκ hD₁ hd hp

/-- Actual primitive-conductor family instance of the complete source bound. -/
theorem proposition141_family_primitive_source_bound {D N D₁ d:ℕ} [NeZero N]
    (χ:RealPrimitiveCharacter D) (i:primitiveConductorFamilyIndex N) (β:ℂ)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {B:ℝ} (hB:0≤B)
    {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) (hD₁:0<D₁) (hd:0<d)
    (hp:∀p∈lemma56PaperPrimes D,p.Coprime N) :
    ‖gaussSum (primitiveConductorFamilyLift N i)⁻¹ ZMod.stdAddChar*
      (∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
        proposition141LevelPrimeRow (D:=D) (primitiveConductorFamilyLift N i) κ D₁ d p)‖≤
      ‖(lemma51PaperT0 D:ℂ)^β‖*Real.sqrt (i.1.val:ℝ)*
        ‖proposition141Sigma χ i.2.val β κ D₁ d (N/i.1.val)‖ := by
  letI : NeZero i.1.val := ⟨(primitiveConductorFamily_index_pos i).ne'⟩
  exact proposition141_level_primitive_source_bound χ i.2.val i.2.property
    (Nat.mem_divisors.mp i.1.property).1 β hD hL hB hκ hD₁ hd
    (fun p hpp=>(hp p hpp).of_dvd_right (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp i.1.property).1))

noncomputable def proposition141ResidualCharacterSource {D N:ℕ} [NeZero N]
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) (D₁ d:ℕ) : ℂ :=
  ∑θ∈(univ:Finset (DirichletCharacter ℂ N)).filter
    (fun θ=>θ≠1 ∧ ∀hDN:D∣N,θ≠χ.chi.changeLevel hDN),
    gaussSum θ⁻¹ ZMod.stdAddChar*
      (∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
        proposition141LevelPrimeRow (D:=D) θ κ D₁ d p)

/-- The complete literal remaining character source is dominated by its
actual primitive-divisor σ sum, with both genuine exclusions unchanged. -/
theorem proposition141_residual_primitive_source_bound {D N D₁ d:ℕ} [NeZero N]
    (χ:RealPrimitiveCharacter D) (β:ℂ) (hD:1<D) (hL:2000≤lemma23PaperL D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hp:∀p∈lemma56PaperPrimes D,p.Coprime N) :
    ‖proposition141ResidualCharacterSource (N:=N) χ β κ D₁ d‖≤
      ‖(lemma51PaperT0 D:ℂ)^β‖*
        ∑i:primitiveConductorFamilyIndex N,
          if 1 < i.1.val ∧ (∀hDN:D∣N,primitiveConductorFamilyLift N i≠χ.chi.changeLevel hDN) then
            Real.sqrt (i.1.val:ℝ)*‖proposition141Sigma χ i.2.val β κ D₁ d (N/i.1.val)‖ else 0 := by
  unfold proposition141ResidualCharacterSource
  apply (norm_sum_le _ _).trans
  rw [sum_filter,primitiveConductorFamily_sum,mul_sum]
  apply sum_le_sum
  intro i hi
  have hr := primitiveConductorFamily_index_pos i
  have hn : primitiveConductorFamilyLift N i≠1↔1 < i.1.val := by
    constructor
    · intro h
      have hn:i.1.val≠1 := fun he=>h ((primitiveConductorFamily_principal_iff i).mpr he)
      omega
    · intro h he
      have hn := (primitiveConductorFamily_principal_iff i).mp he
      omega
  simp only [hn]
  by_cases ht:1 < i.1.val ∧ (∀hDN:D∣N,primitiveConductorFamilyLift N i≠χ.chi.changeLevel hDN)
  · rw [if_pos ht,if_pos ht]
    have hb := proposition141_family_primitive_source_bound χ i β hD hL hB hκ hD₁ hd hp
    exact hb.trans_eq (by ring)
  · rw [if_neg ht,if_neg ht,mul_zero]

end ZhangLS.Spec
