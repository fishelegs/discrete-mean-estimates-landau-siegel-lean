import ZhangLS.Spec.Proposition71CharacterPrimeSource
import ZhangLS.Spec.PrimitiveConductorNonprincipalSum

/-! The actual source nonprincipal block bounded by all genuine primitive
conductors, keeping the full d,k,phi(k) and sqrt(r) weights. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3500000

/-- The cancellation-bearing source is bounded only after exact induction
into the original full sigma. Principal means precisely conductor one. -/
theorem proposition71_nonprincipal_gauss_source_sum_bound {D k d : ℕ} [NeZero k]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hk : k∈lemma81PolynomialIndices D)
    (hd : 0<d) {B : ℝ} (hB : 0≤B) (c : ℝ) (a : ℕ → ℂ)
    (ha : Lemma81AdmissibleSequence D B a) :
    ‖∑θ∈(univ : Finset (DirichletCharacter ℂ k)).erase 1,
      gaussSum θ⁻¹ ZMod.stdAddChar*proposition71CharacterPrimeSource D d c a θ‖≤
      ∑r∈k.divisors, if 1<r then Real.sqrt (r : ℝ)*
        ∑θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
          ‖proposition71OriginalSigmaSeries D c a (k/r) d θ‖ else 0 := by
  rw [primitiveConductor_nonprincipal_sum]
  apply (norm_sum_le _ _).trans
  calc
    _≤∑i : primitiveConductorFamilyIndex k, if 1<(i.1).val then
      Real.sqrt ((i.1).val : ℝ)*‖proposition71OriginalSigmaSeries D c a (k/(i.1).val) d (i.2).val‖ else 0 := by
      apply sum_le_sum
      intro i hi
      by_cases hr : 1<(i.1).val
      · simp only [if_pos hr]
        exact proposition71_primitive_family_source_bound hD hL hk hd hB c a ha i
      · simp only [if_neg hr,norm_zero,le_refl]
    _=_ := by
      rw [primitiveConductor_gt_one_divisor_sum
        (fun (r : ℕ) (θ : DirichletCharacter ℂ r) => Real.sqrt (r : ℝ)*
          ‖proposition71OriginalSigmaSeries D c a (k/r) d θ‖)]
      apply sum_congr rfl
      intro r hr
      split_ifs <;> simp only [mul_sum]

noncomputable def proposition71DivisorConductorBlock (D d k : ℕ) (c : ℝ) (a : ℕ → ℂ) : ℝ :=
  if d*k∈lemma81PolynomialIndices D then
    ∑r∈k.divisors, if 1<r then
      ((d : ℝ)*(k/r : ℕ)*(k.totient : ℝ)*Real.sqrt (r : ℝ))⁻¹*
        ∑θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
          ‖proposition71OriginalSigmaSeries D c a (k/r) d θ‖ else 0
  else 0

lemma proposition71_divisor_conductor_block_nonneg (D d k : ℕ) (c : ℝ) (a : ℕ → ℂ) :
    0≤proposition71DivisorConductorBlock D d k c a := by
  unfold proposition71DivisorConductorBlock
  split_ifs
  · apply sum_nonneg
    intro r hr
    split_ifs <;> positivity
  · exact le_rfl

/-- Exact conductor arithmetic normalization, paying the sqrt(r) factor. -/
lemma proposition71_divisor_conductor_weight {d k r : ℕ}
    (hd : 0<d) (hk : 0<k) (hr : 0<r) (hdiv : r∣k) :
    ((d : ℝ)*(k : ℝ)*(k.totient : ℝ))⁻¹*Real.sqrt (r : ℝ)=
      ((d : ℝ)*(k/r : ℕ)*(k.totient : ℝ)*Real.sqrt (r : ℝ))⁻¹ := by
  have hdR : (d : ℝ)≠0 := by exact_mod_cast hd.ne'
  have hkR : (k : ℝ)≠0 := by exact_mod_cast hk.ne'
  have hphiR : (k.totient : ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  have hrR : 0<(r : ℝ) := by exact_mod_cast hr
  have hq : 0<k/r := Nat.div_pos (Nat.le_of_dvd hk hdiv) hr
  have hqR : (k/r : ℕ)≠(0 : ℝ) := by exact_mod_cast hq.ne'
  have hmul : ((k/r : ℕ) : ℝ)*(r : ℝ)=(k : ℝ) := by exact_mod_cast Nat.div_mul_cancel hdiv
  have hs : Real.sqrt (r : ℝ)≠0 := (Real.sqrt_pos.mpr hrR).ne'
  field_simp
  rw [Real.sq_sqrt hrR.le]
  nlinarith only [hmul]

/-- Actual supported a2 block bound; every divisor and primitive character
of k is retained. The only outer coefficient loss is its real bound B2. -/
theorem proposition71_nonprincipal_source_block_bound {D d k : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {B₁ B₂ : ℝ} (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (c : ℝ) (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (ha₂ : ∀n, ‖a₂ n‖≤B₂) :
    ‖proposition71NonprincipalSourceBlock D d k c a₁ a₂‖≤
      B₂*proposition71DivisorConductorBlock D d k c a₁ := by
  by_cases hs : 0<d ∧ 0<k ∧ d*k∈lemma81PolynomialIndices D
  · letI : NeZero k := ⟨hs.2.1.ne'⟩
    have hkS := (proposition71_short_factors hs.1 hs.2.1 hs.2.2).2
    have hb := proposition71_nonprincipal_gauss_source_sum_bound hD hL hkS hs.1 hB₁ c a₁ ha₁
    let R := ∑r∈k.divisors, if 1<r then Real.sqrt (r : ℝ)*
      ∑θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖proposition71OriginalSigmaSeries D c a₁ (k/r) d θ‖ else 0
    have hR : 0≤R := by dsimp [R]; apply sum_nonneg; intro r hr; split_ifs <;> positivity
    have hv : ‖(d : ℂ)⁻¹*(a₂ (d*k)/(k : ℂ))*(k.totient : ℂ)⁻¹‖≤
        B₂*((d : ℝ)*(k : ℝ)*(k.totient : ℝ))⁻¹ := by
      simp only [norm_mul,norm_inv,norm_div,Complex.norm_natCast]
      calc
        _≤(d : ℝ)⁻¹*(B₂/(k : ℝ))*(k.totient : ℝ)⁻¹ := by gcongr; exact ha₂ (d*k)
        _=_ := by ring
    unfold proposition71NonprincipalSourceBlock
    rw [dif_pos hs,norm_mul]
    have hbound := mul_le_mul hv hb (norm_nonneg _) (by positivity)
    apply hbound.trans_eq
    unfold proposition71DivisorConductorBlock
    rw [if_pos hs.2.2]
    rw [mul_assoc]
    simp only [mul_sum]
    apply sum_congr rfl
    intro r hr
    by_cases hr1 : 1<r
    · simp only [if_pos hr1]
      have hw := proposition71_divisor_conductor_weight hs.1 hs.2.1 (by omega) (Nat.mem_divisors.mp hr).1
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro θ hθ
      rw [←mul_assoc,hw]
    · simp only [if_neg hr1,mul_zero]
  · have hz : proposition71NonprincipalSourceBlock D d k c a₁ a₂=0 := by simp [proposition71NonprincipalSourceBlock,hs]
    rw [hz,norm_zero]
    exact mul_nonneg hB₂ (proposition71_divisor_conductor_block_nonneg D d k c a₁)

end ZhangLS.Spec
