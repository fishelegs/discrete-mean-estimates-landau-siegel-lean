import ZhangLS.Spec.Proposition141LevelSigmaAttachment
import ZhangLS.Spec.QuotientSourceDomination

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Literal finite original residual, with the original reciprocal d,k and
level-totient weight. Neither main character is included in its source. -/
noncomputable def proposition141FiniteResidualMajorant {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ) : ℝ :=
  (Real.sqrt (D:ℝ))⁻¹ *
    ∑D₁∈D.divisors,∑d∈proposition141Indices D,∑k∈proposition141Indices D,
      if hN:0<(D/D₁)*k then
        letI : NeZero ((D/D₁)*k) := ⟨hN.ne'⟩
        if k.Coprime D₁ then
          (‖a (d*k)‖/((d:ℝ)*(k:ℝ)*(((D/D₁)*k).totient:ℝ)))*
            ‖proposition141ResidualCharacterSource (N:=(D/D₁)*k) χ β κ D₁ d‖
        else 0
      else 0

/-- The same actual primitive source, indexed by a natural k with its
positive branch explicit; zero is merely a totalization outside that branch. -/
noncomputable def proposition141QuotientNatRow {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ) (D₁ D₂ d k : ℕ) : ℝ :=
  if hk:0<k then
    ∑i:primitiveConductorFamilyIndex (D₂*k),
      quotientConductorSourceTerm χ β κ a D₁ D₂ d ⟨⟨k,hk⟩,i⟩
  else 0

theorem proposition141_quotient_nat_row_zero {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ) (D₁ D₂ d k : ℕ)
    (hz : a (d*k)=0) : proposition141QuotientNatRow χ β κ a D₁ D₂ d k=0 := by
  unfold proposition141QuotientNatRow
  split_ifs <;> simp [quotientConductorSourceTerm,hz]

/-- Positive-series conversion for exactly a supplied positive finite set.
This is applied below only after proving support from the original a*. -/
theorem proposition141_tsum_pnat_eq_finite (S : Finset ℕ) (F : ℕ→ℝ)
    (hpos : ∀n∈S,0<n) (hzero : ∀n:ℕ,0<n→n∉S→F n=0) :
    (∑'n:ℕ+,F (n:ℕ))=∑n∈S,F n := by
  let T : Finset ℕ+ := S.preimage (fun n:ℕ+ => (n:ℕ))
    (fun _ _ _ _ he => PNat.eq he)
  calc
    _ = ∑n∈T,F (n:ℕ) := by
      apply tsum_eq_sum
      intro n hn
      exact hzero n n.property (by simpa [T] using hn)
    _ = _ := by
      apply sum_preimage
      intro n hn hnot
      exact False.elim (hnot ⟨⟨n,hpos n hn⟩,rfl⟩)

/-- No positive k is removed except where its original short coefficient
vanishes, including the closed endpoint of the paper's support. -/
theorem proposition141_quotient_k_tsum_eq_finite {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ) {Ba : ℝ} {a : ℕ→ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0<d) :
    (∑'k:ℕ+,∑i:primitiveConductorFamilyIndex (D₂*(k:ℕ)),
      quotientConductorSourceTerm χ β κ a D₁ D₂ d ⟨k,i⟩)=
      ∑k∈proposition141Indices D,proposition141QuotientNatRow χ β κ a D₁ D₂ d k := by
  have he (k:ℕ+) :
      (∑i:primitiveConductorFamilyIndex (D₂*(k:ℕ)),
        quotientConductorSourceTerm χ β κ a D₁ D₂ d ⟨k,i⟩)=
        proposition141QuotientNatRow χ β κ a D₁ D₂ d (k:ℕ) := by
    unfold proposition141QuotientNatRow
    split_ifs with hpos
    · rfl
    · exact False.elim (hpos k.property)
  rw [tsum_congr he]
  apply proposition141_tsum_pnat_eq_finite _ _
    (fun n hn => (proposition141_mem_indices D n |>.mp hn).1)
  intro k hk hout
  apply proposition141_quotient_nat_row_zero
  exact proposition141_omitted_coefficient_zero ha hd hk (fun hh=>hout hh.2)

/-- The complete nested positive source equals its literal finite original
coefficient box. Both series are cut off using proved a*-support only. -/
theorem proposition141_quotient_dk_tsum_eq_finite {D D₁ D₂ : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ) {Ba : ℝ} {a : ℕ→ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) :
    (∑'d:ℕ+,∑'k:ℕ+,∑i:primitiveConductorFamilyIndex (D₂*(k:ℕ)),
      quotientConductorSourceTerm χ β κ a D₁ D₂ (d:ℕ) ⟨k,i⟩)=
      ∑d∈proposition141Indices D,∑k∈proposition141Indices D,
        proposition141QuotientNatRow χ β κ a D₁ D₂ d k := by
  have he (d:ℕ+) := proposition141_quotient_k_tsum_eq_finite χ β κ ha d.property (D₁:=D₁) (D₂:=D₂)
  calc
    _ = ∑'d:ℕ+,∑k∈proposition141Indices D,
        proposition141QuotientNatRow χ β κ a D₁ D₂ (d:ℕ) k := tsum_congr he
    _ = _ := by
      apply proposition141_tsum_pnat_eq_finite (proposition141Indices D)
        (fun d : ℕ => ∑k∈proposition141Indices D, proposition141QuotientNatRow χ β κ a D₁ D₂ d k)
        (fun n hn => (proposition141_mem_indices D n |>.mp hn).1)
      intro d hd hout
      apply sum_eq_zero
      intro k hk
      apply proposition141_quotient_nat_row_zero
      exact proposition141_omitted_coefficient_zero ha hd
        (proposition141_mem_indices D k |>.mp hk).1 (fun hh=>hout hh.1)

/-- Exact finite presentation of the frozen normalized quotient source. -/
theorem proposition141_quotient_normalized_eq_finite {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ) {Ba : ℝ} {a : ℕ→ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) :
    quotientSourceNormalizedSource χ β κ a =
      ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
        ∑D₁∈D.divisors,∑d∈proposition141Indices D,∑k∈proposition141Indices D,
          proposition141QuotientNatRow χ β κ a D₁ (D/D₁) d k := by
  unfold quotientSourceNormalizedSource
  simp_rw [proposition141_quotient_dk_tsum_eq_finite χ β κ ha]

/-- A literal residual row is bounded with its exact coefficient. The prime
unit condition is derived from nonzero a*(d*k) and the original support. -/
theorem proposition141_weighted_residual_row_le_quotient {D D₁ d k : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {Bκ Ba : ℝ} (hBκ : 0≤Bκ) {κ a : ℕ→ℂ}
    (hκ : Proposition141KappaBound Bκ κ) (ha : Proposition141AdmissibleSequence D Ba a)
    (hD₁ : D₁∈D.divisors) (hd : 0<d) (hk : 0<k) :
    (if hN:0<(D/D₁)*k then
      letI : NeZero ((D/D₁)*k) := ⟨hN.ne'⟩
      if k.Coprime D₁ then
        (‖a (d*k)‖/((d:ℝ)*(k:ℝ)*(((D/D₁)*k).totient:ℝ)))*
          ‖proposition141ResidualCharacterSource (N:=(D/D₁)*k) χ β κ D₁ d‖
      else 0
    else 0) ≤ ‖(lemma51PaperT0 D:ℂ)^β‖*
      proposition141QuotientNatRow χ β κ a D₁ (D/D₁) d k := by
  have hdiv := (Nat.mem_divisors.mp hD₁).1
  have hD₁0 : 0<D₁ := Nat.pos_of_dvd_of_pos hdiv χ.modulus_pos
  have hD₂ : 0<D/D₁ := Nat.div_pos (Nat.le_of_dvd χ.modulus_pos hdiv) hD₁0
  have hN : 0<(D/D₁)*k := Nat.mul_pos hD₂ hk
  letI : NeZero ((D/D₁)*k) := ⟨hN.ne'⟩
  rw [dif_pos hN]
  by_cases hz : a (d*k)=0
  · rw [proposition141_quotient_nat_row_zero χ β κ a D₁ (D/D₁) d k hz]
    split_ifs <;> simp [hz]
  have hp (p:ℕ) (hpp:p∈lemma56PaperPrimes D) : p.Coprime ((D/D₁)*k) :=
    (proposition141_supported_modulus_coprime_prime ha hD hmod hpp hd hk hz).of_dvd_right
      (Nat.mul_dvd_mul_right (Nat.div_dvd_of_dvd hdiv) k)
  unfold proposition141QuotientNatRow
  rw [dif_pos hk]
  by_cases hc : k.Coprime D₁
  · rw [if_pos hc]
    have hb := proposition141_residual_primitive_source_bound χ β hD hL hBκ hκ hD₁0 hd hp
    apply (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
    rw [mul_left_comm]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    dsimp [quotientConductorSourceTerm,primitiveConductorFamilyLift]
    split_ifs with h₁ h₂ h₂
    · ring
    · exact False.elim (h₂ ⟨hc,h₁⟩)
    · exact False.elim (h₁ h₂.2)
    · ring
  · rw [if_neg hc]
    simp [quotientConductorSourceTerm,hc]

/-- The finite normalized original residual is controlled by the frozen
quotient source with no target-bound premise and no change of weights. -/
theorem proposition141_finite_residual_majorant_le_quotient {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {Bκ Ba : ℝ} (hBκ : 0≤Bκ) {κ a : ℕ→ℂ}
    (hκ : Proposition141KappaBound Bκ κ) (ha : Proposition141AdmissibleSequence D Ba a) :
    proposition141FiniteResidualMajorant χ β κ a ≤ quotientSourceNormalizedSource χ β κ a := by
  rw [proposition141_quotient_normalized_eq_finite χ β κ ha]
  unfold proposition141FiniteResidualMajorant
  rw [div_eq_mul_inv,mul_comm ‖(lemma51PaperT0 D:ℂ)^β‖,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp_rw [mul_sum]
  apply sum_le_sum
  intro D₁ hD₁
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro k hk
  exact proposition141_weighted_residual_row_le_quotient χ β hD hL hmod hBκ hκ ha hD₁
    (proposition141_mem_indices D d |>.mp hd).1 (proposition141_mem_indices D k |>.mp hk).1

end ZhangLS.Spec
