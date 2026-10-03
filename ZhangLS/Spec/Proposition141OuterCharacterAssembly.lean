import ZhangLS.Spec.Proposition141OuterCharacterObjects

/-! Exact finite outer assembly of the original principal, χ-induced and
remaining character contributions. No residual is defined by subtraction. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141OuterMean {D:ℕ} (χ:RealPrimitiveCharacter D) (β:ℂ)
    (F:ℕ→ℕ→ℕ→ℕ→ℂ) : ℂ :=
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  (gaussSum χ.chi ZMod.stdAddChar/(D:ℂ))*
    ∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
      ∑D₁∈D.divisors,∑d∈proposition141Indices D,∑k∈proposition141Indices D,F D₁ p d k

lemma proposition141_outer_mean_add {D:ℕ} (χ:RealPrimitiveCharacter D) (β:ℂ)
    (F G:ℕ→ℕ→ℕ→ℕ→ℂ) :
    proposition141OuterMean χ β (fun D₁ p d k=>F D₁ p d k+G D₁ p d k)=
      proposition141OuterMean χ β F+proposition141OuterMean χ β G := by
  simp only [proposition141OuterMean,sum_add_distrib,mul_add]

noncomputable def proposition141RemainingMean {D:ℕ} (χ:RealPrimitiveCharacter D)
    (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  proposition141OuterMean χ β (fun D₁ p d k=>if k.Coprime D₁ then
    (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141RemainingCharacterRow χ D₁ (D/D₁) p d k κ else 0)

noncomputable def proposition141FullCharacterMean {D:ℕ} (χ:RealPrimitiveCharacter D)
    (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  proposition141OuterMean χ β (fun D₁ p d k=>if k.Coprime D₁ then
    (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141FullCharacterRow D D₁ (D/D₁) p d k κ else 0)

/-- The complete fixed-D additive mean is its actual full-character mean. -/
theorem proposition141_fixed_gcd_full_character_mean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (a:ℕ→ℂ) (β:ℂ) :
    proposition141FixedGcdMean χ β κ a=proposition141FullCharacterMean χ β κ a := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  unfold proposition141FixedGcdMean proposition141FullCharacterMean proposition141OuterMean
  congr 1
  apply sum_congr rfl
  intro p hp
  congr 1
  apply sum_congr rfl
  intro D₁ hD₁
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro k hk
  have hdiv := (Nat.mem_divisors.mp hD₁).1
  have hD₁0:0<D₁ := Nat.pos_of_dvd_of_pos hdiv χ.modulus_pos
  have hD₂:0<D/D₁ := Nat.div_pos (Nat.le_of_dvd χ.modulus_pos hdiv) hD₁0
  have hk0 := (proposition141_mem_indices D k |>.mp hk).1
  have hd0 := (proposition141_mem_indices D d |>.mp hd).1
  have hN:0<(D/D₁)*k := Nat.mul_pos hD₂ hk0
  letI : NeZero ((D/D₁)*k) := ⟨hN.ne'⟩
  have hpp:p∈lemma56PaperPrimes D := by rw [←proposition141_prime_windows_equal]; exact hp
  have hp0 := (lemma56_mem_paper_primes D p |>.mp hpp).1.pos
  have hcp:p.Coprime ((D/D₁)*k) := (proposition141_prime_short_unit hD hmod hpp hk).1.symm.of_dvd_right
    (Nat.mul_dvd_mul_right (Nat.div_dvd_of_dvd hdiv) k)
  have hq:1≤((D/D₁:ℕ):ℝ)*(p:ℝ)*(k:ℝ) := by
    have hn:1≤(D/D₁)*p*k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.mul_ne_zero hD₂.ne' hp0.ne') hk0.ne')
    exact_mod_cast hn
  have hqP:((D/D₁:ℕ):ℝ)*(p:ℝ)*(k:ℝ)≤lemma23PaperP D^10 := by
    apply le_trans _ (proposition141_prime_correction_scales hD hL hmod hpp hk).2.2.2
    have hv:((D/D₁:ℕ):ℝ)≤(D:ℝ) := by exact_mod_cast Nat.div_le_self D D₁
    gcongr
  dsimp only
  by_cases hc:k.Coprime D₁
  · rw [if_pos hc,if_pos hc]
    congr 1
    unfold proposition141FullCharacterRow
    rw [dif_pos hN]
    exact proposition141_fixed_reciprocal_character_expansion hD hL hcp hB hκ hD₁0 hd0 hq hqP
  · rw [if_neg hc,if_neg hc]

lemma proposition141_chi_outer_mean {D:ℕ} (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) :
    proposition141OuterMean χ β (fun D₁ p d k=>if k.Coprime D₁ then
      (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141ChiCharacterRow χ D₁ (D/D₁) p d k κ else 0)=
      proposition141ChiInducedTotal χ β κ a := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  unfold proposition141OuterMean proposition141ChiInducedTotal
  congr 1
  apply sum_congr rfl
  intro p hp
  congr 1
  have he (D₁:ℕ) (hD₁:D₁∈D.divisors) :
      (∑d∈proposition141Indices D,∑k∈proposition141Indices D,if k.Coprime D₁ then
        (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141ChiCharacterRow χ D₁ (D/D₁) p d k κ else 0)=
      if D₁=1 then ∑d∈proposition141Indices D,∑k∈proposition141Indices D,
        (d:ℂ)⁻¹*(a (d*k)/((k:ℂ)*((D*k).totient:ℂ)))*proposition141ChiInducedInner χ κ p d k else 0 := by
    calc
      _=∑d∈proposition141Indices D,∑k∈proposition141Indices D,
          if D₁=1 then (d:ℂ)⁻¹*(a (d*k)/((k:ℂ)*((D*k).totient:ℂ)))*
            proposition141ChiInducedInner χ κ p d k else 0 := by
        apply sum_congr rfl
        intro d hd
        apply sum_congr rfl
        intro k hk
        exact proposition141_weighted_chi_source_branch χ hD₁ (proposition141_mem_indices D k |>.mp hk).1 κ a
      _=_ := by split_ifs <;> simp only [if_true,if_false,sum_const_zero]
  rw [sum_congr rfl he]
  have h1:1∈D.divisors := Nat.mem_divisors.mpr ⟨one_dvd D,χ.modulus_ne_zero⟩
  simp only [sum_ite_eq',h1,if_true]

/-- The complete remaining source is an explicit character sum. Its exact
separation from both original main contributions is a proved equality. -/
theorem proposition141_full_character_mean_partition {D:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (β:ℂ) (κ a:ℕ→ℂ) :
    proposition141FullCharacterMean χ β κ a=
      proposition141PrincipalTotal χ β κ a+proposition141ChiInducedTotal χ β κ a+
        proposition141RemainingMean χ β κ a := by
  let P := fun (D₁ p d k:ℕ)=>if k.Coprime D₁ then proposition141PrincipalRow D D₁ (D/D₁) p d k κ a else 0
  let C := fun (D₁ p d k:ℕ)=>if k.Coprime D₁ then
    (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141ChiCharacterRow χ D₁ (D/D₁) p d k κ else 0
  let R := fun (D₁ p d k:ℕ)=>if k.Coprime D₁ then
    (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141RemainingCharacterRow χ D₁ (D/D₁) p d k κ else 0
  have he : proposition141FullCharacterMean χ β κ a=
      proposition141OuterMean χ β (fun D₁ p d k=>(P D₁ p d k+C D₁ p d k)+R D₁ p d k) := by
    unfold proposition141FullCharacterMean proposition141OuterMean
    congr 1
    apply sum_congr rfl
    intro p hp
    congr 1
    apply sum_congr rfl
    intro D₁ hD₁
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro k hk
    have hdiv := (Nat.mem_divisors.mp hD₁).1
    have hD₁0:0<D₁ := Nat.pos_of_dvd_of_pos hdiv χ.modulus_pos
    have hD₂:0<D/D₁ := Nat.div_pos (Nat.le_of_dvd χ.modulus_pos hdiv) hD₁0
    have hk0 := (proposition141_mem_indices D k |>.mp hk).1
    dsimp [P,C,R]
    by_cases hc:k.Coprime D₁
    · simp only [if_pos hc]
      exact proposition141_weighted_character_row_partition χ hD (Nat.mul_pos hD₂ hk0) κ a
    · simp only [if_neg hc,add_zero]
  rw [he,proposition141_outer_mean_add,proposition141_outer_mean_add]
  have hp : proposition141OuterMean χ β P=proposition141PrincipalTotal χ β κ a := rfl
  have hc : proposition141OuterMean χ β C=proposition141ChiInducedTotal χ β κ a := proposition141_chi_outer_mean χ β κ a
  rw [hp,hc]
  rfl

end ZhangLS.Spec
