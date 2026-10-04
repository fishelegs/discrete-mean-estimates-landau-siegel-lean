import ZhangLS.Spec.CompositeRamanujanCenterReduction

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.CompositeRamanujanCenter
open Complex Finset
open scoped Classical ComplexConjugate

/-- Positive reciprocal phase, with the inverse in the actual residue ring. -/
noncomputable def reciprocalPhase (A : ℕ) [NeZero A] (B p : ℕ) : ℂ :=
  ZMod.stdAddChar ((B : ZMod A) * (p : ZMod A)⁻¹)

/-- The full nonprincipal family at the actual level, including imprimitive characters. -/
noncomputable def nonprincipalCharacters (k : ℕ) [NeZero k] :
    Finset (DirichletCharacter ℂ k) := univ.filter (fun θ => θ ≠ 1)

/-- The genuinely nonprincipal finite Gauss expansion, normalized by φ(k).
Here θ⁻¹ is the character whose values are the complex conjugates of θ. -/
noncomputable def nonprincipalExpansion (k : ℕ) [NeZero k] (l p : ℕ) : ℂ :=
  (∑ θ ∈ nonprincipalCharacters k,
    gaussSum θ⁻¹ ZMod.stdAddChar * θ (l : ZMod k) * conj (θ (p : ZMod k))) /
      (k.totient : ℂ)

theorem inverse_character_is_conjugate {k : ℕ} [NeZero k]
    (θ : DirichletCharacter ℂ k) (a : ZMod k) : θ⁻¹ a = conj (θ a) := by
  rw [← MulChar.star_apply' θ a]
  rfl

/-- The sign is positive: the character factor is θ(l), not θ(-l). -/
theorem positive_character_expansion (k : ℕ) [NeZero k] (l p : ℕ)
    (hl : l.Coprime k) (hp : p.Coprime k) :
    reciprocalPhase k l p =
      (∑ θ : DirichletCharacter ℂ k,
        gaussSum θ⁻¹ ZMod.stdAddChar * θ (l : ZMod k) * conj (θ (p : ZMod k))) /
          (k.totient : ℂ) := by
  have hlu : IsUnit (l : ZMod k) := (ZMod.isUnit_iff_coprime l k).mpr hl
  have h := proposition141_additive_phase_character_expansion
    (-(l : ZMod k)) hlu.neg (ZMod.unitOfCoprime p hp)
  simpa only [neg_neg, ← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime,
    reciprocalPhase, div_eq_mul_inv, mul_comm, mul_assoc] using h

theorem principal_partition {k : ℕ} [NeZero k] (F : DirichletCharacter ℂ k → ℂ) :
    (∑ θ : DirichletCharacter ℂ k, F θ) =
      F 1 + ∑ θ ∈ nonprincipalCharacters k, F θ := by
  have hf : nonprincipalCharacters k = (univ : Finset (DirichletCharacter ℂ k)).erase 1 := by
    ext θ
    simp [nonprincipalCharacters]
  rw [hf]
  exact (sum_erase_add _ F (mem_univ 1)).symm.trans (add_comm _ _)

/-- Subtracting μ(k)/φ(k) removes the entire principal character at level k. -/
theorem centered_character_expansion (k : ℕ) [NeZero k] (l p : ℕ)
    (hl : l.Coprime k) (hp : p.Coprime k) :
    reciprocalPhase k l p - (ArithmeticFunction.moebius k : ℂ) / (k.totient : ℂ) =
      nonprincipalExpansion k l p := by
  rw [positive_character_expansion k l p hl hp, principal_partition]
  have hlu : IsUnit (l : ZMod k) := (ZMod.isUnit_iff_coprime l k).mpr hl
  have hpu : IsUnit (p : ZMod k) := (ZMod.isUnit_iff_coprime p k).mpr hp
  simp only [inv_one, inducedGauss_principal_value, MulChar.one_apply hlu,
    MulChar.one_apply hpu, map_one, mul_one, add_div, add_sub_cancel_left,
    nonprincipalExpansion]

theorem nonprincipal_conductor_gt_one {k : ℕ} [NeZero k]
    {θ : DirichletCharacter ℂ k} (hθ : θ ∈ nonprincipalCharacters k) :
    1 < θ.conductor :=
  inducedGauss_nonprincipal_conductor_gt_one θ (mem_filter.mp hθ).2

/-- Equivalent filter by the actual conductor; no conductor-one term survives. -/
theorem nonprincipalCharacters_eq_conductor_filter (k : ℕ) [NeZero k] :
    nonprincipalCharacters k = univ.filter (fun θ : DirichletCharacter ℂ k => 1 < θ.conductor) := by
  ext θ
  simp only [nonprincipalCharacters, mem_filter, mem_univ, true_and]
  constructor
  · exact inducedGauss_nonprincipal_conductor_gt_one θ
  · intro h hθ
    subst θ
    simp [DirichletCharacter.conductor_one] at h

theorem nonprincipalExpansion_conductor_sum (k : ℕ) [NeZero k] (l p : ℕ) :
    nonprincipalExpansion k l p =
      (∑ θ ∈ univ.filter (fun θ : DirichletCharacter ℂ k => 1 < θ.conductor),
        gaussSum θ⁻¹ ZMod.stdAddChar * θ (l : ZMod k) * conj (θ (p : ZMod k))) /
          (k.totient : ℂ) := by
  rw [nonprincipalExpansion, nonprincipalCharacters_eq_conductor_filter]

theorem level_one_phase (l p : ℕ) : reciprocalPhase 1 l p = 1 := by
  unfold reciprocalPhase
  rw [show (l : ZMod 1) * (p : ZMod 1)⁻¹ = 0 by exact Subsingleton.elim _ _]
  exact AddChar.map_zero_eq_one _

theorem level_one_characters : nonprincipalCharacters 1 = ∅ := by
  ext θ
  simp [nonprincipalCharacters, Subsingleton.elim θ (1 : DirichletCharacter ℂ 1)]

theorem level_one_expansion (l p : ℕ) : nonprincipalExpansion 1 l p = 0 := by
  simp [nonprincipalExpansion, level_one_characters]

theorem level_one_centered (l p : ℕ) :
    reciprocalPhase 1 l p - (ArithmeticFunction.moebius 1 : ℂ) / ((1 : ℕ).totient : ℂ) = 0 := by
  simp [level_one_phase]

/-- Positive inverse phases descend with the numerator and modulus together. -/
theorem scaled_reciprocal_phase {d k : ℕ} [NeZero d] [NeZero k] (l p : ℕ)
    (hp : p.Coprime (d * k)) :
    letI : NeZero (d * k) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne k)⟩
    reciprocalPhase (d * k) (d * l) p = reciprocalPhase k l p := by
  letI : NeZero (d * k) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne k)⟩
  unfold reciprocalPhase
  calc
    _ = ZMod.stdAddChar ((d : ZMod (d * k)) *
        ((l : ZMod (d * k)) * (p : ZMod (d * k))⁻¹)) := by
      congr 1
      push_cast
      ring
    _ = _ := by
      rw [fixedDGcd_additive_quotient, map_mul, map_natCast,
        fixedDGcd_cast_inverse (Nat.dvd_mul_left k d) hp]

/-- Exact centering after gcd removal; k=1 is included. -/
theorem gcd_centered_identity (A : ℕ) [NeZero A] (B p : ℕ) (hp : p.Coprime A) :
    let k := A / Nat.gcd A B
    let l := B / Nat.gcd A B
    letI : NeZero k := ⟨Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne A)) (Nat.gcd_dvd_left A B))
      (Nat.gcd_pos_of_pos_left B (Nat.pos_of_ne_zero (NeZero.ne A))))⟩
    reciprocalPhase A B p - ramanujanSum A B / (A.totient : ℂ) =
      reciprocalPhase k l p - (ArithmeticFunction.moebius k : ℂ) / (k.totient : ℂ) := by
  dsimp only
  have hA := Nat.pos_of_ne_zero (NeZero.ne A)
  have hd := Nat.gcd_pos_of_pos_left B hA
  letI : NeZero (Nat.gcd A B) := ⟨hd.ne'⟩
  have hk := Nat.div_pos (Nat.le_of_dvd hA (Nat.gcd_dvd_left A B)) hd
  letI : NeZero (A / Nat.gcd A B) := ⟨hk.ne'⟩
  have hAd : Nat.gcd A B * (A / Nat.gcd A B) = A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
  have hBd : Nat.gcd A B * (B / Nat.gcd A B) = B := Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
  have hs := scaled_reciprocal_phase (d := Nat.gcd A B) (k := A / Nat.gcd A B)
    (B / Nat.gcd A B) p (by simpa only [hAd] using hp)
  have he : reciprocalPhase A B p =
      reciprocalPhase (A / Nat.gcd A B) (B / Nat.gcd A B) p := by
    convert hs using 1
    simp only [hAd, hBd]
  rw [he, normalized_gcd]

/-- The requested exact finite nonprincipal expansion after the actual gcd quotient. -/
theorem gcd_nonprincipal_expansion (A : ℕ) [NeZero A] (B p : ℕ) (hp : p.Coprime A) :
    let k := A / Nat.gcd A B
    let l := B / Nat.gcd A B
    letI : NeZero k := ⟨Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne A)) (Nat.gcd_dvd_left A B))
      (Nat.gcd_pos_of_pos_left B (Nat.pos_of_ne_zero (NeZero.ne A))))⟩
    reciprocalPhase A B p - ramanujanSum A B / (A.totient : ℂ) =
      nonprincipalExpansion k l p := by
  dsimp only
  letI : NeZero (A / Nat.gcd A B) := ⟨Nat.ne_of_gt (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne A)) (Nat.gcd_dvd_left A B))
    (Nat.gcd_pos_of_pos_left B (Nat.pos_of_ne_zero (NeZero.ne A))))⟩
  rw [gcd_centered_identity A B p hp]
  apply centered_character_expansion
  · exact Nat.Coprime.symm (Nat.gcd_div_gcd_div_gcd_of_pos_left
      (Nat.pos_of_ne_zero (NeZero.ne A)))
  · exact hp.of_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left A B))

theorem divisible_centered_zero (A : ℕ) [NeZero A] (B p : ℕ) (hAB : A ∣ B) :
    reciprocalPhase A B p - ramanujanSum A B / (A.totient : ℂ) = 0 := by
  have hphi : (A.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne A))).ne'
  have hB : (B : ZMod A) = 0 := (ZMod.natCast_eq_zero_iff B A).mpr hAB
  have hsum : ramanujanSum A B = (A.totient : ℂ) := by
    simp [ramanujanSum, hB, ZMod.card_units_eq_totient]
  simp [reciprocalPhase, hB, hsum, hphi]

/-- Quotient level one is exactly the vanishing centered branch. -/
theorem quotient_one_centered_zero (A : ℕ) [NeZero A] (B p : ℕ)
    (hk : A / Nat.gcd A B = 1) :
    reciprocalPhase A B p - ramanujanSum A B / (A.totient : ℂ) = 0 := by
  have hAd : Nat.gcd A B * (A / Nat.gcd A B) = A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
  have hAg : A = Nat.gcd A B := by simpa only [hk, mul_one] using hAd.symm
  apply divisible_centered_zero
  rw [hAg]
  exact Nat.gcd_dvd_right A B

end ZhangLS.Spec.CompositeRamanujanCenter
