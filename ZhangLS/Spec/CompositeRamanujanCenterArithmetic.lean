import ZhangLS.Spec.FixedModulusGcdBridge
import ZhangLS.Spec.InducedGaussMainCharacters

/-! Genuine Ramanujan sums, including modulus one and numerator zero.
All equalities here are finite arithmetic identities. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.CompositeRamanujanCenter
open Complex Finset
open scoped Classical ComplexConjugate

/-- The actual sum of the standard additive character over units. -/
noncomputable def ramanujanSum (A : ℕ) [NeZero A] (B : ℕ) : ℂ :=
  ∑ u : (ZMod A)ˣ, ZMod.stdAddChar ((B : ZMod A) * (u : ZMod A))

theorem ramanujanSum_residues (A : ℕ) [NeZero A] (B : ℕ) :
    ramanujanSum A B = ∑ a : ZMod A,
      if IsUnit a then ZMod.stdAddChar ((B : ZMod A) * a) else 0 := by
  rw [← sum_filter]
  unfold ramanujanSum
  apply sum_bij (fun (u : (ZMod A)ˣ) _ => (u : ZMod A))
  · intro u hu
    exact mem_filter.mpr ⟨mem_univ _, u.isUnit⟩
  · intro u hu v hv h
    exact Units.val_injective h
  · intro a ha
    obtain ⟨u, rfl⟩ := (mem_filter.mp ha).2
    exact ⟨u, mem_univ _, rfl⟩
  · intro u hu
    rfl

theorem ramanujanSum_range (A : ℕ) [NeZero A] (B : ℕ) :
    ramanujanSum A B = ∑ a ∈ range A,
      if a.Coprime A then ZMod.stdAddChar ((B : ZMod A) * (a : ZMod A)) else 0 := by
  rw [ramanujanSum_residues, inducedGauss_sum_zmod_eq_range]
  simp only [ZMod.isUnit_iff_coprime]

/-- Orthogonality uses the actual primitive standard additive character. -/
theorem additive_full_sum (A : ℕ) [NeZero A] (B : ℕ) :
    (∑ a : ZMod A, ZMod.stdAddChar ((B : ZMod A) * a)) =
      if A ∣ B then (A : ℂ) else 0 := by
  simpa only [mul_comm, ZMod.natCast_eq_zero_iff, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
    (AddChar.sum_mulShift (R' := ℂ) (B : ZMod A) (ZMod.isPrimitive_stdAddChar A))

theorem divisor_inner {A : ℕ} [NeZero A] (B : ℕ) {d : ℕ} (hd : d ∣ A) :
    (∑ a ∈ range A, if d ∣ a then
      ZMod.stdAddChar ((B : ZMod A) * (a : ZMod A)) else 0) =
      if A / d ∣ B then ((A / d : ℕ) : ℂ) else 0 := by
  have hA := Nat.pos_of_ne_zero (NeZero.ne A)
  have hdp := Nat.pos_of_dvd_of_pos hd hA
  have hqp := Nat.div_pos (Nat.le_of_dvd hA hd) hdp
  letI : NeZero d := ⟨hdp.ne'⟩
  letI : NeZero (A / d) := ⟨hqp.ne'⟩
  have hAd : d * (A / d) = A := Nat.mul_div_cancel' hd
  have hphase (b : ℕ) :
      ZMod.stdAddChar ((B : ZMod A) * ((d * b : ℕ) : ZMod A)) =
        ZMod.stdAddChar ((B : ZMod (A / d)) * (b : ZMod (A / d))) := by
    have hleft := ZMod.stdAddChar_coe (N := A) ((B * (d * b) : ℕ) : ℤ)
    have hright := ZMod.stdAddChar_coe (N := A / d) ((B * b : ℕ) : ℤ)
    simp only [Int.cast_natCast] at hleft hright
    simp only [Nat.cast_mul] at hleft hright ⊢
    rw [hleft, hright]
    congr 1
    have hAc : (d : ℂ) * ((A / d : ℕ) : ℂ) = (A : ℂ) := by exact_mod_cast hAd
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdp.ne'
    have hqC : ((A / d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqp.ne'
    rw [← hAc]
    field_simp
  calc
    _ = ∑ a ∈ range (d * (A / d)), if d ∣ a then
        ZMod.stdAddChar ((B : ZMod A) * (a : ZMod A)) else 0 := by rw [hAd]
    _ = ∑ b ∈ range (A / d),
        ZMod.stdAddChar ((B : ZMod A) * ((d * b : ℕ) : ZMod A)) :=
      inducedGauss_sum_range_multiples hdp _
    _ = ∑ b : ZMod (A / d), ZMod.stdAddChar ((B : ZMod (A / d)) * b) := by
      simp_rw [hphase]
      exact (inducedGauss_sum_zmod_eq_range (N := A / d)
        (fun b => ZMod.stdAddChar ((B : ZMod (A / d)) * b))).symm
    _ = _ := additive_full_sum (A / d) B

/-- The genuine Möbius divisor formula; no squarefree assumption. -/
theorem ramanujanSum_divisor_formula (A : ℕ) [NeZero A] (B : ℕ) :
    ramanujanSum A B = ∑ g ∈ (Nat.gcd A B).divisors,
      (g : ℂ) * (ArithmeticFunction.moebius (A / g) : ℂ) := by
  rw [ramanujanSum_range, inducedGauss_coprime_sum_mobius (NeZero.ne A)]
  have hinner : (∑ d ∈ A.divisors, (ArithmeticFunction.moebius d : ℂ) *
      ∑ a ∈ range A, if d ∣ a then
        ZMod.stdAddChar ((B : ZMod A) * (a : ZMod A)) else 0) =
      ∑ d ∈ A.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if A / d ∣ B then ((A / d : ℕ) : ℂ) else 0) := by
    apply sum_congr rfl
    intro d hd
    rw [divisor_inner B (Nat.mem_divisors.mp hd).1]
  rw [hinner]
  have hswap : (∑ d ∈ A.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if A / d ∣ B then ((A / d : ℕ) : ℂ) else 0)) =
      ∑ g ∈ A.divisors, if g ∣ B then
        (g : ℂ) * (ArithmeticFunction.moebius (A / g) : ℂ) else 0 := by
    rw [← Nat.sum_divisorsAntidiagonal
      (fun d g => (ArithmeticFunction.moebius d : ℂ) * (if g ∣ B then (g : ℂ) else 0)),
      Nat.sum_divisorsAntidiagonal'
        (fun d g => (ArithmeticFunction.moebius d : ℂ) * (if g ∣ B then (g : ℂ) else 0))]
    apply sum_congr rfl
    intro g hg
    by_cases h : g ∣ B <;> simp [h, mul_comm]
  rw [hswap, ← sum_filter]
  have hg : Nat.gcd A B ≠ 0 := (Nat.gcd_pos_of_pos_left B
    (Nat.pos_of_ne_zero (NeZero.ne A))).ne'
  have hset : A.divisors.filter (fun g => g ∣ B) = (Nat.gcd A B).divisors := by
    ext g
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, NeZero.ne A, hg]
  rw [hset]

theorem ramanujanSum_one (B : ℕ) : ramanujanSum 1 B = 1 := by
  rw [ramanujanSum_divisor_formula]
  simp

theorem ramanujanSum_zero (A : ℕ) [NeZero A] :
    ramanujanSum A 0 = (A.totient : ℂ) := by
  simp [ramanujanSum, ZMod.card_units_eq_totient]

theorem ramanujanSum_unit (A : ℕ) [NeZero A] :
    ramanujanSum A 1 = (ArithmeticFunction.moebius A : ℂ) := by
  rw [ramanujanSum_divisor_formula]
  simp

end ZhangLS.Spec.CompositeRamanujanCenter
