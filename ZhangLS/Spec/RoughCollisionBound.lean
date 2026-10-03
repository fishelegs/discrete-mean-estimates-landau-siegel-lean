import ZhangLS.Spec.RoughCollisionArithmetic

/-! Explicit collision mass for the original q<D^4 rough domain. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def roughCollisionPrimes (D X : ℕ) : Finset ℕ :=
  (Icc (D^4) X).filter Nat.Prime

/-- A finite weighted common-prime cover. Every term is nonnegative; a pair can
be covered by several primes, which only increases the upper bound. -/
theorem roughCollision_prime_cover (D X : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0≤w n) :
    (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if a.Coprime (lemma151Q D) ∧ b.Coprime (lemma151Q D) ∧ ¬a.Coprime b
      then w a*w b else 0) ≤
      ∑ p ∈ roughCollisionPrimes D X,
        (∑ a ∈ (Icc 1 X).filter (fun a => p∣a), w a)^2 := by
  have hind (p a b : ℕ) : 0 ≤ (if p∣a then w a else 0)*(if p∣b then w b else 0) := by
    apply mul_nonneg <;> split_ifs <;> first | exact hw _ | exact le_refl 0
  calc
    _ ≤ ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        ∑ p ∈ roughCollisionPrimes D X,
          (if p∣a then w a else 0)*(if p∣b then w b else 0) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      split_ifs with h
      · obtain ⟨p,hp,hpa,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h.2.2
        have hmem : p∈roughCollisionPrimes D X := by
          refine mem_filter.mpr ⟨mem_Icc.mpr ⟨roughCollision_common_prime_lower h.1 hp hpa,?_⟩,hp⟩
          exact (Nat.le_of_dvd (by have := (mem_Icc.mp ha).1; omega) hpa).trans (mem_Icc.mp ha).2
        calc
          _ = (if p∣a then w a else 0)*(if p∣b then w b else 0) := by simp [hpa,hpb]
          _ ≤ _ := single_le_sum (fun q _ => hind q a b) hmem
      · exact sum_nonneg fun p _ => hind p a b
    _ = ∑ p ∈ roughCollisionPrimes D X,
        ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
          (if p∣a then w a else 0)*(if p∣b then w b else 0) := by
      calc
        _ = ∑ a ∈ Icc 1 X, ∑ p ∈ roughCollisionPrimes D X, ∑ b ∈ Icc 1 X,
            (if p∣a then w a else 0)*(if p∣b then w b else 0) := by
          apply sum_congr rfl
          intro a ha
          exact sum_comm
        _ = _ := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      rw [sum_filter,pow_two,sum_mul_sum]

/-- The closed lower endpoint costs at most 2/D^4, without a prime number theorem. -/
theorem roughCollision_prime_square_tail (D X : ℕ) (hD : 0<D) :
    (∑ p ∈ roughCollisionPrimes D X, ((p : ℝ)^2)⁻¹) ≤ 2/(D^4 : ℕ) := by
  have hpow : 0<D^4 := pow_pos hD _
  have hsubset : roughCollisionPrimes D X ⊆ Ioo (D^4-1) (X+1) := by
    intro p hp
    have hh := mem_Icc.mp (mem_filter.mp hp).1
    exact mem_Ioo.mpr (by omega)
  calc
    _ ≤ ∑ p ∈ Ioo (D^4-1) (X+1), ((p : ℝ)^2)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)
    _ ≤ 2/((D^4-1 : ℕ)+1 : ℝ) := sum_Ioo_inv_sq_le _ _
    _ = _ := by
      have he : (D^4-1 : ℕ)+1=D^4 := Nat.sub_add_cancel (by omega)
      have her : ((D^4-1 : ℕ) : ℝ)+1=(D^4 : ℕ) := by exact_mod_cast he
      rw [her]

/-- Explicit tau-weighted mass of rough collisions in a full rectangle. -/
theorem roughCollision_tau_mass (D X : ℕ) (hD : 0<D) (hX : 1≤X) :
    (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if a.Coprime (lemma151Q D) ∧ b.Coprime (lemma151Q D) ∧ ¬a.Coprime b
      then ((lemma34Tau 2 a : ℝ)/(a : ℝ))*((lemma34Tau 2 b : ℝ)/(b : ℝ)) else 0) ≤
      8*(harmonic X : ℝ)^4/(D^4 : ℕ) := by
  calc
    _ ≤ ∑ p ∈ roughCollisionPrimes D X,
        (∑ a ∈ (Icc 1 X).filter (fun a => p∣a), (lemma34Tau 2 a : ℝ)/(a : ℝ))^2 :=
      roughCollision_prime_cover D X _ (fun _ => by positivity)
    _ ≤ ∑ p ∈ roughCollisionPrimes D X, (2/(p : ℝ)*(harmonic X : ℝ)^2)^2 := by
      apply sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (sum_nonneg (by intros; positivity))
        (roughCollision_prime_multiple_bound (mem_filter.mp hp).2 hX) 2
    _ = 4*(harmonic X : ℝ)^4*(∑ p ∈ roughCollisionPrimes D X, ((p : ℝ)^2)⁻¹) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ 4*(harmonic X : ℝ)^4*(2/(D^4 : ℕ)) :=
      mul_le_mul_of_nonneg_left (roughCollision_prime_square_tail D X hD) (by positivity)
    _ = _ := by ring

end ZhangLS.Spec
