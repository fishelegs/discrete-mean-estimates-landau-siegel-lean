import ZhangLS.Spec.Proposition141OuterCharacterAssembly

/-! Exact prime reordering of the literal remaining character mean, followed
by the original normalized finite positive majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition141_four_finite_sums_swap (P I J K:Finset ℕ) (F:ℕ→ℕ→ℕ→ℕ→ℂ) :
    (∑p∈P,∑i∈I,∑j∈J,∑k∈K,F p i j k)=
      ∑i∈I,∑j∈J,∑k∈K,∑p∈P,F p i j k := by
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  exact sum_comm

noncomputable def proposition141RemainingReordered {D:ℕ} (χ:RealPrimitiveCharacter D)
    (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  (gaussSum χ.chi ZMod.stdAddChar/(D:ℂ))*
    ∑D₁∈D.divisors,∑d∈proposition141Indices D,∑k∈proposition141Indices D,
      if hN:0<(D/D₁)*k then
        letI : NeZero ((D/D₁)*k) := ⟨hN.ne'⟩
        if k.Coprime D₁ then (d:ℂ)⁻¹*(a (d*k)/((k:ℂ)*(((D/D₁)*k).totient:ℂ)))*
          proposition141ResidualCharacterSource (N:=(D/D₁)*k) χ β κ D₁ d else 0
      else 0

/-- The entire prime sum is kept inside each actual character source before
any norm is taken. This preserves the cancellation already proved for σ. -/
theorem proposition141_remaining_mean_reordered {D:ℕ} (χ:RealPrimitiveCharacter D)
    (β:ℂ) (κ a:ℕ→ℂ) :
    proposition141RemainingMean χ β κ a=proposition141RemainingReordered χ β κ a := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  unfold proposition141RemainingMean proposition141OuterMean proposition141RemainingReordered
  congr 1
  simp only [mul_sum]
  rw [proposition141_four_finite_sums_swap]
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
  have hN:0<(D/D₁)*k := Nat.mul_pos hD₂ hk0
  letI : NeZero ((D/D₁)*k) := ⟨hN.ne'⟩
  rw [dif_pos hN]
  by_cases hc:k.Coprime D₁
  · simp only [if_pos hc]
    unfold proposition141RemainingCharacterRow
    simp only [dif_pos hN]
    unfold proposition141ResidualCharacterSource
    let S := (univ:Finset (DirichletCharacter ℂ ((D/D₁)*k))).filter
      (fun θ=>θ≠1 ∧ ∀hDN:D∣(D/D₁)*k,θ≠χ.chi.changeLevel hDN)
    let w := fun p:ℕ=>proposition141ShiftWeight D p β*χ.chi (p:ZMod D)
    let C := (d:ℂ)⁻¹*(a (d*k)/((k:ℂ)*(((D/D₁)*k).totient:ℂ)))
    calc
      _=C*(∑p∈lemma33PrimeWindow D,∑θ∈S,
          gaussSum θ⁻¹ ZMod.stdAddChar*(w p*proposition141LevelPrimeRow (D:=D) θ κ D₁ d p)) := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro p hp
        apply sum_congr rfl
        intro θ hθ
        dsimp [C,w]
        ring
      _=C*(∑θ∈S,∑p∈lemma33PrimeWindow D,
          gaussSum θ⁻¹ ZMod.stdAddChar*(w p*proposition141LevelPrimeRow (D:=D) θ κ D₁ d p)) := by
        rw [sum_comm]
      _=_ := by
        simp only [←mul_sum]
        rfl
  · simp only [if_neg hc,mul_zero,sum_const_zero]

/-- Full original normalized finite residual majorant, after the prime
sum and character induction remain inside each norm. -/
theorem proposition141_remaining_mean_norm_le {D:ℕ} (χ:RealPrimitiveCharacter D)
    (β:ℂ) (κ a:ℕ→ℂ) :
    ‖proposition141RemainingMean χ β κ a‖≤
      (Real.sqrt (D:ℝ))⁻¹*
        ∑D₁∈D.divisors,∑d∈proposition141Indices D,∑k∈proposition141Indices D,
          if hN:0<(D/D₁)*k then
            letI : NeZero ((D/D₁)*k) := ⟨hN.ne'⟩
            if k.Coprime D₁ then
              (‖a (d*k)‖/((d:ℝ)*(k:ℝ)*(((D/D₁)*k).totient:ℝ)))*
                ‖proposition141ResidualCharacterSource (N:=(D/D₁)*k) χ β κ D₁ d‖ else 0
          else 0 := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  rw [proposition141_remaining_mean_reordered]
  unfold proposition141RemainingReordered
  rw [norm_mul,proposition141_principal_gauss_normalization]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro D₁ hD₁
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro d hd
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro k hk
  split_ifs with hN hc
  · simp only [norm_mul,norm_inv,norm_div,Complex.norm_natCast]
    simp only [div_eq_mul_inv,mul_inv_rev]
    exact le_of_eq (by ring)
  · simp
  · simp

end ZhangLS.Spec
