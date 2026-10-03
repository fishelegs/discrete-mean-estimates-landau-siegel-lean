import ZhangLS.Spec.RoughCollisionBudget

/-! Exact smooth/rough divisor splitting and the finite n1 divisor budget.
These identities do not yet reindex the complete original rho-star sum. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- The original supported n1 is coprime to every Q-rough argument. -/
theorem roughCollision_supported_coprime {Q n₁ n : ℕ}
    (hn₁ : Lemma151Supported Q n₁) (hn : n.Coprime Q) : n.Coprime n₁ := by
  by_contra h
  obtain ⟨p,hp,hpn,hpn₁⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hn hpn (hn₁.2 p hp hpn₁))

/-- The actual U*V coefficient has the exact smooth/rough divisor splitting.
No coprimality is assumed between the two rough factors themselves. -/
theorem roughCollision_actual_B_smooth_split {D n₁ n : ℕ}
    (hn₁ : Lemma151Supported (lemma151Q D) n₁)
    (hn : n.Coprime (lemma151Q D)) (hn0 : n≠0) :
    lemma151BChiPsi D (n₁*n) =
      ∑ dd ∈ n₁.divisorsAntidiagonal, ∑ ll ∈ n.divisorsAntidiagonal,
        lemma151First D (dd.1*ll.1)*lemma151Second D (dd.2*ll.2) := by
  unfold lemma151BChiPsi
  rw [proposition71_divisor_pair_split hn₁.1 hn0 (fun a b => lemma151First D a*lemma151Second D b)]
  apply sum_congr rfl
  intro dd hdd
  have he : n.divisorsAntidiagonal.filter (fun ll => ll.1.Coprime dd.2)=
      n.divisorsAntidiagonal := by
    apply filter_eq_self.mpr
    intro ll hll
    have hdd2 : dd.2∣n₁ := by
      exact ⟨dd.1,by rw [mul_comm]; exact (Nat.mem_divisorsAntidiagonal.mp hdd).1.symm⟩
    have hll1 : ll.1∣n := by
      exact ⟨ll.2,(Nat.mem_divisorsAntidiagonal.mp hll).1.symm⟩
    exact Nat.Coprime.of_dvd_right hdd2
      (Nat.Coprime.of_dvd_left hll1 (roughCollision_supported_coprime hn₁ hn))
  rw [he]

/-- The actual finite rectangle error for one divisor split. This is a defined
arithmetic difference, not an assumed error bound or an asymptotic model. -/
noncomputable def roughCollisionSourceDefect (D X l₁ l₂ : ℕ) (c : ℝ) (j : Fin 3) : ℂ :=
    (∑ a ∈ roughCollisionDomain D X, ∑ b ∈ roughCollisionDomain D X,
        lemma151First D (l₁*a)*lemma151Second D (l₂*b)*
          lemma151Rho (lemma83PaperBeta D c j) (a*b)/((a : ℂ)*(b : ℂ))) -
      (∑ a ∈ roughCollisionDomain D X,
        lemma151First D (l₁*a)*lemma151Rho (lemma83PaperBeta D c j) a/(a : ℂ))*
      (∑ b ∈ roughCollisionDomain D X,
        lemma151Second D (l₂*b)*lemma151Rho (lemma83PaperBeta D c j) b/(b : ℂ))

/-- The finite n1 divisor factor is retained exactly. This does not yet include
any external weighted sum over n1 from (15.19)-(15.22). -/
theorem roughCollision_source_divisor_sum {D X : ℕ} (hD : 0<D)
    (hL : 1≤lemma23PaperL D) (hX : 1≤X) (hXP : (X : ℝ)≤lemma23PaperP D)
    (n₁ : ℕ) (c : ℝ) (j : Fin 3) :
    ‖∑ dd ∈ n₁.divisorsAntidiagonal, roughCollisionSourceDefect D X dd.1 dd.2 c j‖ ≤
      (n₁.divisors.card : ℝ)*roughCollisionUniformBudget D := by
  have hcard : n₁.divisorsAntidiagonal.card=n₁.divisors.card := by
    rw [←Nat.map_div_right_divisors]
    simp
  calc
    _ ≤ ∑ dd ∈ n₁.divisorsAntidiagonal, ‖roughCollisionSourceDefect D X dd.1 dd.2 c j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _dd ∈ n₁.divisorsAntidiagonal, roughCollisionUniformBudget D := by
      apply sum_le_sum
      intro dd hdd
      exact roughCollision_actual_source_uniform hD hL hX hXP dd.1 dd.2 c j
    _ = _ := by simp [hcard]

/-- The external character from the repaired psi basis costs no additional
factor, including ramified n1 where it kills the expression identically. -/
theorem roughCollision_source_character_divisor_sum {D X : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 0<D) (hL : 1≤lemma23PaperL D)
    (hX : 1≤X) (hXP : (X : ℝ)≤lemma23PaperP D)
    (n₁ : ℕ) (c : ℝ) (j : Fin 3) :
    ‖χ.evalNat n₁*∑ dd ∈ n₁.divisorsAntidiagonal,
      roughCollisionSourceDefect D X dd.1 dd.2 c j‖ ≤
      (n₁.divisors.card : ℝ)*roughCollisionUniformBudget D := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.chi.norm_le_one _)).trans
    (roughCollision_source_divisor_sum hD hL hX hXP n₁ c j)

end ZhangLS.Spec
