import ZhangLS.Spec.Lemma33AdditiveLargeSieve
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxHeartbeats 2000000

/-- Translation of the coefficient interval changes a trigonometric polynomial only by a
unit-modulus phase; the sample norms are therefore unchanged. -/
theorem trig_sum_shift_norm (S : Finset ℕ) (a : ℕ → ℂ) (M : ℕ)
    (hSM : ∀ n ∈ S, M ≤ n) (x : ℝ) :
    ‖lemma33TrigSum S a x‖ =
      ‖lemma33TrigSum (S.image (fun n => n-M)) (fun k => a (M+k)) x‖ := by
  classical
  have hinj : Set.InjOn (fun n : ℕ => n-M) S := by
    intro n hn m hm he
    have hnM := hSM n hn
    have hmM := hSM m hm
    dsimp only at he
    omega
  have hsum : lemma33TrigSum S a x =
      fourier (T := 1) (M : ℤ) (x : AddCircle (1 : ℝ)) *
        lemma33TrigSum (S.image (fun n => n-M)) (fun k => a (M+k)) x := by
    unfold lemma33TrigSum
    rw [Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnM := hSM n hn
    have hnadd : M + (n-M) = n := by omega
    have he : (n : ℤ) = (M : ℤ) + ((n-M : ℕ) : ℤ) := by omega
    dsimp only
    rw [hnadd, he, fourier_add]
    ring
  rw [hsum, norm_mul]
  have hnorm : ‖fourier (T := 1) (M : ℤ) (x : AddCircle (1 : ℝ))‖ = 1 :=
    Circle.norm_coe _
  rw [hnorm, one_mul]

/-- The additive large sieve for an arbitrary shifted finite interval of length `N`. -/
theorem shifted_additive_large_sieve {ι : Type*} (U : Finset ι) (x : ι → ℝ)
    (S : Finset ℕ) (a : ℕ → ℂ) {P : ℝ} (hP : 1 ≤ P) (M N : ℕ)
    (hN : (N : ℝ) ≤ P ^ 2) (hSN : ∀ n ∈ S, M ≤ n ∧ n ≤ M+N)
    (hx : ∀ i ∈ U, 0 ≤ x i ∧ x i ≤ 1)
    (hsep : ∀ i ∈ U, ∀ j ∈ U, i ≠ j → (8 * P ^ 2)⁻¹ ≤ |x i-x j|) :
    (∑ i ∈ U, ‖lemma33TrigSum S a (x i)‖ ^ 2) ≤
      (32 + Real.pi ^ 2) * P ^ 2 * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let T := S.image (fun n => n-M)
  have hTN : ∀ k ∈ T, k ≤ N := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have := hSN n hn
    omega
  have h := lemma33_additive_large_sieve U x T (fun k => a (M+k)) hP N hN hTN hx hsep
  have hSM : ∀ n ∈ S, M ≤ n := fun n hn => (hSN n hn).1
  have hinj : Set.InjOn (fun n : ℕ => n-M) S := by
    intro n hn m hm he
    have hnM := hSM n hn
    have hmM := hSM m hm
    dsimp only at he
    omega
  have henergy : (∑ k ∈ T, ‖a (M+k)‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have hnadd : M + (n-M) = n := by have := hSM n hn; omega
    exact congrArg (fun k => ‖a k‖ ^ 2) hnadd
  rw [henergy] at h
  simpa only [trig_sum_shift_norm S a M hSM, T] using h

end ZhangLS.Spec
