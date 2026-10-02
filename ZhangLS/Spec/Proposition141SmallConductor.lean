import ZhangLS.Spec.Proposition141Conductor

/-! # Section 14: the actual small-conductor prime bound

Only the independently proved *nonprincipal* port of Lemma 5.6 is used.
The conductor of χ·conj θ is bounded by D*conductor θ<D⁴, then compared
with the paper's T=exp((log D)^(11/10)).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Filter
open scoped ComplexConjugate

/-- The extra factor D in the product conductor is retained. -/
theorem proposition141_small_product_conductor_lt_fourth {D N : ℕ} [NeZero N]
    (χ : RealPrimitiveCharacter D) (hD : D ∣ N) (θ : DirichletCharacter ℂ N)
    (hr : θ.conductor < D^3) :
    (proposition141PrimeCharacter χ hD θ).conductor < D^4 := by
  have hDp : 0 < D := Nat.pos_of_ne_zero χ.modulus_ne_zero
  have hm := Nat.mul_lt_mul_of_pos_left hr hDp
  have he : D * D^3 = D^4 := by ring
  rw [he] at hm
  exact (proposition141_product_conductor_le χ hD θ).trans_lt hm

/-- A single D-threshold, independent of all character levels, places D⁴
below T. The threshold is chosen before χ, N, θ, and τ. -/
theorem proposition141_uniform_fourth_lt_T :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → (D : ℝ)^4 < lemma56PaperT D := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp : Tendsto (fun D : ℕ => lemma23PaperL D ^ (1/10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).comp ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hp.eventually (eventually_gt_atTop 4))
  refine ⟨max N 2,le_max_right _ _,?_⟩
  intro D hD
  have hD2 : 2 ≤ D := (le_max_right N 2).trans hD
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hL : 0 < lemma23PaperL D := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have he : (D : ℝ)^4 = Real.exp (4 * lemma23PaperL D) := by
    rw [mul_comm (4 : ℝ),Real.exp_mul]
    rw [show Real.exp (lemma23PaperL D) = (D : ℝ) from Real.exp_log hDp]
    norm_cast
  rw [he,lemma56PaperT]
  apply Real.exp_lt_exp.mpr
  have hh : lemma23PaperL D ^ (11/10 : ℝ) =
      lemma23PaperL D * lemma23PaperL D ^ (1/10 : ℝ) := by
    rw [show (11/10 : ℝ) = 1 + 1/10 by norm_num,Real.rpow_add hL,Real.rpow_one]
  rw [hh]
  nlinarith [hN D ((le_max_left N 2).trans hD)]

/-- Uniform prime decay for the primitive inducer of the actual product.
The two exclusions belong to θ; both exclusions required by 5.6 for the
product inducer are derived rather than assumed. -/
theorem proposition141_small_product_inducer_prime_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ {D N : ℕ} [NeZero N] (χ : RealPrimitiveCharacter D)
      (hD : D ∣ N) (θ : DirichletCharacter ℂ N),
      D₀ ≤ D → NormalizedAssumptionA χ → θ ≠ 1 →
      θ ≠ χ.chi.changeLevel hD → θ.conductor < D^3 →
      ∀ τ : ℝ, |τ| ≤ D →
        ‖lemma56PrimeSum D (proposition141PrimeCharacter χ hD θ).primitiveCharacter τ‖ ≤
          C * lemma56PrimeMass D * lemma56Decay D := by
  obtain ⟨C,hC,N₀,hbound⟩ := lemma56_uniform_primitive_prime_window_normalized_bound
  obtain ⟨N₁,hN₁,hT⟩ := proposition141_uniform_fourth_lt_T
  refine ⟨C,hC,max N₀ N₁,hN₁.trans (le_max_right _ _),?_⟩
  intro D N _ χ hd θ hDN hA hθ hne hr τ hτ
  have hD2 : 2 ≤ D := hN₁.trans ((le_max_right N₀ N₁).trans hDN)
  let ξ := proposition141PrimeCharacter χ hd θ
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  have hc := proposition141_actual_product_inducer_admissible χ hd θ hθ hne
  have hrT : (ξ.conductor : ℝ) < lemma56PaperT D := by
    have hfourth : (ξ.conductor : ℝ) < (D : ℝ)^4 := by
      exact_mod_cast proposition141_small_product_conductor_lt_fourth χ hd θ hr
    exact hfourth.trans (hT D ((le_max_right N₀ N₁).trans hDN))
  exact hbound χ ξ.primitiveCharacter ((le_max_left N₀ N₁).trans hDN)
    (by omega) hA hc.2.1 hc.1 hrT hc.2.2 τ hτ

/-- The prime sum actually occurring after the Mellin transform of (14.8). -/
noncomputable def proposition141ProductPrimeSum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N) (τ : ℝ) : ℂ :=
  ∑ p ∈ lemma56PaperPrimes D, χ.chi (p : ZMod D) * conj (θ (p : ZMod N)) *
    (p : ℂ) ^ (1 + I * (τ : ℂ))

/-- Prime-window evaluation is justified by p>N, which gives the unit
condition. Equality on all natural numbers would be false in general. -/
theorem proposition141_actual_prime_sum_eq_inducer {D N : ℕ} [NeZero N]
    (χ : RealPrimitiveCharacter D) (hD : D ∣ N) (θ : DirichletCharacter ℂ N)
    (hNP : (N : ℝ) ≤ lemma23PaperP D) (τ : ℝ) :
    proposition141ProductPrimeSum χ θ τ =
      lemma56PrimeSum D (proposition141PrimeCharacter χ hD θ).primitiveCharacter τ := by
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpp,hpP,_⟩ := (lemma56_mem_paper_primes D p).mp hp
  have hNp : N < p := by exact_mod_cast hNP.trans_lt hpP
  have hc : p.Coprime N := hpp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact (not_le_of_gt hNp) (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hd))
  rw [proposition141_product_inducer_eval χ hD θ p hc]

/-- The nonprincipal 5.6 estimate transferred to the actual χ·conj θ prime
sum in (14.8), with its original weights and height range. -/
theorem proposition141_small_actual_product_prime_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ {D N : ℕ} [NeZero N] (χ : RealPrimitiveCharacter D)
      (hD : D ∣ N) (θ : DirichletCharacter ℂ N),
      D₀ ≤ D → NormalizedAssumptionA χ → (N : ℝ) ≤ lemma23PaperP D →
      θ ≠ 1 → θ ≠ χ.chi.changeLevel hD → θ.conductor < D^3 →
      ∀ τ : ℝ, |τ| ≤ D →
        ‖proposition141ProductPrimeSum χ θ τ‖ ≤
          C * lemma56PrimeMass D * lemma56Decay D := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_small_product_inducer_prime_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D N _ χ hd θ hDN hA hNP hθ hne hr τ hτ
  rw [proposition141_actual_prime_sum_eq_inducer χ hd θ hNP τ]
  exact hbound χ hd θ hDN hA hθ hne hr τ hτ

end ZhangLS.Spec
