import ZhangLS.Spec.ShortUpsilonEnergy
import ZhangLS.Spec.Lemma31

/-! Genuine full P² L3.1 attachment for actual short-υ coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

noncomputable def shortUpsilonErrorEnergy {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ‖lemma83Kappa β n - shortUpsilonKappa χ β n‖^2*(n:ℝ)⁻¹

lemma shortUpsilon_error_energy_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (N : ℕ) : 0 ≤ shortUpsilonErrorEnergy χ β N := by
  unfold shortUpsilonErrorEnergy
  positivity

lemma shortUpsilon_harmonic_paper_bound {D N : ℕ} (hL : 1 ≤ lemma23PaperL D)
    (hN : 1 ≤ N) (hNP : N ≤ ⌊lemma23PaperP D^2⌋₊) :
    (harmonic N : ℝ) ≤ 3*lemma23PaperL D^9 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNP' : (N:ℝ) ≤ lemma23PaperP D^2 :=
    (show (N:ℝ) ≤ ⌊lemma23PaperP D^2⌋₊ by exact_mod_cast hNP).trans
      (Nat.floor_le (sq_nonneg _))
  have hh := Real.log_le_log hNp hNP'
  simp only [Real.log_pow, lemma23PaperP, Real.log_exp, Nat.cast_ofNat] at hh
  have hh1 : 1 ≤ lemma23PaperL D^9 := one_le_pow₀ hL
  exact (harmonic_le_one_add_log N).trans (by linarith)

lemma shortUpsilon_tail_restrict {D : ℕ} (χ : RealPrimitiveCharacter D) (N M : ℕ)
    (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ n‖^2*(n:ℝ)⁻¹) ≤
      ∑ n ∈ Finset.Ioc (D^4) M, ‖lemma23NuArithmeticFunction χ n‖^2*(n:ℝ)⁻¹ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc_right hNM
  · intros; positivity

/-- No D⁸-only input occurs: the actual full floor(P²) L3.1 tail is used. -/
theorem shortUpsilon_error_energy_sq_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ))
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0) (N : ℕ)
    (hNP : N ≤ ⌊lemma23PaperP D^2⌋₊) :
    shortUpsilonErrorEnergy χ β N ^ 2 ≤
      1260 * 3^80 * lemma23PaperL D^(-1291 : ℤ) := by
  have hLp : 0 < lemma23PaperL D := by linarith
  by_cases hN : N = 0
  · subst N
    simp only [shortUpsilonErrorEnergy, Finset.Icc_eq_empty_of_lt (by omega : (0:ℕ) < 1),
      Finset.sum_empty, zero_pow (by decide : 2≠0)]
    positivity
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have htail := (shortUpsilon_tail_restrict χ N _ hNP).trans
      (lemma31_actual_square_paper_tail_le χ hD hL hA hAbs)
    have hH := shortUpsilon_harmonic_paper_bound hL hN1 hNP
    have hH0 : 0 ≤ (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      positivity
    calc
      _ ≤ (∑ n ∈ Finset.Ioc (D^4) N,
          ‖lemma23NuArithmeticFunction χ n‖^2*(n:ℝ)⁻¹) * (harmonic N : ℝ)^80 :=
        shortUpsilon_error_energy_sq_le_tail_harmonic χ β hβ N hN1
      _ ≤ (1260*lemma23PaperL D^(-2011 : ℤ)) * (3*lemma23PaperL D^9)^80 :=
        mul_le_mul htail (pow_le_pow_left₀ hH0 hH 80)
          (by positivity) (by positivity)
      _ = 1260*3^80*(lemma23PaperL D^(-2011 : ℤ) * lemma23PaperL D^720) := by ring
      _ = _ := by
        congr 1
        simpa only [Int.reduceAdd, zpow_ofNat] using
          (zpow_add₀ hLp.ne' (-2011 : ℤ) 720).symm

lemma shortUpsilon_square_bound_to_integral_power (L S : ℝ) (hL : 1 ≤ L)
    (hS : 0 ≤ S) (hbound : S^2 ≤ 1260*3^80*L^(-1291 : ℤ)) :
    S ≤ 36*3^40*L^(-640 : ℤ) := by
  have hLp : 0 < L := by linarith
  have hz : L^(-1291 : ℤ) ≤ L^(-1290 : ℤ) :=
    zpow_le_zpow_right₀ hL (by norm_num)
  have hfactor : 1260*3^80*L^(-1291 : ℤ) ≤ (36*3^40*L^(-645 : ℤ))^2 := by
    calc
      _ ≤ 1296*3^80*L^(-1290 : ℤ) := by
        apply mul_le_mul _ hz (by positivity) (by positivity)
        norm_num
      _ = (36*3^40)^2 * (L^(-645 : ℤ))^2 := by
        rw [← zpow_natCast (L^(-645 : ℤ)) 2, ← zpow_mul]
        norm_num
      _ = _ := by ring
  have hs : S ≤ 36*3^40*L^(-645 : ℤ) :=
    (sq_le_sq₀ hS (by positivity)).mp (hbound.trans hfactor)
  exact hs.trans (mul_le_mul_of_nonneg_left
    (zpow_le_zpow_right₀ hL (by norm_num : (-645:ℤ) ≤ -640)) (by positivity))

theorem shortUpsilon_error_energy_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ))
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0) (N : ℕ)
    (hNP : N ≤ ⌊lemma23PaperP D^2⌋₊) :
    shortUpsilonErrorEnergy χ β N ≤ 36*3^40*lemma23PaperL D^(-640 : ℤ) :=
  shortUpsilon_square_bound_to_integral_power _ _ hL
    (shortUpsilon_error_energy_nonneg χ β N)
    (shortUpsilon_error_energy_sq_le χ hD hL hA hAbs β hβ N hNP)

/-- The single conductor threshold is selected before χ, pure shifts, and every endpoint N. -/
theorem shortUpsilon_uniform_actual_error_energy :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ β : Fin 3 → ℂ, (∀ j, (β j).re = 0) →
      ∀ N : ℕ, N ≤ ⌊lemma23PaperP D^2⌋₊ →
        shortUpsilonErrorEnergy χ β N^2 ≤ 1260*3^80*lemma23PaperL D^(-1291 : ℤ) ∧
        shortUpsilonErrorEnergy χ β N ≤ 36*3^40*lemma23PaperL D^(-640 : ℤ) := by
  obtain ⟨D₀, hD₀⟩ := lemma31_exponential_absorption_threshold
  refine ⟨D₀, ?_⟩
  intro D hD χ hA β hβ N hNP
  obtain ⟨hD1, hL3, hAbs⟩ := hD₀ D hD
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  exact ⟨shortUpsilon_error_energy_sq_le χ hD1 hL1 hA hAbs β hβ N hNP,
    shortUpsilon_error_energy_le χ hD1 hL1 hA hAbs β hβ N hNP⟩

/-- Any common mask of modulus at most one retains the same coefficient energy. -/
theorem shortUpsilon_masked_energy_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (N : ℕ) (mask : ℕ → ℂ)
    (hm : ∀ n ∈ Finset.Icc 1 N, ‖mask n‖ ≤ 1) :
    (∑ n ∈ Finset.Icc 1 N,
      ‖mask n*(lemma83Kappa β n-shortUpsilonKappa χ β n)‖^2*(n:ℝ)⁻¹) ≤
      shortUpsilonErrorEnergy χ β N := by
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hs : ‖mask n‖^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hm n hn) 2
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs
    (sq_nonneg ‖lemma83Kappa β n-shortUpsilonKappa χ β n‖)

end ZhangLS.Spec
