import ZhangLS.Spec.Lemma151WeightedError
import ZhangLS.Spec.RoughCollisionArithmetic
import ZhangLS.Spec.Lemma31

/-! Appendix B.1 with the actual coefficients. The paper cites Lemma 3.2 outside
its D^8 upper endpoint. We instead use the already-proved linear ν-tail in the
Lemma 3.1 chain, valid through floor(P^2), and retain assumption (A). -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- Q excludes primes strictly below D^4. A rough h>1 is nevertheless strictly
above D^4: equality would force D^4 itself to be prime, which is impossible. -/
theorem appendixB_rough_gt_fourth {D h : ℕ} (hh : 1<h)
    (hrough : h.Coprime (lemma151Q D)) : D^4<h := by
  obtain ⟨p,hp,hph⟩ := Nat.exists_prime_and_dvd (by omega : h≠1)
  have hlo := roughCollision_common_prime_lower hrough hp hph
  have hhi := Nat.le_of_dvd (by omega : 0<h) hph
  have hne : p≠D^4 := by
    intro he
    exact (Nat.Prime.not_prime_pow (x := D) (by decide : 2≤4)) (he ▸ hp)
  omega

/-- Finite rectangle bound before any asymptotic estimate. It retains the
original strict-Q rough domain and every actual ν coefficient. -/
theorem appendixB_rough_arithmetic_error_finite {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (S : Finset ℕ)
    (hS : ∀ n∈S, 0<n ∧ n≤N ∧ n.Coprime (lemma151Q D))
    (w : ℕ→ℂ) (W : ℝ) (hW : 0≤W) (hw : ∀ n∈S, ‖w n‖≤W) :
    lemma151ArithmeticReplacementError χ S w ≤
      W*(harmonic N : ℝ)^2*
        ∑ h∈Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ h‖/(h : ℝ) := by
  let A : Finset (Σ n : ℕ, ℕ×ℕ) :=
    S.sigma fun n => n.divisorsAntidiagonal.filter (fun a => a.2≠1)
  let pairOf (x : Σ n : ℕ, ℕ×ℕ) : ℕ×ℕ := x.2
  let weight (a : ℕ×ℕ) : ℝ :=
    (a.1.divisors.card : ℝ)/(a.1 : ℝ)*
      (‖lemma23NuArithmeticFunction χ a.2‖/(a.2 : ℝ))
  have hnonneg : ∀ a, 0≤weight a := by intro a; dsimp [weight]; positivity
  have hA (x) (hx : x∈A) : x.2∈x.1.divisorsAntidiagonal ∧ x.2.2≠1 :=
    mem_filter.mp (mem_sigma.mp hx).2
  have hinj : Set.InjOn pairOf A := by
    intro x hx y hy hxy
    rcases x with ⟨nx,px⟩
    rcases y with ⟨ny,py⟩
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp (hA _ hx).1).1
    have hyprod := (Nat.mem_divisorsAntidiagonal.mp (hA _ hy).1).1
    change px.1*px.2=nx at hxprod
    change py.1*py.2=ny at hyprod
    have hxy' : px=py := hxy
    have hn : nx=ny := by rw [←hxprod,←hyprod,hxy']
    exact Sigma.ext hn (heq_of_eq hxy')
  have hsub : A.image pairOf ⊆ Icc 1 N ×ˢ Ioc (D^4) N := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    have hn := hS _ (mem_sigma.mp hx).1
    have hp := (Nat.mem_divisorsAntidiagonal.mp (hA _ hx).1).1
    have hpos₁ : 0<x.2.1 := Nat.pos_of_ne_zero (by
      intro hz
      rw [hz,zero_mul] at hp
      exact hn.1.ne' hp.symm)
    have hpos₂ : 0<x.2.2 := Nat.pos_of_ne_zero (by
      intro hz
      rw [hz,mul_zero] at hp
      exact hn.1.ne' hp.symm)
    have hdiv₁ : x.2.1∣x.1 := ⟨x.2.2,hp.symm⟩
    have hdiv₂ : x.2.2∣x.1 := ⟨x.2.1,by rw [mul_comm]; exact hp.symm⟩
    have hrough := Nat.Coprime.of_dvd_left hdiv₂ hn.2.2
    have hlo := appendixB_rough_gt_fourth (by have := (hA _ hx).2; omega) hrough
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hpos₁,(Nat.le_of_dvd hn.1 hdiv₁).trans hn.2.1⟩,
      mem_Ioc.mpr ⟨hlo,(Nat.le_of_dvd hn.1 hdiv₂).trans hn.2.1⟩⟩
  have hexpand : lemma151ArithmeticReplacementError χ S w =
      ∑ x∈A, ‖w x.1‖/(x.1 : ℝ)*
        ((x.2.1.divisors.card : ℝ)*‖lemma23NuArithmeticFunction χ x.2.2‖) := by
    unfold lemma151ArithmeticReplacementError
    rw [sum_sigma]
    apply sum_congr rfl
    intro n hn
    dsimp only
    rw [←mul_sum,sum_filter]
    congr 1
    apply sum_congr rfl
    intro a ha
    split_ifs <;> simp_all
  have hweight : ∀ x∈A, (x.2.1.divisors.card : ℝ)*
      ‖lemma23NuArithmeticFunction χ x.2.2‖/(x.1 : ℝ)=weight x.2 := by
    intro x hx
    have hp := (Nat.mem_divisorsAntidiagonal.mp (hA _ hx).1).1
    dsimp [weight]
    rw [←hp,Nat.cast_mul]
    ring
  calc
    _ = ∑ x∈A, ‖w x.1‖/(x.1 : ℝ)*
        ((x.2.1.divisors.card : ℝ)*‖lemma23NuArithmeticFunction χ x.2.2‖) := hexpand
    _ ≤ ∑ x∈A, W*weight x.2 := by
      apply sum_le_sum
      intro x hx
      calc
        _ = ‖w x.1‖*((x.2.1.divisors.card : ℝ)*
            ‖lemma23NuArithmeticFunction χ x.2.2‖/(x.1 : ℝ)) := by ring
        _ = ‖w x.1‖*weight x.2 := by rw [hweight x hx]
        _ ≤ W*weight x.2 := mul_le_mul_of_nonneg_right (hw _ (mem_sigma.mp hx).1) (hnonneg _)
    _ = W*∑ a∈A.image pairOf, weight a := by rw [sum_image hinj,mul_sum]
    _ ≤ W*∑ a∈Icc 1 N ×ˢ Ioc (D^4) N, weight a :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (by intros; exact hnonneg _)) hW
    _ = W*((∑ m∈Icc 1 N, (m.divisors.card : ℝ)/(m : ℝ))*
        ∑ h∈Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ h‖/(h : ℝ)) := by
      dsimp only [weight]
      rw [Finset.sum_product' (Icc 1 N) (Ioc (D^4) N)
        (fun m h : ℕ => (m.divisors.card : ℝ)/(m : ℝ)*
          (‖lemma23NuArithmeticFunction χ h‖/(h : ℝ))),←sum_mul_sum]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (by simpa only [div_eq_mul_inv] using lemma23_divisor_weighted_sum_le_harmonic_sq N)
          (sum_nonneg (by intros; positivity))) hW

/-- A genuine ν-tail on the required interval, retaining assumption (A).
This is stronger than the Cauchy consequence of Lemma 3.1's square tail. -/
theorem appendixB_actual_nu_tail {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹≤lemma23PaperL D^(-2013 : ℤ))
    (hN : N≤lemma31PaperCutoff D) :
    (∑ h∈Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ h‖/(h : ℝ)) ≤
      21*lemma23PaperL D^(-2013 : ℤ) := by
  have hpow : D^2≤D^4 := pow_le_pow_right₀ (by omega : 1≤D) (by decide)
  calc
    _ ≤ ∑ h∈Ioc (D^2) (lemma31PaperCutoff D),
        ‖lemma23NuArithmeticFunction χ h‖/(h : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (by
        intro h hh
        exact mem_Ioc.mpr ⟨lt_of_le_of_lt hpow (mem_Ioc.mp hh).1,(mem_Ioc.mp hh).2.trans hN⟩)
        (by intros; positivity)
    _ ≤ _ := by simpa only [lemma31_nu_real_eq_norm,div_eq_mul_inv] using
      lemma31_nu_linear_paper_tail_le χ hD hL hA hAbs

/-- B.1, quantitatively and uniformly in every bounded external weight.
The cutoff may be closed at P^2, which contains the original strict n<P set. -/
theorem appendixB_weighted_B1_explicit {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹≤lemma23PaperL D^(-2013 : ℤ))
    {β : ℂ} (hβ : β.re=0) (S : Finset ℕ)
    (hS : ∀ n∈S, 0<n ∧ n≤lemma31PaperCutoff D ∧ n.Coprime (lemma151Q D))
    (w : ℕ→ℂ) (W : ℝ) (hW : 0≤W) (hw : ∀ n∈S, ‖w n‖≤W) :
    ‖(∑ n∈S, w n*lemma151RhoStar χ β n/n)-
      (∑ n∈S, w n*lemma151Rho β n/n)‖ ≤
      189*W*lemma23PaperL D^(-1995 : ℤ) := by
  have hl : 0<lemma23PaperL D := by linarith
  have hh : 0≤(harmonic (lemma31PaperCutoff D) : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    positivity
  have hH := (harmonic_le_one_add_log (lemma31PaperCutoff D)).trans
    (lemma31_paper_cutoff_log_factor_le hD hL)
  have hHs : (harmonic (lemma31PaperCutoff D) : ℝ)^2≤9*lemma23PaperL D^18 := by
    have := pow_le_pow_left₀ hh hH 2
    nlinarith only [this]
  have he : lemma23PaperL D^18*lemma23PaperL D^(-2013 : ℤ)=
      lemma23PaperL D^(-1995 : ℤ) := by
    simpa only [Int.reduceAdd,zpow_ofNat] using
      (zpow_add₀ hl.ne' (18 : ℤ) (-2013 : ℤ)).symm
  calc
    _ ≤ lemma151ArithmeticReplacementError χ S w :=
      lemma151_weighted_rhostar_replacement χ hβ S w
    _ ≤ W*(harmonic (lemma31PaperCutoff D) : ℝ)^2*
        ∑ h∈Ioc (D^4) (lemma31PaperCutoff D), ‖lemma23NuArithmeticFunction χ h‖/(h : ℝ) :=
      appendixB_rough_arithmetic_error_finite χ S hS w W hW hw
    _ ≤ W*(9*lemma23PaperL D^18)*(21*lemma23PaperL D^(-2013 : ℤ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hHs hW)
        (appendixB_actual_nu_tail χ hD hL hA hAbs le_rfl)
        (sum_nonneg (by intros; positivity)) (by positivity)
    _ = _ := by rw [show W*(9*lemma23PaperL D^18)*(21*lemma23PaperL D^(-2013 : ℤ))=
        189*W*(lemma23PaperL D^18*lemma23PaperL D^(-2013 : ℤ)) by ring,he]

/-- Uniform version of B.1; the threshold is independent of χ, j, the finite
cutoff, and the external bounded weight. No contradiction to (A) is used. -/
theorem appendixB_weighted_B1_uniform :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ β : ℂ, β.re=0 → ∀ S : Finset ℕ,
      (∀ n∈S, 0<n ∧ n≤lemma31PaperCutoff D ∧ n.Coprime (lemma151Q D)) →
      ∀ w : ℕ→ℂ, ∀ W : ℝ, 0≤W → (∀ n∈S, ‖w n‖≤W) →
      ‖(∑ n∈S, w n*lemma151RhoStar χ β n/n)-
        (∑ n∈S, w n*lemma151Rho β n/n)‖≤189*W*lemma23PaperL D^(-1995 : ℤ) := by
  obtain ⟨D₀,hD₀⟩ := lemma31_exponential_absorption_threshold
  refine ⟨D₀,?_⟩
  intro D hD χ hA β hβ S hS w W hW hw
  have hh := hD₀ D hD
  exact appendixB_weighted_B1_explicit χ hh.1 (by linarith [hh.2.1]) hA hh.2.2
    hβ S hS w W hW hw

end ZhangLS.Spec
