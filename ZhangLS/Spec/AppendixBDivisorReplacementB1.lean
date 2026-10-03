import ZhangLS.Spec.AppendixBDivisorNuTail

/-! A divisor-weighted B.1 rectangle on the original strict-Q rough domain. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- The same actual arithmetic error with τ₂-sized weights. -/
theorem appendixB_divisor_arithmetic_error_finite {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (S : Finset ℕ)
    (hS : ∀ n∈S, 0<n ∧ n≤N ∧ n.Coprime (lemma151Q D))
    (w : ℕ→ℂ) (W : ℝ) (hW : 0≤W) (hw : ∀ n∈S, ‖w n‖≤W*(lemma34Tau 2 n : ℝ)) :
    lemma151ArithmeticReplacementError χ S w ≤
      W*(harmonic N : ℝ)^4*
        ∑ h∈Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ h‖*(lemma34Tau 2 h : ℝ)/(h : ℝ) := by
  let A : Finset (Σ n : ℕ, ℕ×ℕ) :=
    S.sigma fun n => n.divisorsAntidiagonal.filter (fun a => a.2≠1)
  let pairOf (x : Σ n : ℕ, ℕ×ℕ) : ℕ×ℕ := x.2
  let weight (a : ℕ×ℕ) : ℝ :=
    (lemma34Tau 2 a.1 : ℝ)^2/(a.1 : ℝ)*
      (‖lemma23NuArithmeticFunction χ a.2‖*(lemma34Tau 2 a.2 : ℝ)/(a.2 : ℝ))
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
  calc
    _ = ∑ x∈A, ‖w x.1‖/(x.1 : ℝ)*
        ((x.2.1.divisors.card : ℝ)*‖lemma23NuArithmeticFunction χ x.2.2‖) := hexpand
    _ ≤ ∑ x∈A, W*weight x.2 := by
      apply sum_le_sum
      intro x hx
      have hp := (Nat.mem_divisorsAntidiagonal.mp (hA _ hx).1).1
      have hτ : (lemma34Tau 2 x.1 : ℝ) ≤
          (lemma34Tau 2 x.2.1 : ℝ)*(lemma34Tau 2 x.2.2 : ℝ) := by
        rw [←hp]
        exact_mod_cast proposition71_tau_submultiplicative 2 x.2.1 x.2.2
      have hw' := (hw _ (mem_sigma.mp hx).1).trans
        (mul_le_mul_of_nonneg_left hτ hW)
      calc
        _ ≤ (W*((lemma34Tau 2 x.2.1 : ℝ)*(lemma34Tau 2 x.2.2 : ℝ)))/(x.1 : ℝ)*
            ((x.2.1.divisors.card : ℝ)*‖lemma23NuArithmeticFunction χ x.2.2‖) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hw' (by positivity)) (by positivity)
        _ = W*weight x.2 := by
          dsimp [weight]
          rw [←hp,Nat.cast_mul,←lemma34_tau2_eq_divisor_card]
          ring
    _ = W*∑ a∈A.image pairOf, weight a := by rw [sum_image hinj,mul_sum]
    _ ≤ W*∑ a∈Icc 1 N ×ˢ Ioc (D^4) N, weight a :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (by intros; exact hnonneg _)) hW
    _ = W*((∑ m∈Icc 1 N, (lemma34Tau 2 m : ℝ)^2/(m : ℝ))*
        ∑ h∈Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ h‖*(lemma34Tau 2 h : ℝ)/(h : ℝ)) := by
      dsimp only [weight]
      rw [Finset.sum_product' (Icc 1 N) (Ioc (D^4) N)
        (fun m h : ℕ => (lemma34Tau 2 m : ℝ)^2/(m : ℝ)*
          (‖lemma23NuArithmeticFunction χ h‖*(lemma34Tau 2 h : ℝ)/(h : ℝ))),←sum_mul_sum]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (appendixB_tau_two_harmonic_energy N)
          (sum_nonneg (by intros; positivity))) hW


/-- Quantitative bound for the original error object, from the actual ν square
 tail. No pointwise bound or extension of Lemma 3.2 is postulated. -/
theorem appendixB_divisor_arithmetic_error_explicit {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹≤lemma23PaperL D^(-2013 : ℤ))
    (S : Finset ℕ)
    (hS : ∀ n∈S, 0<n ∧ n≤lemma31PaperCutoff D ∧ n.Coprime (lemma151Q D))
    (w : ℕ→ℂ) (W : ℝ) (hW : 0≤W)
    (hw : ∀ n∈S, ‖w n‖≤W*(lemma34Tau 2 n : ℝ)) :
    lemma151ArithmeticReplacementError χ S w ≤
      25920*W*lemma23PaperL D^(-951 : ℤ) := by
  have hl : 0<lemma23PaperL D := by linarith
  have hh : 0≤(harmonic (lemma31PaperCutoff D) : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    positivity
  have hH := (harmonic_le_one_add_log (lemma31PaperCutoff D)).trans
    (lemma31_paper_cutoff_log_factor_le hD hL)
  have hHs : (harmonic (lemma31PaperCutoff D) : ℝ)^4≤81*lemma23PaperL D^36 := by
    convert pow_le_pow_left₀ hh hH 4 using 1 <;> ring
  have he : lemma23PaperL D^36*lemma23PaperL D^(-987 : ℤ)=
      lemma23PaperL D^(-951 : ℤ) := by
    simpa only [Int.reduceAdd,zpow_ofNat] using
      (zpow_add₀ hl.ne' (36 : ℤ) (-987 : ℤ)).symm
  calc
    _ ≤ W*(harmonic (lemma31PaperCutoff D) : ℝ)^4*
        ∑ h∈Ioc (D^4) (lemma31PaperCutoff D),
          ‖lemma23NuArithmeticFunction χ h‖*(lemma34Tau 2 h : ℝ)/(h : ℝ) :=
      appendixB_divisor_arithmetic_error_finite χ S hS w W hW hw
    _ ≤ W*(81*lemma23PaperL D^36)*(320*lemma23PaperL D^(-987 : ℤ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hHs hW)
        (appendixB_actual_divisor_nu_tail χ hD hL hA hAbs le_rfl)
        (sum_nonneg (by intros; positivity)) (by positivity)
    _ = _ := by rw [show W*(81*lemma23PaperL D^36)*(320*lemma23PaperL D^(-987 : ℤ))=
        25920*W*(lemma23PaperL D^36*lemma23PaperL D^(-987 : ℤ)) by ring,he]

/-- Genuine divisor-weighted rho-star to rho replacement at any imaginary shift. -/
theorem appendixB_divisor_weighted_B1_explicit {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹≤lemma23PaperL D^(-2013 : ℤ))
    {β : ℂ} (hβ : β.re=0) (S : Finset ℕ)
    (hS : ∀ n∈S, 0<n ∧ n≤lemma31PaperCutoff D ∧ n.Coprime (lemma151Q D))
    (w : ℕ→ℂ) (W : ℝ) (hW : 0≤W)
    (hw : ∀ n∈S, ‖w n‖≤W*(lemma34Tau 2 n : ℝ)) :
    ‖(∑ n∈S, w n*lemma151RhoStar χ β n/n)-
      (∑ n∈S, w n*lemma151Rho β n/n)‖ ≤
      25920*W*lemma23PaperL D^(-951 : ℤ) :=
  (lemma151_weighted_rhostar_replacement χ hβ S w).trans
    (appendixB_divisor_arithmetic_error_explicit χ hD hL hA hAbs S hS w W hW hw)

/-- The finite actual beta shifts with c fixed before the common conductor
 threshold. This arithmetic estimate needs neither a bound on c nor on n₁. -/
theorem appendixB_divisor_weighted_B1_uniform (c : ℝ) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ S : Finset ℕ,
      (∀ n∈S, 0<n ∧ n≤lemma31PaperCutoff D ∧ n.Coprime (lemma151Q D)) →
      ∀ w : ℕ→ℂ, ∀ W : ℝ, 0≤W → (∀ n∈S, ‖w n‖≤W*(lemma34Tau 2 n : ℝ)) →
      ‖(∑ n∈S, w n*lemma151RhoStar χ (lemma83PaperBeta D c j) n/n)-
        (∑ n∈S, w n*lemma151Rho (lemma83PaperBeta D c j) n/n)‖ ≤
        25920*W*lemma23PaperL D^(-951 : ℤ) := by
  obtain ⟨D₀,hD₀⟩ := lemma31_exponential_absorption_threshold
  refine ⟨D₀,?_⟩
  intro D hD χ hA j S hS w W hW hw
  have hh := hD₀ D hD
  exact appendixB_divisor_weighted_B1_explicit χ hh.1 (by linarith [hh.2.1]) hA hh.2.2
    (lemma83_beta_re D c j) S hS w W hW hw

end ZhangLS.Spec
