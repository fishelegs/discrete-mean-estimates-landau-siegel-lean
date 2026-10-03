import ZhangLS.Spec.ShortUpsilonArithmetic
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta
set_option maxHeartbeats 2000000

theorem shortUpsilon_weighted_convolution_le (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ((f*g) n) * (n : ℝ)⁻¹) ≤
      (∑ n ∈ Finset.Icc 1 X, (f n) * (n : ℝ)⁻¹) *
      (∑ n ∈ Finset.Icc 1 X, (g n) * (n : ℝ)⁻¹) := by
  classical
  let S : Finset (Σ n : ℕ, ℕ × ℕ) :=
    (Finset.Icc 1 X).sigma fun n => n.divisorsAntidiagonal
  let R : Finset (ℕ × ℕ) := Finset.Icc 1 X ×ˢ Finset.Icc 1 X
  let pairOf (x : Σ n : ℕ, ℕ × ℕ) : ℕ × ℕ := x.2
  let weight (p : ℕ × ℕ) : ℝ :=
    ((f p.1) * (p.1 : ℝ)⁻¹) * ((g p.2) * (p.2 : ℝ)⁻¹)
  have hsum_expand :
      (∑ n ∈ Finset.Icc 1 X, ((f*g) n) * (n : ℝ)⁻¹) =
      ∑ x ∈ S, (f x.2.1 * g x.2.2) * (x.1 : ℝ)⁻¹ := by
    simp only [ArithmeticFunction.mul_apply,Finset.sum_mul]
    exact (Finset.sum_sigma (Finset.Icc 1 X) (fun n => n.divisorsAntidiagonal)
      (fun x : Σ n : ℕ, ℕ × ℕ => (f x.2.1 * g x.2.2) * (x.1 : ℝ)⁻¹)).symm
  have hpair_inj : Set.InjOn pairOf S := by
    intro x hx y hy hxy
    rcases x with ⟨nx, px⟩
    rcases y with ⟨ny, py⟩
    simp only [pairOf] at hxy
    have hpx : px ∈ nx.divisorsAntidiagonal := (Finset.mem_sigma.mp hx).2
    have hpy : py ∈ ny.divisorsAntidiagonal := (Finset.mem_sigma.mp hy).2
    have hnx : px.1 * px.2 = nx := (Nat.mem_divisorsAntidiagonal.mp hpx).1
    have hny : py.1 * py.2 = ny := (Nat.mem_divisorsAntidiagonal.mp hpy).1
    have hfst : nx = ny := by rw [← hnx, ← hny, hxy]
    exact Sigma.ext hfst (heq_of_eq hxy)
  have himage_subset : S.image pairOf ⊆ R := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
    let n := x.1
    let q := x.2
    have hmem := Finset.mem_sigma.mp hx
    have hn : n ∈ Finset.Icc 1 X := hmem.1
    have hq : q ∈ n.divisorsAntidiagonal := hmem.2
    have hprod : q.1 * q.2 = n := (Nat.mem_divisorsAntidiagonal.mp hq).1
    have hnle : n ≤ X := (Finset.mem_Icc.mp hn).2
    have hnpos : 0 < n := lt_of_lt_of_le (by decide) (Finset.mem_Icc.mp hn).1
    have hq1 : 0 < q.1 := Nat.pos_of_ne_zero (by
      intro hzero
      rw [hzero, zero_mul] at hprod
      omega)
    have hq2 : 0 < q.2 := Nat.pos_of_ne_zero (by
      intro hzero
      rw [hzero, mul_zero] at hprod
      omega)
    have hq1le : q.1 ≤ X := (Nat.le_mul_of_pos_right q.1 hq2).trans (hprod ▸ hnle)
    have hq2le : q.2 ≤ X := (Nat.le_mul_of_pos_left q.2 hq1).trans (hprod ▸ hnle)
    simp only [R, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq1), hq1le⟩,
      ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq2), hq2le⟩⟩
  have hsum_reindex :
      (∑ x ∈ S, (f x.2.1 * g x.2.2) * (x.1 : ℝ)⁻¹) = ∑ p ∈ S.image pairOf, weight p := by
    rw [Finset.sum_image hpair_inj]
    apply Finset.sum_congr rfl
    intro x hx
    let n := x.1
    let q := x.2
    have hmem := Finset.mem_sigma.mp hx
    have hn : n ∈ Finset.Icc 1 X := hmem.1
    have hq : q ∈ n.divisorsAntidiagonal := hmem.2
    have hprod : q.1 * q.2 = n := (Nat.mem_divisorsAntidiagonal.mp hq).1
    simp only [pairOf, weight]
    change (f q.1 * g q.2) * (n : ℝ)⁻¹ =
      ((f q.1) * (q.1 : ℝ)⁻¹) * ((g q.2) * (q.2 : ℝ)⁻¹)
    rw [← hprod, Nat.cast_mul, mul_inv]
    ring
  have hsum_rect :
      (∑ p ∈ S.image pairOf, weight p) ≤ ∑ p ∈ R, weight p :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_subset (by
      intro p hp hnot
      simp only [weight]
      exact mul_nonneg (mul_nonneg (hf _) (by positivity)) (mul_nonneg (hg _) (by positivity)))
  have hrect :
      (∑ p ∈ R, weight p) =
      (∑ n ∈ Finset.Icc 1 X, (f n) * (n : ℝ)⁻¹) *
      (∑ n ∈ Finset.Icc 1 X, (g n) * (n : ℝ)⁻¹) := by
    change (∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
      ((f p.1) * (p.1 : ℝ)⁻¹) * ((g p.2) * (p.2 : ℝ)⁻¹)) = _
    rw [Finset.sum_product' (Finset.Icc 1 X) (Finset.Icc 1 X)
      (fun a b : ℕ => ((f a) * (a : ℝ)⁻¹) * ((g b) * (b : ℝ)⁻¹)),
      ← Finset.sum_mul_sum]
  calc
    _ = ∑ x ∈ S, (f x.2.1 * g x.2.2) * (x.1 : ℝ)⁻¹ := hsum_expand
    _ = ∑ p ∈ S.image pairOf, weight p := hsum_reindex
    _ ≤ ∑ p ∈ R, weight p := hsum_rect
    _ = _ := hrect

/-- Divisor Cauchy, with the exact number of divisor pairs. -/
theorem shortUpsilon_convolution_sq_le (f g : ArithmeticFunction ℂ) (n : ℕ) :
    ‖(f*g) n‖^2 ≤ (lemma34Tau 2 n : ℝ) *
      ∑ q ∈ n.divisorsAntidiagonal, ‖f q.1‖^2*‖g q.2‖^2 := by
  have hnorm : ‖(f*g) n‖ ≤
      ∑ q ∈ n.divisorsAntidiagonal, ‖f q.1*g q.2‖ := by
    simpa only [ArithmeticFunction.mul_apply] using
      norm_sum_le n.divisorsAntidiagonal (fun q => f q.1*g q.2)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq n.divisorsAntidiagonal
    (fun _ => (1:ℝ)) (fun q => ‖f q.1*g q.2‖)
  have hcard : n.divisorsAntidiagonal.card = lemma34Tau 2 n := by
    rw [lemma34_tau2_eq_divisor_card, ← Nat.map_div_right_divisors]
    simp
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (by simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
      hcard, norm_mul, mul_pow] using hcs)

noncomputable def shortUpsilonEnergyWeight (f : ArithmeticFunction ℂ) : ArithmeticFunction ℝ :=
  ⟨fun n => ‖f n‖^2 * (lemma34Tau 2 n : ℝ), by simp⟩

@[simp] lemma shortUpsilon_energyWeight_apply (f : ArithmeticFunction ℂ) (n : ℕ) :
    shortUpsilonEnergyWeight f n = ‖f n‖^2*(lemma34Tau 2 n : ℝ) := rfl

lemma shortUpsilon_energyWeight_nonneg (f : ArithmeticFunction ℂ) (n : ℕ) :
    0 ≤ shortUpsilonEnergyWeight f n := by
  rw [shortUpsilon_energyWeight_apply]
  positivity

theorem shortUpsilon_convolution_sq_le_weight_convolution
    (f g : ArithmeticFunction ℂ) (n : ℕ) :
    ‖(f*g) n‖^2 ≤ (shortUpsilonEnergyWeight f * shortUpsilonEnergyWeight g) n := by
  apply (shortUpsilon_convolution_sq_le f g n).trans
  rw [ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hp := (Nat.mem_divisorsAntidiagonal.mp hq).1
  have ht : (lemma34Tau 2 n : ℝ) ≤
      (lemma34Tau 2 q.1 : ℝ)*(lemma34Tau 2 q.2 : ℝ) := by
    rw [← hp]
    exact_mod_cast proposition71_tau_submultiplicative 2 q.1 q.2
  simp only [shortUpsilon_energyWeight_apply]
  calc
    _ ≤ ((lemma34Tau 2 q.1 : ℝ)*(lemma34Tau 2 q.2 : ℝ)) *
        (‖f q.1‖^2*‖g q.2‖^2) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    _ = _ := by ring

/-- The rectangular enlargement is only in the nonnegative error estimate. -/
theorem shortUpsilon_convolution_harmonic_energy_le (f g : ArithmeticFunction ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ‖(f*g) n‖^2 * (n:ℝ)⁻¹) ≤
      (∑ n ∈ Finset.Icc 1 N, ‖f n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹) *
      (∑ n ∈ Finset.Icc 1 N, ‖g n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        (shortUpsilonEnergyWeight f * shortUpsilonEnergyWeight g) n * (n:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (shortUpsilon_convolution_sq_le_weight_convolution f g n)
        (by positivity)
    _ ≤ _ := shortUpsilon_weighted_convolution_le _ _
      (shortUpsilon_energyWeight_nonneg f) (shortUpsilon_energyWeight_nonneg g) N

lemma shortUpsilon_tau_two_fourth_le (n : ℕ) :
    (lemma34Tau 2 n : ℝ)^4 ≤ (lemma34Tau 16 n : ℝ) := by
  have h2 := lemma34_tau_square_le_real 2 n (by norm_num)
  have h4 := lemma34_tau_square_le_real 4 n (by norm_num)
  norm_num only [Nat.reduceMul] at h2 h4
  calc
    _ = ((lemma34Tau 2 n : ℝ)^2)^2 := by ring
    _ ≤ (lemma34Tau 4 n : ℝ)^2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
    _ ≤ _ := h4

lemma shortUpsilon_tau_four_sq_times_two_le (n : ℕ) :
    (lemma34Tau 4 n : ℝ)^2*(lemma34Tau 2 n : ℝ) ≤ (lemma34Tau 32 n : ℝ) := by
  calc
    _ ≤ (lemma34Tau 16 n : ℝ)*(lemma34Tau 2 n : ℝ) :=
      mul_le_mul_of_nonneg_right (lemma34_tau_square_le_real 4 n (by norm_num))
        (Nat.cast_nonneg _)
    _ ≤ _ := lemma34_tau_product_le_real 16 2 n (by norm_num) (by norm_num)

lemma shortUpsilon_fourfold_harmonic_weight_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      ‖shortUpsilonFourfold χ β n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹) ≤
      (harmonic N : ℝ)^32 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (lemma34Tau 32 n : ℝ)*(n:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (shortUpsilon_fourfold_norm_le_tau_four χ β hβ n) 2)
        (Nat.cast_nonneg _)).trans (shortUpsilon_tau_four_sq_times_two_le n)
    _ ≤ _ := lemma34_tau_weighted_sum_le_harmonic_pow 32 N hN

lemma shortUpsilon_nu_norm_le_tau_two {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23NuArithmeticFunction χ n‖ ≤ (lemma34Tau 2 n : ℝ) := by
  rw [lemma34_tau2_eq_divisor_card]
  exact lemma23NuArithmeticFunction_norm_le_card_divisors χ n

lemma shortUpsilon_nu_mixed_weight_le {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23NuArithmeticFunction χ n‖^2 * (lemma34Tau 2 n : ℝ)^2 ≤
      (lemma34Tau 16 n : ℝ) := by
  calc
    _ ≤ (lemma34Tau 2 n : ℝ)^2 * (lemma34Tau 2 n : ℝ)^2 :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (shortUpsilon_nu_norm_le_tau_two χ n) 2) (sq_nonneg _)
    _ = (lemma34Tau 2 n : ℝ)^4 := by ring
    _ ≤ _ := shortUpsilon_tau_two_fourth_le n

lemma shortUpsilon_tail_harmonic_weight_sq_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc (D^4) N,
      ‖lemma23UpsilonArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹)^2 ≤
      (∑ n ∈ Finset.Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ n‖^2*(n:ℝ)⁻¹) *
        (harmonic N : ℝ)^16 := by
  have hnu : (∑ n ∈ Finset.Ioc (D^4) N,
      ‖lemma23UpsilonArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹) ≤
      ∑ n ∈ Finset.Ioc (D^4) N,
        ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro n hn
    gcongr
    exact shortUpsilon_norm_le_nu χ n
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Ioc (D^4) N)
    (r := fun n => ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹)
    (f := fun n => ‖lemma23NuArithmeticFunction χ n‖^2*(n:ℝ)⁻¹)
    (g := fun n => ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2*(n:ℝ)⁻¹)
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun _ _ => by ring_nf; rfl)
  have hmoment : (∑ n ∈ Finset.Ioc (D^4) N,
      ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2*(n:ℝ)⁻¹) ≤
      (harmonic N : ℝ)^16 := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc (D^4) N, (lemma34Tau 16 n : ℝ)*(n:ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_right (shortUpsilon_nu_mixed_weight_le χ n) (by positivity)
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (lemma34Tau 16 n : ℝ)*(n:ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_Ioc, Finset.mem_Icc] at *
          omega
        · intros; positivity
      _ ≤ _ := lemma34_tau_weighted_sum_le_harmonic_pow 16 N hN
  exact (pow_le_pow_left₀ (by positivity) hnu 2).trans
    (hcs.trans (mul_le_mul_of_nonneg_left hmoment (by positivity)))

lemma shortUpsilon_difference_weight_identity {D : ℕ} (χ : RealPrimitiveCharacter D) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      ‖(lemma23UpsilonArithmeticFunction χ - shortUpsilon χ) n‖^2 *
        (lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹) =
    ∑ n ∈ Finset.Ioc (D^4) N,
      ‖lemma23UpsilonArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹ := by
  have hs : (Finset.Icc 1 N).filter (fun n => D^4 < n) = Finset.Ioc (D^4) N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [shortUpsilon_sub_apply, shortUpsilon_apply]
  split_ifs <;> simp_all <;> omega

/-- The complete finite arithmetic bound, before analytic parameters are inserted. -/
theorem shortUpsilon_error_energy_sq_le_tail_harmonic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ‖lemma83Kappa β n - shortUpsilonKappa χ β n‖^2*(n:ℝ)⁻¹)^2 ≤
      (∑ n ∈ Finset.Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ n‖^2*(n:ℝ)⁻¹) *
        (harmonic N : ℝ)^80 := by
  have hconv := shortUpsilon_convolution_harmonic_energy_le
    (lemma23UpsilonArithmeticFunction χ - shortUpsilon χ) (shortUpsilonFourfold χ β) N
  rw [← shortUpsilon_kappa_residual_convolution, shortUpsilon_difference_weight_identity] at hconv
  simp only [shortUpsilon_sub_apply] at hconv
  have hb := shortUpsilon_fourfold_harmonic_weight_le χ β hβ N hN
  have ha := shortUpsilon_tail_harmonic_weight_sq_le χ N hN
  have hmain := hconv.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  calc
    _ ≤ ((∑ n ∈ Finset.Ioc (D^4) N,
        ‖lemma23UpsilonArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹) *
        (harmonic N : ℝ)^32)^2 := pow_le_pow_left₀ (by positivity) hmain 2
    _ = (∑ n ∈ Finset.Ioc (D^4) N,
        ‖lemma23UpsilonArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)*(n:ℝ)⁻¹)^2 *
        (harmonic N : ℝ)^64 := by ring
    _ ≤ ((∑ n ∈ Finset.Ioc (D^4) N,
        ‖lemma23NuArithmeticFunction χ n‖^2*(n:ℝ)⁻¹) * (harmonic N : ℝ)^16) *
        (harmonic N : ℝ)^64 := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := by ring

end ZhangLS.Spec
