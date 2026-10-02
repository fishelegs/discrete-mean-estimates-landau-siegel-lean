import ZhangLS.Spec.Lemma23ProductApproximation

/-!
# The actual long Dirichlet sum in Lemma 4.4

The defining condition (3.5) supplies both endpoint and integral budgets.
Abel summation then bounds the genuine long sum; no partial-sum estimate is
assumed beyond the definition of the good family.
-/

namespace ZhangLS.Spec

open MeasureTheory Complex

set_option maxHeartbeats 1000000

noncomputable def lemma44X3CenteredCoefficient {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  if D ^ 4 < n then lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
    Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ)) else 0

@[simp] theorem lemma44X3CenteredCoefficient_zero {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) :
    lemma44X3CenteredCoefficient χ ψ 0 = 0 := by simp [lemma44X3CenteredCoefficient]

theorem lemma44_X3_eq_centered_partial_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (x : ℝ) :
    lemma23ActualX3 χ ψ x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
      lemma44X3CenteredCoefficient χ ψ n := by
  classical
  have hfilter : (Finset.Icc 0 ⌊x⌋₊).filter (fun n => D ^ 4 < n) =
      Finset.Ioc (D ^ 4) ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [lemma23ActualX3]
  symm
  simp only [lemma44X3CenteredCoefficient, ← Finset.sum_filter, hfilter]

theorem lemma44_X3_zero_of_le {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : x ≤ (D : ℝ) ^ 4) : lemma23ActualX3 χ ψ x = 0 := by
  have hfloor : ⌊x⌋₊ ≤ D ^ 4 := by
    simpa only [← Nat.cast_pow, Nat.floor_natCast] using Nat.floor_le_floor hx
  simp [lemma23ActualX3, Finset.Ioc_eq_empty_of_le hfloor]

/-- `D^4 < P^2`, checked from the actual paper parameters. -/
theorem lemma44_D4_le_P2 {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hL : 3 ≤ lemma23PaperL D) :
    (D : ℝ) ^ 4 ≤ lemma23PaperP D ^ 2 := by
  have hD : (0 : ℝ) < D := by exact_mod_cast χ.modulus_pos
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_pow, Real.log_pow, lemma23PaperP, Real.log_exp]
  have hL2 : lemma23PaperL D ^ 2 ≤ lemma23PaperL D ^ 9 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  change 4 * lemma23PaperL D ≤ 2 * lemma23PaperL D ^ 9
  nlinarith

/-- Extending the budget down to `1` contributes exactly zero below `D^4`. -/
theorem lemma44_X3_integral_eq {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (hL : 3 ≤ lemma23PaperL D) :
    (∫ t in Set.Ioc (1 : ℝ) (lemma23PaperP D ^ 2), ‖lemma23ActualX3 χ ψ t‖ / t) =
      ∫ t in Set.Ioc ((D : ℝ) ^ 4) (lemma23PaperP D ^ 2), ‖lemma23ActualX3 χ ψ t‖ / t := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast χ.modulus_pos
  have hD4 := one_le_pow₀ hD1 (n := 4)
  have hD4P := lemma44_D4_le_P2 χ hL
  have h := integral_union_eq_left_of_forall
    (μ := volume) (s := Set.Ioc ((D : ℝ) ^ 4) (lemma23PaperP D ^ 2))
    (f := fun t : ℝ => ‖lemma23ActualX3 χ ψ t‖ / t)
    (t := Set.Ioc (1 : ℝ) ((D : ℝ) ^ 4)) measurableSet_Ioc
    (fun t ht => by
      change ‖lemma23ActualX3 χ ψ t‖ / t = 0
      rw [lemma44_X3_zero_of_le χ ψ ht.2]
      simp)
  rw [Set.union_comm, Set.Ioc_union_Ioc_eq_Ioc hD4 hD4P] at h
  exact h

/-- Integrability of the actual step-function budget on the full real interval. -/
theorem lemma44_X3_div_integrable {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) :
    IntegrableOn (fun t : ℝ => ‖lemma23ActualX3 χ ψ t‖ / t)
      (Set.Ioc (1 : ℝ) (lemma23PaperP D ^ 2)) := by
  have h := lemma23_partial_sum_div_integrableOn_Ioc
    (N := ⌈lemma23PaperP D ^ 2⌉₊) (lemma44X3CenteredCoefficient χ ψ)
  have hsub : Set.Ioc (1 : ℝ) (lemma23PaperP D ^ 2) ⊆
      Set.Ioc 1 (⌈lemma23PaperP D ^ 2⌉₊ : ℝ) :=
    Set.Ioc_subset_Ioc_right (Nat.le_ceil _)
  simpa only [← lemma44_X3_eq_centered_partial_sum] using h.mono_set hsub

theorem Lemma23GoodPartialSums.x3_bounds {D N : ℕ}
    {χ : RealPrimitiveCharacter D} {ψ : DirichletCharacter ℂ N}
    (h : Lemma23GoodPartialSums χ ψ) (hL : 3 ≤ lemma23PaperL D) :
    ‖lemma23ActualX3 χ ψ (lemma23PaperP D ^ 2)‖ ≤ lemma23PaperL D ^ (-585 : ℤ) ∧
      (∫ t in Set.Ioc (1 : ℝ) (lemma23PaperP D ^ 2), ‖lemma23ActualX3 χ ψ t‖ / t) ≤
        lemma23PaperL D ^ (-585 : ℤ) := by
  have hI : 0 ≤ ∫ t in Set.Ioc ((D : ℝ) ^ 4) (lemma23PaperP D ^ 2),
      ‖lemma23ActualX3 χ ψ t‖ / t := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    have hD4 : 0 ≤ (D : ℝ) ^ 4 := by positivity
    exact div_nonneg (norm_nonneg _) (by linarith [ht.1])
  have hE := norm_nonneg (lemma23ActualX3 χ ψ (lemma23PaperP D ^ 2))
  have hb := h.condition35
  constructor
  · linarith
  · rw [lemma44_X3_integral_eq χ ψ hL]
    linarith

/-- The genuine long sum from `D^4` to `P^2`. -/
noncomputable def lemma44LongDirichletSum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊,
    lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
      Complex.exp (-s * (Real.log (n : ℝ) : ℂ))

/-- Exact centered Abel representation, with the real `P^2` endpoint handled by flooring. -/
theorem lemma44_long_sum_eq_centered_abel_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) :
    lemma44LongDirichletSum χ ψ s =
      ∑ n ∈ Finset.Icc 0 ⌊lemma23PaperP D ^ 2⌋₊,
        lemma23AbelPowerWeight (lemma23PaperCenter D - s) n *
          lemma44X3CenteredCoefficient χ ψ n := by
  classical
  have hfilter : (Finset.Icc 0 ⌊lemma23PaperP D ^ 2⌋₊).filter (fun n => D ^ 4 < n) =
      Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simp only [lemma44X3CenteredCoefficient, mul_ite, mul_zero, ← Finset.sum_filter, hfilter]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [lemma23AbelPowerWeight]
  rw [show Complex.exp ((lemma23PaperCenter D - s) * (Real.log (n : ℝ) : ℂ)) *
      (lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
        Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))) =
      (lemma23NuArithmeticFunction χ n * ψ (n : ZMod N)) *
        (Complex.exp ((lemma23PaperCenter D - s) * (Real.log (n : ℝ) : ℂ)) *
          Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))) by ring,
    ← Complex.exp_add]
  congr 2
  ring

/-- An actual long-sum estimate from condition (3.5), uniform in its complex argument.
The positive real-part loss is displayed explicitly so that it can cancel the
functional-equation factor on the shifted contour. -/
theorem lemma44_long_sum_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ) :
    ‖lemma44LongDirichletSum χ ψ s‖ ≤
      Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)) *
        (1 + ‖lemma23PaperCenter D - s‖) * lemma23PaperL D ^ (-585 : ℤ) := by
  let R := lemma23PaperP D ^ 2
  let K : ℕ := ⌊R⌋₊
  let c := lemma44X3CenteredCoefficient χ ψ
  let z := lemma23PaperCenter D - s
  let A := Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re))
  have hR : 1 ≤ R := by
    have hP : 1 ≤ lemma23PaperP D := by
      apply Real.one_le_exp_iff.mpr
      positivity
    exact one_le_pow₀ hP
  have hK1 : 1 ≤ K := (Nat.le_floor_iff (by linarith : 0 ≤ R)).mpr (by simpa using hR)
  have hKR : (K : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hweight {t : ℝ} (ht : 1 ≤ t) (htR : t ≤ R) :
      ‖lemma23AbelPowerWeight z t‖ ≤ A := by
    have hlog : Real.log t ≤ 2 * lemma23PaperL D ^ 9 := by
      have h := Real.log_le_log (by linarith : 0 < t) htR
      simpa [R, Real.log_pow, lemma23PaperP, Real.log_exp] using h
    apply (lemma23AbelPowerWeight_norm_le_exp ht (by
      change 1 / 2 - s.re ≤ max 0 (1 / 2 - s.re)
      exact le_max_right _ _)).trans
    apply Real.exp_le_exp.mpr
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hlog (le_max_left 0 (1 / 2 - s.re))]
  have hb := hgood.x3_bounds hL
  have hEndpoint : ‖∑ k ∈ Finset.Icc 0 K, c k‖ ≤ lemma23PaperL D ^ (-585 : ℤ) := by
    simpa only [K, c, ← lemma44_X3_eq_centered_partial_sum] using hb.1
  have hIntegral : (∫ t in Set.Ioc (1 : ℝ) K,
      ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t) ≤ lemma23PaperL D ^ (-585 : ℤ) := by
    simp only [c, ← lemma44_X3_eq_centered_partial_sum]
    apply le_trans _ hb.2
    apply setIntegral_mono_set (lemma44_X3_div_integrable χ ψ)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact div_nonneg (norm_nonneg _) (by linarith [ht.1])
    · exact (Set.Ioc_subset_Ioc_right hKR).eventuallyLE
  have hbase := lemma23_abel_power_weight_norm_bound (c := c) (z := z)
    (N := K) (A := A) (B := lemma23PaperL D ^ (-585 : ℤ))
    (K := ‖z‖ * A) (M := lemma23PaperL D ^ (-585 : ℤ))
    (by simp [c]) (hweight (by exact_mod_cast hK1) hKR) hEndpoint
    (by dsimp [A]; positivity)
    (fun t ht => mul_le_mul_of_nonneg_left (hweight ht.1.le (ht.2.trans hKR)) (norm_nonneg _))
    hIntegral
  rw [← lemma44_long_sum_eq_centered_abel_sum χ ψ s] at hbase
  exact hbase.trans_eq (by dsimp [A, z]; ring)

/-- The paper's spacing parameter `α = π / log P`. -/
noncomputable def lemma44PaperAlpha (D : ℕ) : ℝ :=
  Real.pi / Real.log (lemma23PaperP D)

/-- The actual region in the statement of Lemma 4.4. -/
def Lemma44InOmega3 (D : ℕ) (s : ℂ) : Prop :=
  1 / 2 - lemma44PaperAlpha D < s.re ∧ s.re < 1 + lemma44PaperAlpha D ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 3

theorem lemma44_alpha_pos_le_one {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    0 < lemma44PaperAlpha D ∧ lemma44PaperAlpha D ≤ 1 := by
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  have hLpos : 0 < lemma23PaperL D := by linarith
  refine ⟨div_pos Real.pi_pos (pow_pos hLpos _), ?_⟩
  apply (div_le_iff₀ (pow_pos hLpos 9)).mpr
  have hL2 : lemma23PaperL D ^ 2 ≤ lemma23PaperL D ^ 9 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  nlinarith [Real.pi_le_four]

theorem lemma44_omega3_displacement {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma44InOmega3 D s) :
    ‖lemma23PaperCenter D - s‖ ≤ 3 * lemma23PaperL D ^ 405 := by
  have ha := lemma44_alpha_pos_le_one hL
  have hre : |(lemma23PaperCenter D - s).re| ≤ 2 := by
    change |1 / 2 - s.re| ≤ 2
    have hreal := hs.1
    have hreal' := hs.2.1
    apply abs_le.mpr
    constructor <;> linarith [ha.2]
  have him : |(lemma23PaperCenter D - s).im| ≤ lemma23PaperL D ^ 405 + 3 := by
    simpa [abs_sub_comm] using hs.2.2.le
  have hpow : 3 ≤ lemma23PaperL D ^ 405 :=
    hL.trans (le_self_pow₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

/-- The `L^-180` exponent of the long-sum step is obtained without enlarging
the center-displacement estimate to `L^406`. -/
theorem lemma44_long_sum_L180_of_displacement {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hdisp : ‖lemma23PaperCenter D - s‖ ≤ 3 * lemma23PaperL D ^ 405) :
    ‖lemma44LongDirichletSum χ ψ s‖ ≤
      4 * Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)) *
        lemma23PaperL D ^ (-180 : ℤ) := by
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hpow : 1 ≤ lemma23PaperL D ^ 405 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have hprod : lemma23PaperL D ^ 405 * lemma23PaperL D ^ (-585 : ℤ) =
      lemma23PaperL D ^ (-180 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLpos.ne']
    norm_num
  have hcoef : (1 + ‖lemma23PaperCenter D - s‖) * lemma23PaperL D ^ (-585 : ℤ) ≤
      4 * lemma23PaperL D ^ (-180 : ℤ) := by
    calc
      _ ≤ (4 * lemma23PaperL D ^ 405) * lemma23PaperL D ^ (-585 : ℤ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [mul_assoc, hprod]
  have hb := lemma44_long_sum_bound χ ψ s hL hgood
  have he := mul_le_mul_of_nonneg_left hcoef
    (Real.exp_nonneg (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)))
  exact hb.trans (by nlinarith [he])

/-- Uniform actual long-sum control on the whole region of Lemma 4.4.
Gaussian smoothing and the contour integral are separate remaining obligations. -/
theorem lemma44_long_sum_on_omega3 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44LongDirichletSum χ ψ s‖ ≤
      4 * Real.exp (2 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) := by
  have hLpos : 0 < lemma23PaperL D := by linarith
  have ha := lemma44_alpha_pos_le_one hL
  have hmax : max 0 (1 / 2 - s.re) ≤ lemma44PaperAlpha D :=
    max_le ha.1.le (by linarith [hs.1])
  have halpha : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
    field_simp
  have hexp : Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)) ≤
      Real.exp (2 * Real.pi) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hmax (pow_pos hLpos 9).le
    rw [halpha] at h
    linarith
  have hb := lemma44_long_sum_L180_of_displacement χ ψ s hL hψ.2
    (lemma44_omega3_displacement hL hs)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end ZhangLS.Spec
