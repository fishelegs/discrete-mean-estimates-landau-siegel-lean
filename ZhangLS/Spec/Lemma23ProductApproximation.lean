import ZhangLS.Spec.Lemma23GoodSet

/-!
# The genuine product-tail identity for Lemma 4.2

The product coefficients are the truncated convolution `varsigma` of the
actual inverse sequences `ν` and `υ`.  Low coefficients cancel exactly;
the remaining centered partial sums are precisely `X₄` from (3.6).
-/

namespace ZhangLS.Spec

open MeasureTheory

theorem lemma23ActualVarsigma_eq_delta_of_le {D : ℕ}
    (χ : RealPrimitiveCharacter D) {n : ℕ} (hn : n ≤ D ^ 4) :
    lemma23ActualVarsigma χ n = if n = 1 then 1 else 0 := by
  classical
  have hfilter :
      (n.divisorsAntidiagonal.filter (fun q => q.1 ≤ D ^ 4 ∧ q.2 ≤ D ^ 4)) =
        n.divisorsAntidiagonal := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact ⟨(Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hq)).trans hn,
      (Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hq)).trans hn⟩
  rw [lemma23ActualVarsigma, hfilter]
  exact lemma23NuUpsilon_convolutionCoefficient χ n

private theorem lemma23_varsigma_filter_eq_box {D n : ℕ} (hn : n ≠ 0) :
    (n.divisorsAntidiagonal.filter (fun q => q.1 ≤ D ^ 4 ∧ q.2 ≤ D ^ 4)) =
      ((Finset.Icc 1 (D ^ 4) ×ˢ Finset.Icc 1 (D ^ 4)).filter
        (fun q => q.1 * q.2 = n)) := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨hq, hcut⟩
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hq).1
    have hleft := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hq
    have hright := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hq
    exact ⟨⟨⟨by omega, hcut.1⟩, ⟨by omega, hcut.2⟩⟩, hprod⟩
  · rintro ⟨⟨hl, hr⟩, hprod⟩
    exact ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hn⟩, hl.2, hr.2⟩

/-- Exact mixed convolution expansion for the actual Section 4 product. -/
theorem lemma23ActualSectionFourFG_expansion {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) :
    lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s *
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s =
      ∑ n ∈ Finset.Icc 1 (D ^ 8), lemma23ActualVarsigma χ n * ψ (n : ZMod N) *
        Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
  classical
  let T := Finset.Icc 1 (D ^ 4) ×ˢ Finset.Icc 1 (D ^ 4)
  let term : ℕ → ℂ := fun n => ψ (n : ZMod N) *
    Complex.exp (-s * (Real.log (n : ℝ) : ℂ))
  have hpair : ∀ q ∈ T,
      (lemma23NuArithmeticFunction χ q.1 * ψ (q.1 : ZMod N) *
        Complex.exp (-s * (Real.log (q.1 : ℝ) : ℂ))) *
      (lemma23UpsilonArithmeticFunction χ q.2 * ψ (q.2 : ZMod N) *
        Complex.exp (-s * (Real.log (q.2 : ℝ) : ℂ))) =
      (lemma23NuArithmeticFunction χ q.1 * lemma23UpsilonArithmeticFunction χ q.2) *
        term (q.1 * q.2) := by
    intro q hq
    have hq' := Finset.mem_product.mp hq
    have hqa := (Finset.mem_Icc.mp hq'.1).1
    have hqb := (Finset.mem_Icc.mp hq'.2).1
    have ha : (q.1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : q.1 ≠ 0)
    have hb : (q.2 : ℝ) ≠ 0 := by exact_mod_cast (by omega : q.2 ≠ 0)
    have hlog : (Real.log ((q.1 * q.2 : ℕ) : ℝ) : ℂ) =
        (Real.log (q.1 : ℝ) : ℂ) + (Real.log (q.2 : ℝ) : ℂ) := by
      rw [Nat.cast_mul, Real.log_mul ha hb, Complex.ofReal_add]
    have hψprod : ψ ((q.1 * q.2 : ℕ) : ZMod N) =
        ψ (q.1 : ZMod N) * ψ (q.2 : ZMod N) := by rw [Nat.cast_mul, map_mul]
    have hexp : Complex.exp (-s * (Real.log ((q.1 * q.2 : ℕ) : ℝ) : ℂ)) =
        Complex.exp (-s * (Real.log (q.1 : ℝ) : ℂ)) *
          Complex.exp (-s * (Real.log (q.2 : ℝ) : ℂ)) := by
      rw [hlog, mul_add, Complex.exp_add]
    dsimp [term]
    rw [hψprod, hexp]
    ring
  have hmaps : ∀ q ∈ T, q.1 * q.2 ∈ Finset.Icc 1 (D ^ 8) := by
    intro q hq
    have hq' := Finset.mem_product.mp hq
    have ha := Finset.mem_Icc.mp hq'.1
    have hb := Finset.mem_Icc.mp hq'.2
    apply Finset.mem_Icc.mpr
    constructor
    · nlinarith
    · calc
        q.1 * q.2 ≤ D ^ 4 * D ^ 4 := Nat.mul_le_mul ha.2 hb.2
        _ = D ^ 8 := by rw [← pow_add]
  unfold lemma23ActualSectionFourF lemma23ActualSectionFourG
    lemma23SectionFourF lemma23SectionFourG lemma23FiniteDirichletPolynomial
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  calc
    _ = ∑ q ∈ T,
        (lemma23NuArithmeticFunction χ q.1 * lemma23UpsilonArithmeticFunction χ q.2) *
          term (q.1 * q.2) := Finset.sum_congr rfl hpair
    _ = ∑ n ∈ Finset.Icc 1 (D ^ 8),
        ∑ q ∈ T with q.1 * q.2 = n,
          (lemma23NuArithmeticFunction χ q.1 * lemma23UpsilonArithmeticFunction χ q.2) *
            term (q.1 * q.2) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      rw [lemma23ActualVarsigma, lemma23_varsigma_filter_eq_box hn0]
      calc
        _ = (∑ q ∈ T with q.1 * q.2 = n,
            lemma23NuArithmeticFunction χ q.1 * lemma23UpsilonArithmeticFunction χ q.2) *
              term n := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q hq
          rw [(Finset.mem_filter.mp hq).2]
        _ = _ := by dsimp [T, term]; ring

/-- The low coefficients of the actual product cancel, leaving exactly the tail in (3.6). -/
theorem lemma23ActualSectionFourFG_sub_one_eq_tail {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) :
    lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s *
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s - 1 =
      ∑ n ∈ Finset.Ioc (D ^ 4) (D ^ 8), lemma23ActualVarsigma χ n * ψ (n : ZMod N) *
        Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
  classical
  have hD1 : 1 ≤ D := χ.modulus_pos
  have hD4 : 1 ≤ D ^ 4 := one_le_pow₀ hD1
  have hD8 : 1 ≤ D ^ 8 := one_le_pow₀ hD1
  have hterm : ∀ n ∈ Finset.Icc 1 (D ^ 8),
      lemma23ActualVarsigma χ n * ψ (n : ZMod N) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) =
        (if n = 1 then 1 else 0) +
          (if D ^ 4 < n then lemma23ActualVarsigma χ n * ψ (n : ZMod N) *
            Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) else 0) := by
    intro n hn
    by_cases hcut : D ^ 4 < n
    · have hn1 : n ≠ 1 := by omega
      simp [hcut, hn1]
    · rw [if_neg hcut, add_zero, lemma23ActualVarsigma_eq_delta_of_le χ (by omega)]
      by_cases hn1 : n = 1 <;> simp [hn1]
  have htail : (Finset.Icc 1 (D ^ 8)).filter (fun n => D ^ 4 < n) =
      Finset.Ioc (D ^ 4) (D ^ 8) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [lemma23ActualSectionFourFG_expansion, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc, hD8, le_refl, and_self, if_true]
  rw [← Finset.sum_filter, htail]
  ring

/-- The zero-extended centered coefficient sequence for the product tail. -/
noncomputable def lemma23ActualX4CenteredCoefficient {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  if D ^ 4 < n then lemma23ActualVarsigma χ n * ψ (n : ZMod N) *
    Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ)) else 0

@[simp] theorem lemma23ActualX4CenteredCoefficient_zero {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) :
    lemma23ActualX4CenteredCoefficient χ ψ 0 = 0 := by
  simp [lemma23ActualX4CenteredCoefficient]

theorem lemma23ActualX4_eq_centered_partial_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (x : ℝ) :
    lemma23ActualX4 χ ψ x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
      lemma23ActualX4CenteredCoefficient χ ψ n := by
  classical
  have hfilter : (Finset.Icc 0 ⌊x⌋₊).filter (fun n => D ^ 4 < n) =
      Finset.Ioc (D ^ 4) ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [lemma23ActualX4]
  symm
  simp only [lemma23ActualX4CenteredCoefficient, ← Finset.sum_filter, hfilter]

theorem lemma23ActualSectionFourFG_sub_one_eq_centered_abel_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) :
    lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s *
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s - 1 =
      ∑ n ∈ Finset.Icc 0 (D ^ 8),
        lemma23AbelPowerWeight (lemma23PaperCenter D - s) n *
          lemma23ActualX4CenteredCoefficient χ ψ n := by
  classical
  have hterm : ∀ n : ℕ,
      lemma23AbelPowerWeight (lemma23PaperCenter D - s) n *
          lemma23ActualX4CenteredCoefficient χ ψ n =
        if D ^ 4 < n then lemma23ActualVarsigma χ n * ψ (n : ZMod N) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) else 0 := by
    intro n
    by_cases hn : D ^ 4 < n
    · simp only [lemma23ActualX4CenteredCoefficient, if_pos hn, lemma23AbelPowerWeight]
      calc
        _ = (lemma23ActualVarsigma χ n * ψ (n : ZMod N)) *
            (Complex.exp ((lemma23PaperCenter D - s) * (Real.log (n : ℝ) : ℂ)) *
              Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))) := by ring
        _ = _ := by rw [← Complex.exp_add]; congr 2; ring
    · simp [lemma23ActualX4CenteredCoefficient, hn]
  have hfilter : (Finset.Icc 0 (D ^ 8)).filter (fun n => D ^ 4 < n) =
      Finset.Ioc (D ^ 4) (D ^ 8) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [lemma23ActualSectionFourFG_sub_one_eq_tail]
  symm
  simp only [hterm, ← Finset.sum_filter, hfilter]

theorem lemma23ActualX4_zero_of_le {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : x ≤ (D : ℝ) ^ 4) : lemma23ActualX4 χ ψ x = 0 := by
  have hfloor : ⌊x⌋₊ ≤ D ^ 4 := by
    simpa only [← Nat.cast_pow, Nat.floor_natCast] using Nat.floor_le_floor hx
  simp [lemma23ActualX4, Finset.Ioc_eq_empty_of_le hfloor]

/-- Extending the integral down to `1` adds a zero integrand, not a new estimate. -/
theorem lemma23ActualX4_integral_eq {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) :
    (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ) ^ 8), ‖lemma23ActualX4 χ ψ t‖ / t) =
      ∫ t in Set.Ioc ((D : ℝ) ^ 4) ((D : ℝ) ^ 8), ‖lemma23ActualX4 χ ψ t‖ / t := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast χ.modulus_pos
  have hD4 : (1 : ℝ) ≤ (D : ℝ) ^ 4 := one_le_pow₀ hD1
  have hD48 : (D : ℝ) ^ 4 ≤ (D : ℝ) ^ 8 := pow_le_pow_right₀ hD1 (by norm_num)
  have h := integral_union_eq_left_of_forall
    (μ := volume)
    (s := Set.Ioc ((D : ℝ) ^ 4) ((D : ℝ) ^ 8))
    (f := fun t : ℝ => ‖lemma23ActualX4 χ ψ t‖ / t)
    (t := Set.Ioc (1 : ℝ) ((D : ℝ) ^ 4)) measurableSet_Ioc
    (fun t ht => by
      change ‖lemma23ActualX4 χ ψ t‖ / t = 0
      rw [lemma23ActualX4_zero_of_le χ ψ ht.2]
      simp)
  rw [Set.union_comm, Set.Ioc_union_Ioc_eq_Ioc hD4 hD48] at h
  exact h

theorem Lemma23GoodPartialSums.x4_bounds {D N : ℕ}
    {χ : RealPrimitiveCharacter D} {ψ : DirichletCharacter ℂ N}
    (h : Lemma23GoodPartialSums χ ψ) :
    ‖lemma23ActualX4 χ ψ ((D : ℝ) ^ 8)‖ ≤ lemma23PaperL D ^ (-633 : ℤ) ∧
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ) ^ 8), ‖lemma23ActualX4 χ ψ t‖ / t) ≤
        lemma23PaperL D ^ (-633 : ℤ) := by
  have hI : 0 ≤ ∫ t in Set.Ioc ((D : ℝ) ^ 4) ((D : ℝ) ^ 8),
      ‖lemma23ActualX4 χ ψ t‖ / t := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    apply div_nonneg (norm_nonneg _)
    have hD4 : 0 ≤ (D : ℝ) ^ 4 := by positivity
    linarith [ht.1]
  have hE := norm_nonneg (lemma23ActualX4 χ ψ ((D : ℝ) ^ 8))
  have hbudget := h.condition36
  constructor
  · linarith
  · rw [lemma23ActualX4_integral_eq]
    linarith

/-- Lemma 4.2 with explicit absolute constant `4`, derived from the actual
defining condition (3.6) throughout the full region `Ω₁`. -/
theorem lemma23_lemma42_of_good_partial_sums {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hs : Lemma23InOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s *
        lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s - 1‖ ≤
      4 * lemma23PaperL D ^ (-227 : ℤ) := by
  let L := lemma23PaperL D
  let c := lemma23ActualX4CenteredCoefficient χ ψ
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLne : L ≠ 0 := by dsimp [L]; linarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast χ.modulus_pos
  have hD8 : (D : ℝ) ^ 8 ≤ (D : ℝ) ^ 80 := pow_le_pow_right₀ hD1 (by norm_num)
  have hEndpoint :
      ‖lemma23AbelPowerWeight (lemma23PaperCenter D - s) ((D ^ 8 : ℕ) : ℝ)‖ ≤ L := by
    rw [Nat.cast_pow]
    exact lemma23_omega1_power_kernel_le hL hs (one_le_pow₀ hD1) hD8
  have hbounds := hgood.x4_bounds
  have hCoefEndpoint : ‖∑ n ∈ Finset.Icc 0 (D ^ 8), c n‖ ≤ L ^ (-633 : ℤ) := by
    have hx := lemma23ActualX4_eq_centered_partial_sum χ ψ ((D : ℝ) ^ 8)
    rw [← Nat.cast_pow, Nat.floor_natCast] at hx
    change ‖∑ n ∈ Finset.Icc 0 (D ^ 8), lemma23ActualX4CenteredCoefficient χ ψ n‖ ≤
      lemma23PaperL D ^ (-633 : ℤ)
    rw [← hx, Nat.cast_pow]
    exact hbounds.1
  have hIntegral : (∫ t in Set.Ioc (1 : ℝ) ((D ^ 8 : ℕ) : ℝ),
      ‖∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n‖ / t) ≤ L ^ (-633 : ℤ) := by
    dsimp [c, L]
    simpa only [Nat.cast_pow, ← lemma23ActualX4_eq_centered_partial_sum] using hbounds.2
  have hWeight : ∀ t ∈ Set.Ioc (1 : ℝ) ((D ^ 8 : ℕ) : ℝ),
      ‖lemma23PaperCenter D - s‖ *
          ‖lemma23AbelPowerWeight (lemma23PaperCenter D - s) t‖ ≤ 3 * L ^ 406 := by
    intro t ht
    have ht8 : t ≤ (D : ℝ) ^ 8 := by simpa only [Nat.cast_pow] using ht.2
    have htD : t ≤ (D : ℝ) ^ 80 := ht8.trans hD8
    calc
      _ ≤ (3 * L ^ 405) * L :=
        mul_le_mul (lemma23_center_displacement_le_three hL hs)
          (lemma23_omega1_power_kernel_le hL hs ht.1.le htD) (norm_nonneg _) (by positivity)
      _ = 3 * L ^ 406 := by rw [pow_succ]; ring
  have hAbel := lemma23_abel_power_weight_norm_bound (by simp [c]) hEndpoint
    hCoefEndpoint (by positivity : 0 ≤ 3 * L ^ 406) hWeight hIntegral
  have hpower : L ^ 406 * L ^ (-633 : ℤ) = L ^ (-227 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLne]
    norm_num
  have hfirst : L * L ^ (-633 : ℤ) ≤ L ^ (-227 : ℤ) := by
    rw [← hpower]
    apply mul_le_mul_of_nonneg_right
    · simpa using pow_le_pow_right₀ hL1 (show 1 ≤ 406 by norm_num)
    · positivity
  rw [lemma23ActualSectionFourFG_sub_one_eq_centered_abel_sum]
  calc
    _ ≤ L * L ^ (-633 : ℤ) + (3 * L ^ 406) * L ^ (-633 : ℤ) := hAbel
    _ = L * L ^ (-633 : ℤ) + 3 * L ^ (-227 : ℤ) := by rw [mul_assoc, hpower]
    _ ≤ 4 * L ^ (-227 : ℤ) := by linarith

theorem lemma23_lemma42 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    (hs : Lemma23InOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s *
        lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) s - 1‖ ≤
      4 * lemma23PaperL D ^ (-227 : ℤ) :=
  lemma23_lemma42_of_good_partial_sums χ ψ s hL hψ.2 hs

end ZhangLS.Spec
