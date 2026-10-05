import ZhangLS.Spec.Lemma33GaussTransform

/-! # Exact primitive parity means of actual additive samples

The finite additive polynomial is the existing `lemma33AdditivePolynomial`. Its zero mean
comes from additive orthogonality on unit frequencies. The parity Parseval identity is proved
for the actual Dirichlet character family, and the principal character correction is then
removed using the exact Gauss transform. No projection-module assumptions are used.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

/-- The complete additive sample mean is supported only on frequencies divisible by the
modulus. This identity does not require primality. -/
theorem actualSample_additivePolynomial_sum {p : ℕ} [NeZero p]
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ j : ZMod p, lemma33AdditivePolynomial S a j) =
      (p : ℂ) * ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod p) = 0), a n := by
  classical
  simp only [lemma33AdditivePolynomial]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p)]
  simp only [ZMod.card, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_mul, mul_comm]

/-- An additive polynomial supported on units has zero complete sample mean. -/
theorem actualSample_additivePolynomial_sum_eq_zero_of_units {p : ℕ} [NeZero p]
    (hp : 1 < p) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, IsUnit (n : ZMod p)) :
    (∑ j : ZMod p, lemma33AdditivePolynomial S a j) = 0 := by
  classical
  letI : Fact (1 < p) := ⟨hp⟩
  rw [actualSample_additivePolynomial_sum]
  have hempty : S.filter (fun n : ℕ => (n : ZMod p) = 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn, hz⟩
    exact (hS n hn).ne_zero hz
  simp [hempty]

/-- The full complete sample mean vanishes whenever every nonunit frequency has zero
coefficient. In particular this applies after deleting the multiples of a prime. -/
theorem actualSample_additivePolynomial_sum_eq_zero_of_nonunit_vanish
    {p : ℕ} [NeZero p] (hp : 1 < p) (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ¬ IsUnit (n : ZMod p) → a n = 0) :
    (∑ j : ZMod p, lemma33AdditivePolynomial S a j) = 0 := by
  classical
  letI : Fact (1 < p) := ⟨hp⟩
  rw [actualSample_additivePolynomial_sum]
  suffices (∑ n ∈ S.filter (fun n : ℕ => (n : ZMod p) = 0), a n) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hn, hz⟩
  exact ha n hn (fun hu => hu.ne_zero hz)

/-- Filtering to unit frequencies gives an actual additive sample vector of mean zero. -/
theorem actualSample_additivePolynomial_unitFilter_sum_eq_zero
    {p : ℕ} [NeZero p] (hp : 1 < p) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ j : ZMod p,
      lemma33AdditivePolynomial (S.filter (fun n : ℕ => IsUnit (n : ZMod p))) a j) = 0 := by
  exact actualSample_additivePolynomial_sum_eq_zero_of_units hp _ a
    (fun n hn => (Finset.mem_filter.mp hn).2)

lemma actualSample_prime_primitive_iff_ne_one {p : ℕ} [NeZero p]
    (hp : p.Prime) (χ : DirichletCharacter ℂ p) : χ.IsPrimitive ↔ χ ≠ 1 := by
  constructor
  · exact lemma33_primitive_nonprincipal hp χ
  · intro hχ
    rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with h | h
    · exact False.elim (hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mpr h))
    · exact h

lemma actualSample_character_inv_neg_one {p : ℕ} (χ : DirichletCharacter ℂ p) :
    χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  rcases χ.even_or_odd with h | h
  · change χ (-1) = 1 at h
    simp [h]
  · change χ (-1) = -1 at h
    simp [h]

lemma actualSample_reflected_character_sum {p : ℕ} [NeZero p]
    (F : ZMod p → ℂ) (χ : DirichletCharacter ℂ p) :
    (∑ u : ZMod p, F (-u) * χ⁻¹ u) =
      χ (-1) * ∑ u : ZMod p, F u * χ⁻¹ u := by
  have hneg (u : ZMod p) : χ⁻¹ (-u) = χ (-1) * χ⁻¹ u := by
    rw [← neg_one_mul u, map_mul, actualSample_character_inv_neg_one]
  calc
    _ = ∑ u : ZMod p, F u * χ⁻¹ (-u) := by
      exact Fintype.sum_bijective (fun u : ZMod p => -u)
        neg_involutive.bijective _ _ (fun u => by simp)
    _ = _ := by
      simp_rw [hneg]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

lemma actualSample_parity_projected_transform {p : ℕ} [NeZero p]
    (F : ZMod p → ℂ) (χ : DirichletCharacter ℂ p)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ u : ZMod p, ((F u + (s : ℂ) * F (-u)) / 2) * χ⁻¹ u) =
      if χ (-1) = (s : ℂ) then ∑ u : ZMod p, F u * χ⁻¹ u else 0 := by
  have hr := actualSample_reflected_character_sum F χ
  have hexpand :
      (∑ u : ZMod p, ((F u + (s : ℂ) * F (-u)) / 2) * χ⁻¹ u) =
      ((∑ u : ZMod p, F u * χ⁻¹ u) +
        (s : ℂ) * (∑ u : ZMod p, F (-u) * χ⁻¹ u)) / 2 := by
    simp_rw [div_mul_eq_mul_div, add_mul]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum, mul_assoc]
  rw [hexpand, hr]
  rcases χ.even_or_odd with hχ | hχ <;>
    rcases hs with rfl | rfl
  all_goals change χ (-1) = _ at hχ
  all_goals norm_num [hχ]

lemma actualSample_parity_transform_parseval {p : ℕ} [NeZero p]
    (hp : p.Prime) (F : ZMod p → ℂ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ (-1) = (s : ℂ)),
      ‖∑ u : ZMod p, F u * χ⁻¹ u‖ ^ 2) =
    (p.totient : ℝ) * ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
      ‖(F u + (s : ℂ) * F (-u)) / 2‖ ^ 2 := by
  classical
  have h := lemma33_unit_character_transform_parseval hp
    (fun u => (F u + (s : ℂ) * F (-u)) / 2)
  simp_rw [actualSample_parity_projected_transform F _ s hs] at h
  simpa only [apply_ite, ite_pow, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_filter] using h

lemma actualSample_parity_norm_square (x y : ℂ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ‖(x + (s : ℂ) * y) / 2‖ ^ 2 =
      (‖x‖ ^ 2 + ‖y‖ ^ 2 + 2 * s * (x * star y).re) / 4 := by
  rcases hs with rfl | rfl
  all_goals simp only [Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im,
    Complex.div_re, Complex.div_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  all_goals norm_num
  all_goals ring


lemma actualSample_parity_norm_square_sum {p : ℕ} [NeZero p]
    (F : ZMod p → ℂ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ u : ZMod p, ‖(F u + (s : ℂ) * F (-u)) / 2‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ u : ZMod p,
        (‖F u‖ ^ 2 + s * (F u * star (F (-u))).re) := by
  have hneg : (∑ u : ZMod p, ‖F (-u)‖ ^ 2) = ∑ u : ZMod p, ‖F u‖ ^ 2 := by
    exact Fintype.sum_bijective (fun u : ZMod p => -u)
      neg_involutive.bijective _ _ (fun u => rfl)
  simp_rw [actualSample_parity_norm_square _ _ s hs]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hneg]
  ring

lemma actualSample_parity_norm_square_zero (x : ℂ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ‖(x + (s : ℂ) * x) / 2‖ ^ 2 = if s = 1 then ‖x‖ ^ 2 else 0 := by
  rcases hs with rfl | rfl
  · simp
  · norm_num

lemma actualSample_parity_unit_norm_square_sum {p : ℕ} [NeZero p]
    (F : ZMod p → ℂ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
      ‖(F u + (s : ℂ) * F (-u)) / 2‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ u : ZMod p,
        (‖F u‖ ^ 2 + s * (F u * star (F (-u))).re) -
        if s = 1 then ‖F 0‖ ^ 2 else 0 := by
  classical
  have h := Finset.sum_erase_add Finset.univ
    (fun u : ZMod p => ‖(F u + (s : ℂ) * F (-u)) / 2‖ ^ 2)
    (Finset.mem_univ (0 : ZMod p))
  rw [actualSample_parity_norm_square_sum F s hs] at h
  simp only [neg_zero, actualSample_parity_norm_square_zero _ s hs] at h
  linarith

lemma actualSample_principal_transform_of_zero_mean {p : ℕ} [NeZero p]
    (hp : p.Prime) (F : ZMod p → ℂ) (hF : ∑ u : ZMod p, F u = 0) :
    (∑ u : ZMod p, F u * (1 : DirichletCharacter ℂ p)⁻¹ u) = -F 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hunit : (∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod p)), F u) = -F 0 := by
    have h := Finset.sum_erase_add Finset.univ F (Finset.mem_univ (0 : ZMod p))
    rw [hF] at h
    exact eq_neg_of_add_eq_zero_left h
  calc
    _ = ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
          F u * (1 : DirichletCharacter ℂ p) u := by
      have h := Finset.sum_erase_add Finset.univ
        (fun u => F u * (1 : DirichletCharacter ℂ p) u) (Finset.mem_univ (0 : ZMod p))
      simpa only [inv_one, MulChar.map_zero, mul_zero, add_zero] using h.symm
    _ = ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod p)), F u := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [MulChar.one_apply, isUnit_iff_ne_zero, (Finset.mem_erase.mp hu).1]
    _ = -F 0 := hunit


lemma actualSample_primitive_parity_transform_exact {p : ℕ} [NeZero p]
    (hp : p.Prime) (F : ZMod p → ℂ) (hF : ∑ u : ZMod p, F u = 0)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p =>
        χ.IsPrimitive ∧ χ (-1) = (s : ℂ)),
      ‖∑ u : ZMod p, F u * χ⁻¹ u‖ ^ 2) =
      ((p : ℝ) - 1) / 2 * ∑ u : ZMod p,
        (‖F u‖ ^ 2 + s * (F u * star (F (-u))).re) -
        (p : ℝ) * (if s = 1 then ‖F 0‖ ^ 2 else 0) := by
  classical
  let T : DirichletCharacter ℂ p → ℝ := fun χ => ‖∑ u : ZMod p, F u * χ⁻¹ u‖ ^ 2
  let f : DirichletCharacter ℂ p → ℝ := fun χ => if χ (-1) = (s : ℂ) then T χ else 0
  have hsum :
      (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p =>
        χ.IsPrimitive ∧ χ (-1) = (s : ℂ)), T χ) =
      ∑ χ ∈ (Finset.univ.erase 1 : Finset (DirichletCharacter ℂ p)), f χ := by
    rw [← Finset.filter_ne', Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ hχ
    simp only [actualSample_prime_primitive_iff_ne_one hp, f]
    by_cases h1 : χ = 1 <;> by_cases hs' : χ (-1) = (s : ℂ) <;> simp [h1, hs']
  have hf1 : f 1 = if s = 1 then ‖F 0‖ ^ 2 else 0 := by
    have h1 : (1 : DirichletCharacter ℂ p) (-1) = 1 := by simp [MulChar.one_apply]
    simp only [f, T, h1, actualSample_principal_transform_of_zero_mean hp F hF, norm_neg]
    congr 1
    apply propext
    rw [← Complex.ofReal_one, Complex.ofReal_inj]
    exact eq_comm
  have hsplit := Finset.sum_erase_add Finset.univ f
    (Finset.mem_univ (1 : DirichletCharacter ℂ p))
  rw [← hsum, hf1] at hsplit
  have hfull : (∑ χ : DirichletCharacter ℂ p, f χ) =
      (p.totient : ℝ) * ((1 / 2 : ℝ) * ∑ u : ZMod p,
        (‖F u‖ ^ 2 + s * (F u * star (F (-u))).re) -
        if s = 1 then ‖F 0‖ ^ 2 else 0) := by
    rw [← Finset.sum_filter]
    exact (actualSample_parity_transform_parseval hp F s hs).trans
      (congrArg ((p.totient : ℝ) * ·) (actualSample_parity_unit_norm_square_sum F s hs))
  rw [hfull] at hsplit
  have htot : (p.totient : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]
    norm_num
  rw [htot] at hsplit
  change (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p =>
    χ.IsPrimitive ∧ χ (-1) = (s : ℂ)), T χ) = _
  nlinarith [hsplit]

lemma actualSample_additivePolynomial_primitive_parity_mean_exact_of_zero_mean
    {p : ℕ} [NeZero p] (hp : p.Prime) (S : Finset ℕ) (a : ℕ → ℂ)
    (hF : ∑ u : ZMod p, lemma33AdditivePolynomial S a u = 0)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p =>
        χ.IsPrimitive ∧ χ (-1) = (s : ℂ)),
      ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2) =
      ((p : ℝ) - 1) / (2 * (p : ℝ)) * ∑ u : ZMod p,
        (‖lemma33AdditivePolynomial S a u‖ ^ 2 +
          s * (lemma33AdditivePolynomial S a u *
            star (lemma33AdditivePolynomial S a (-u))).re) -
        (if s = 1 then ‖lemma33AdditivePolynomial (p := p) S a 0‖ ^ 2 else 0) := by
  classical
  have h := actualSample_primitive_parity_transform_exact hp
    (lemma33AdditivePolynomial S a) hF s hs
  have hgauss :
      (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p =>
          χ.IsPrimitive ∧ χ (-1) = (s : ℂ)),
        ‖∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u‖ ^ 2) =
      (p : ℝ) * (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p =>
          χ.IsPrimitive ∧ χ (-1) = (s : ℂ)),
        ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    exact lemma33_gauss_finite_transform_norm_square hp χ
      (Finset.mem_filter.mp hχ).2.1 S a
  rw [hgauss] at h
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply (mul_left_cancel₀ hpR)
  calc
    _ = _ := h
    _ = _ := by field_simp

lemma actualSample_additivePolynomial_primitive_parity_mean_exact_of_units
    {p : ℕ} [NeZero p] (hp : p.Prime) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, IsUnit (n : ZMod p))
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p =>
        χ.IsPrimitive ∧ χ (-1) = (s : ℂ)),
      ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2) =
      ((p : ℝ) - 1) / (2 * (p : ℝ)) * ∑ u : ZMod p,
        (‖lemma33AdditivePolynomial S a u‖ ^ 2 +
          s * (lemma33AdditivePolynomial S a u *
            star (lemma33AdditivePolynomial S a (-u))).re) -
        (if s = 1 then ‖lemma33AdditivePolynomial (p := p) S a 0‖ ^ 2 else 0) := by
  exact actualSample_additivePolynomial_primitive_parity_mean_exact_of_zero_mean hp S a
    (actualSample_additivePolynomial_sum_eq_zero_of_units hp.one_lt S a hS) s hs

lemma actualSample_additivePolynomial_primitive_parity_mean_exact_of_nonunit_vanish
    {p : ℕ} [NeZero p] (hp : p.Prime) (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ¬ IsUnit (n : ZMod p) → a n = 0)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p =>
        χ.IsPrimitive ∧ χ (-1) = (s : ℂ)),
      ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2) =
      ((p : ℝ) - 1) / (2 * (p : ℝ)) * ∑ u : ZMod p,
        (‖lemma33AdditivePolynomial S a u‖ ^ 2 +
          s * (lemma33AdditivePolynomial S a u *
            star (lemma33AdditivePolynomial S a (-u))).re) -
        (if s = 1 then ‖lemma33AdditivePolynomial (p := p) S a 0‖ ^ 2 else 0) := by
  exact actualSample_additivePolynomial_primitive_parity_mean_exact_of_zero_mean hp S a
    (actualSample_additivePolynomial_sum_eq_zero_of_nonunit_vanish hp.one_lt S a ha) s hs


/-- Deleting the nonunit frequencies modulo a prime removes exactly the constant
contribution from the frequencies divisible by that prime. No mean-zero hypothesis is used. -/
theorem actualSample_additivePolynomial_eq_unitFilter_add_constant
    {p : ℕ} [NeZero p] (hp : p.Prime) (S : Finset ℕ) (a : ℕ → ℂ) (j : ZMod p) :
    lemma33AdditivePolynomial S a j =
      lemma33AdditivePolynomial (S.filter (fun n : ℕ => IsUnit (n : ZMod p))) a j +
        ∑ n ∈ S.filter (fun n : ℕ => p ∣ n), a n := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hfilter : S.filter (fun n : ℕ => IsUnit (n : ZMod p)) =
      S.filter (fun n : ℕ => ¬ p ∣ n) := by
    apply Finset.filter_congr
    intro n hn
    rw [isUnit_iff_ne_zero, ne_eq, ZMod.natCast_eq_zero_iff]
  have hconstant :
      (∑ n ∈ S.filter (fun n : ℕ => p ∣ n),
        a n * ZMod.stdAddChar (j * (n : ZMod p))) =
      ∑ n ∈ S.filter (fun n : ℕ => p ∣ n), a n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [(ZMod.natCast_eq_zero_iff n p).mpr (Finset.mem_filter.mp hn).2]
    simp
  unfold lemma33AdditivePolynomial
  rw [hfilter]
  calc
    _ = (∑ n ∈ S.filter (fun n : ℕ => p ∣ n),
        a n * ZMod.stdAddChar (j * (n : ZMod p))) +
      ∑ n ∈ S.filter (fun n : ℕ => ¬ p ∣ n),
        a n * ZMod.stdAddChar (j * (n : ZMod p)) :=
      (Finset.sum_filter_add_sum_filter_not S (fun n : ℕ => p ∣ n) _).symm
    _ = _ := by rw [hconstant]; exact add_comm _ _

/-- The full-minus-unit sample vector is the same constant at every sample point. -/
theorem actualSample_additivePolynomial_sub_unitFilter
    {p : ℕ} [NeZero p] (hp : p.Prime) (S : Finset ℕ) (a : ℕ → ℂ) (j : ZMod p) :
    lemma33AdditivePolynomial S a j -
      lemma33AdditivePolynomial (S.filter (fun n : ℕ => IsUnit (n : ZMod p))) a j =
        ∑ n ∈ S.filter (fun n : ℕ => p ∣ n), a n := by
  rw [actualSample_additivePolynomial_eq_unitFilter_add_constant hp S a j]
  ring


/-- A Dirichlet polynomial is unchanged by deleting its nonunit frequencies.
This holds for every character and every modulus, without primality. -/
theorem actualSample_characterPolynomial_eq_unitFilter
    {p : ℕ} (χ : DirichletCharacter ℂ p) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ S, a n * χ (n : ZMod p)) =
      ∑ n ∈ S.filter (fun n : ℕ => IsUnit (n : ZMod p)), a n * χ (n : ZMod p) := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have hnu : ¬ IsUnit (n : ZMod p) := by
    intro hu
    exact hnot (Finset.mem_filter.mpr ⟨hn, hu⟩)
  rw [χ.map_nonunit hnu, mul_zero]

end ZhangLS.Spec
