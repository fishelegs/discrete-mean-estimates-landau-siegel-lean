import ZhangLS.Spec.Lemma59Parameters

/-! # Auxiliary inputs for Lemma 5.9

The actual original closed strip, actual coefficients and actual L-function
are retained. The full `Lemma59Target` quotient is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric MeasureTheory Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma59_linear_telescoping_product (N : ℕ) :
    (∏ k ∈ range N, (((k : ℝ) + 2) / ((k : ℝ) + 1))) = (N : ℝ) + 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prod_range_succ, ih]
    push_cast
    have h : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

lemma lemma59_shift_factor_bound {z ρ : ℂ} {δ a : ℝ}
    (hδ : 0 ≤ δ) (ha : 0 < a) (hd : δ / a ≤ ‖z - ρ‖)
    (hne : z ≠ ρ) :
    ‖(z + I * (δ : ℂ) - ρ) / (z - ρ)‖ ≤ 1 + a := by
  have hnorm : 0 < ‖z - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have htri := norm_add_le (z - ρ) (I * (δ : ℂ))
  rw [norm_mul, norm_I, norm_real, Real.norm_of_nonneg hδ, one_mul] at htri
  have he : z - ρ + I * (δ : ℂ) = z + I * (δ : ℂ) - ρ := by ring
  rw [he] at htri
  rw [norm_div]
  apply (div_le_iff₀ hnorm).mpr
  have hd' : δ ≤ a * ‖z - ρ‖ := by
    have hh := (div_le_iff₀ ha).mp hd
    nlinarith only [hh]
  nlinarith only [htri, hd']

lemma lemma59_ranked_zero_product_bound {N : ℕ} {z : ℂ} {ρ : ℕ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ k ∈ range N, ((k : ℝ) + 1) * δ ≤ ‖z - ρ k‖) :
    ‖∏ k ∈ range N, (z + I * (δ : ℂ) - ρ k) / (z - ρ k)‖ ≤ (N : ℝ) + 1 := by
  rw [norm_prod, ← lemma59_linear_telescoping_product N]
  apply prod_le_prod
  · intro k hk
    exact norm_nonneg _
  · intro k hk
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    have hdn : 0 < ‖z - ρ k‖ := (mul_pos hkpos hδ).trans_le (hgap k hk)
    have hne : z ≠ ρ k := sub_ne_zero.mp (norm_pos_iff.mp hdn)
    have h := lemma59_shift_factor_bound hδ.le (inv_pos.mpr hkpos)
      (by simpa only [div_inv_eq_mul, mul_comm] using hgap k hk) hne
    have he : 1 + ((k : ℝ) + 1)⁻¹ = ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
      field_simp
      ring
    exact h.trans_eq he

lemma lemma59_near_zero_factor_bound {z ρ : ℂ} {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hd : η * δ ≤ ‖z - ρ‖) :
    ‖(z + I * (δ : ℂ) - ρ) / (z - ρ)‖ ≤ 1 + η⁻¹ := by
  have hdn : 0 < ‖z - ρ‖ := (mul_pos hη hδ).trans_le hd
  exact lemma59_shift_factor_bound hδ.le (inv_pos.mpr hη)
    (by simpa only [div_inv_eq_mul, mul_comm] using hd)
    (sub_ne_zero.mp (norm_pos_iff.mp hdn))

lemma lemma59_above_zero_norm_decreases {z ρ : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (habove : z.im + δ ≤ ρ.im) :
    ‖z + I * (δ : ℂ) - ρ‖ ≤ ‖z - ρ‖ := by
  have hsq := Complex.sq_norm_sub_sq_re (z + I * (δ : ℂ) - ρ)
  have hsq' := Complex.sq_norm_sub_sq_re (z - ρ)
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
    sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
    zero_add] at hsq hsq'
  have hh := mul_nonneg hδ (sub_nonneg.mpr habove)
  nlinarith only [hsq, hsq', hh, sq_nonneg δ, norm_nonneg (z + I * (δ : ℂ) - ρ), norm_nonneg (z - ρ)]

lemma lemma59_above_zero_factor_le_one {z ρ : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (habove : z.im + δ ≤ ρ.im) :
    ‖(z + I * (δ : ℂ) - ρ) / (z - ρ)‖ ≤ 1 := by
  rw [norm_div]
  by_cases hne : z = ρ
  · simp [hne]
  · have hp : 0 < ‖z - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    exact (div_le_one₀ hp).mpr (lemma59_above_zero_norm_decreases hδ habove)

lemma lemma59_above_zero_product_le_one (S : Finset ℂ) {z : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (habove : ∀ ρ ∈ S, z.im + δ ≤ ρ.im) :
    ‖∏ ρ ∈ S, (z + I * (δ : ℂ) - ρ) / (z - ρ)‖ ≤ 1 := by
  rw [norm_prod]
  calc
    _ ≤ ∏ ρ ∈ S, (1 : ℝ) := by
      apply prod_le_prod
      · intro ρ hρ
        exact norm_nonneg _
      · intro ρ hρ
        exact lemma59_above_zero_factor_le_one hδ (habove ρ hρ)
    _ = 1 := by simp

lemma lemma59_descending_gap_rank {x : ℕ → ℝ} {δ : ℝ} {N : ℕ}
    (hgap : ∀ k < N, x (k + 1) + δ ≤ x k) :
    ∀ k ≤ N, x k + (k : ℝ) * δ ≤ x 0 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkN : k < N := by omega
    have hi := ih (by omega)
    have hs := hgap k hkN
    push_cast
    linarith only [hi, hs]

lemma lemma59_descending_zeros_ranked_distance {z : ℂ} {ρ : ℕ → ℂ} {δ : ℝ} {N : ℕ}
    (hfirst : (ρ 0).im + δ ≤ z.im)
    (hgap : ∀ k < N, (ρ (k + 1)).im + δ ≤ (ρ k).im) :
    ∀ k ∈ range N, ((k : ℝ) + 1) * δ ≤ ‖z - ρ k‖ := by
  intro k hk
  have hi := lemma59_descending_gap_rank (x := fun k => (ρ k).im) hgap k (mem_range.mp hk).le
  have hnorm : z.im - (ρ k).im ≤ ‖z - ρ k‖ :=
    (le_abs_self _).trans (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - ρ k))
  linarith only [hfirst, hi, hnorm]

lemma lemma59_descending_zero_product_bound {z : ℂ} {ρ : ℕ → ℂ} {δ : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hfirst : (ρ 0).im + δ ≤ z.im)
    (hgap : ∀ k < N, (ρ (k + 1)).im + δ ≤ (ρ k).im) :
    ‖∏ k ∈ range N, (z + I * (δ : ℂ) - ρ k) / (z - ρ k)‖ ≤ (N : ℝ) + 1 := by
  exact lemma59_ranked_zero_product_bound hδ
    (lemma59_descending_zeros_ranked_distance hfirst hgap)

lemma lemma59_exceptional_zero_product_bound (S : Finset ℂ) {z : ℂ} {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hcard : S.card ≤ 2)
    (hgap : ∀ ρ ∈ S, η * δ ≤ ‖z - ρ‖) :
    ‖∏ ρ ∈ S, (z + I * (δ : ℂ) - ρ) / (z - ρ)‖ ≤ (1 + η⁻¹) ^ 2 := by
  have hbase : 1 ≤ 1 + η⁻¹ := by linarith only [le_of_lt (inv_pos.mpr hη)]
  rw [norm_prod]
  calc
    _ ≤ ∏ ρ ∈ S, (1 + η⁻¹) := by
      apply prod_le_prod
      · intro ρ hρ
        exact norm_nonneg _
      · intro ρ hρ
        exact lemma59_near_zero_factor_bound hδ hη (hgap ρ hρ)
    _ = (1 + η⁻¹) ^ S.card := by simp
    _ ≤ (1 + η⁻¹) ^ 2 := pow_le_pow_right₀ hbase hcard

end ZhangLS.Spec
