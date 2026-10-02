import ZhangLS.Spec.Lemma51Modulus

/-! # Absolute vertical transport after cancelling the real conductor -/

namespace ZhangLS.Spec

open Complex Set

set_option maxHeartbeats 1000000

theorem lemma51_vertical_transport {f : ℂ → ℂ} {s w : ℂ} {c B K : ℝ}
    (hw : w.re = 0) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ f (s + (x : ℂ) * w))
    (hne : ∀ x ∈ Icc (0 : ℝ) 1, f (s + (x : ℂ) * w) ≠ 0)
    (hfn : ∀ x ∈ Icc (0 : ℝ) 1, ‖f (s + (x : ℂ) * w)‖ ≤ B)
    (hld : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖logDeriv f (s + (x : ℂ) * w) + (c : ℂ)‖ ≤ K) :
    ‖(f (s + w) - f s * Complex.exp (-(c : ℂ) * w)) / w‖ ≤ B * K := by
  by_cases hw0 : w = 0
  · simp [hw0, mul_nonneg hB hK]
  let G : ℂ → ℂ := fun z => f (s + z * w) * Complex.exp ((c : ℂ) * z * w)
  let d : ℝ → ℂ := fun x =>
    (f (s + (x : ℂ) * w) * (logDeriv f (s + (x : ℂ) * w) + (c : ℂ))) * w *
      Complex.exp ((c : ℂ) * (x : ℂ) * w)
  have hexpn (x : ℝ) : ‖Complex.exp ((c : ℂ) * (x : ℂ) * w)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, hw]
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => G (x : ℂ)) (d x) x := by
    have harg : HasDerivAt (fun z : ℂ => s + z * w) w (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).mul_const w).const_add s
    have hfd := (hf x hx).hasDerivAt.comp (x : ℂ) harg
    have hea : HasDerivAt (fun z : ℂ => (c : ℂ) * z * w) ((c : ℂ) * w) (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul (c : ℂ)).mul_const w
    have hg := hfd.mul hea.cexp
    simp only [Function.comp_def] at hg
    have he : deriv f (s + (x : ℂ) * w) * w * Complex.exp ((c : ℂ) * (x : ℂ) * w) +
        f (s + (x : ℂ) * w) *
          (Complex.exp ((c : ℂ) * (x : ℂ) * w) * ((c : ℂ) * w)) = d x := by
      dsimp [d]
      rw [logDeriv_apply]
      field_simp [hne x hx]
    rw [he] at hg
    exact hg.comp_ofReal
  have hdn (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : ‖d x‖ ≤ B * K * ‖w‖ := by
    dsimp [d]
    rw [norm_mul, norm_mul, norm_mul, hexpn, mul_one]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
    exact mul_le_mul (hfn x hx) (hld x hx) (norm_nonneg _) hB
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt) hdn (convex_Icc (0 : ℝ) 1)
    (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  norm_num only [Complex.ofReal_one, Complex.ofReal_zero, sub_zero, norm_one, mul_one] at hb
  have he : G 1 - G 0 =
      (f (s + w) - f s * Complex.exp (-(c : ℂ) * w)) * Complex.exp ((c : ℂ) * w) := by
    dsimp [G]
    simp only [one_mul, zero_mul, mul_zero, add_zero, Complex.exp_zero, mul_one]
    rw [sub_mul, mul_assoc, ← Complex.exp_add]
    have hh : -(c : ℂ) * w + (c : ℂ) * w = 0 := by ring
    rw [hh, Complex.exp_zero, mul_one]
  rw [he, norm_mul] at hb
  have hn : ‖Complex.exp ((c : ℂ) * w)‖ = 1 := by simpa using hexpn 1
  rw [hn, mul_one] at hb
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hw0)).mpr hb

end ZhangLS.Spec
