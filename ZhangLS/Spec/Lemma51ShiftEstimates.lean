import ZhangLS.Spec.Lemma51VerticalTransport

/-! # Actual conductor-normalized shifts throughout the paper's region -/

namespace ZhangLS.Spec

open Complex Set

set_option maxHeartbeats 1000000

theorem lemma51_shift_segment_region {D : ℕ} {s w : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InRegion D s)
    (hwre : w.re = 0) (hwim : |w.im| < lemma23PaperL D ^ 20)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Lemma51InExtendedRegion D (s + (x : ℂ) * w) := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpow : lemma23PaperL D ^ 20 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hre : (s + (x : ℂ) * w).re = s.re := by simp [mul_re, hwre]
  refine ⟨by rw [hre]; exact hs.1, ?_⟩
  have he : (s + (x : ℂ) * w).im - (lemma23PaperCenter D).im =
      (s.im - (lemma23PaperCenter D).im) + x * w.im := by simp [mul_im]; ring
  rw [he]
  have hxn : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
  have hm : |x * w.im| ≤ |w.im| := by
    rw [abs_mul]
    nlinarith [abs_nonneg w.im]
  exact (abs_add_le _ _).trans (by linarith [hs.2])

theorem lemma51_actual_shift_at_real_conductor {D N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N ≠ 1)
    (hlogN : Real.log (N : ℝ) ≤ 2 * lemma23PaperL D ^ 9)
    {q E : ℝ} (hq : 0 < q) (hE : 0 ≤ E)
    (hqerror : |Real.log (N : ℝ) - Real.log q| ≤ E)
    {s w : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InRegion D s)
    (hwre : w.re = 0) (hwim : |w.im| < lemma23PaperL D ^ 20) :
    ‖(lemma23DirichletZ θ (s + w) - lemma23DirichletZ θ s *
        ((q * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w‖ ≤
      Real.exp (600 * Real.pi) * (21 * lemma23PaperL D ^ (-114 : ℤ) + E) := by
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hc : 0 < q * lemma51PaperT0 D := mul_pos hq hT
  have hregion (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :=
    lemma51_shift_segment_region hL hs hwre hwim hx
  have hheight (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < (s + (x : ℂ) * w).im :=
    hT.trans_le (lemma51_extended_region_data hL (hregion x hx)).2.2.1
  have herror (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ‖logDeriv (lemma23DirichletZ θ) (s + (x : ℂ) * w) +
        (Real.log (q * lemma51PaperT0 D) : ℂ)‖ ≤
        21 * lemma23PaperL D ^ (-114 : ℤ) + E := by
    have hh := lemma51_DirichletZ_logDeriv_at_T0 θ hθ hN hL (hregion x hx)
    have hqnorm : ‖((Real.log q - Real.log (N : ℝ) : ℝ) : ℂ)‖ ≤ E := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] using hqerror
    have he : logDeriv (lemma23DirichletZ θ) (s + (x : ℂ) * w) +
        (Real.log (q * lemma51PaperT0 D) : ℂ) =
        (logDeriv (lemma23DirichletZ θ) (s + (x : ℂ) * w) + Complex.log (N : ℂ) +
          (Real.log (lemma51PaperT0 D) : ℂ)) +
        ((Real.log q - Real.log (N : ℝ) : ℝ) : ℂ) := by
      rw [Real.log_mul hq.ne' hT.ne', ← Complex.natCast_log]
      push_cast
      ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hh hqnorm)
  have ht := lemma51_vertical_transport hwre (Real.exp_nonneg _)
    (show 0 ≤ 21 * lemma23PaperL D ^ (-114 : ℤ) + E by positivity)
    (fun x hx => lemma23DirichletZ_differentiableAt_of_im_ne_zero θ (hheight x hx).ne')
    (fun x hx => lemma23DirichletZ_ne_zero_of_im_pos θ hθ hN (hheight x hx))
    (fun x hx => lemma51_DirichletZ_norm_bound θ hθ hN hlogN hL (hregion x hx)) herror
  have he : ((q * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w) =
      Complex.exp (-(Real.log (q * lemma51PaperT0 D) : ℂ) * w) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne'),
      ← Complex.ofReal_log hc.le]
    congr 1
    ring
  rw [he]
  exact ht

end ZhangLS.Spec
