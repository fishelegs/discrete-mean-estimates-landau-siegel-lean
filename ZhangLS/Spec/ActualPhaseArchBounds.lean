import ZhangLS.Spec.ActualPhaseTransforms

/-! A genuine broad-rectangle gamma envelope.

The conductor power is kept exactly. The remaining factor is exponential
in log(height) times the horizontal displacement. This coarse remainder
suffices for a fixed power-of-P tail gap, including displacement L^9.
No asymptotic or gamma estimate is supplied as an input premise.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Topology Classical
set_option maxHeartbeats 2000000

noncomputable def actualPhaseGammaError (t : ℝ) : ℝ :=
  48*Real.log (3*t) + 16*Real.pi + 8 + ‖Complex.log (Real.pi : ℂ)‖

/-- A coarse original-height bound, independent of the real coordinate.
In outward tail estimates its linear L cost is absorbed by the fixed L^9
support gap before the horizontal Gaussian is applied. -/
theorem actualPhase_source_gamma_error_le {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {t : ℝ} (ht : |t-(lemma23PaperCenter D).im| ≤ 2*lemma23PaperL D^405+3) :
    actualPhaseGammaError t ≤ 60000*lemma23PaperL D := by
  let z : ℂ := (1/2 : ℂ)+I*(t : ℂ)
  have hz : Lemma44InExtendedGammaRegion D z := by
    refine ⟨?_,?_⟩
    · simp [z]
    · simpa [z] using ht
  have hh := lemma44_extended_gamma_region_height hL hz
  have hzIm : z.im = t := by simp [z]
  have htp : 0 < t := by simpa only [hzIm] using hh.2.2.1
  have hlog : Real.log (3*t) ≤ 519*Real.log (lemma23PaperL D)+30 := by
    simpa only [hzIm,abs_of_pos htp] using hh.2.2.2
  have hlogL : Real.log (lemma23PaperL D) ≤ lemma23PaperL D :=
    Real.log_le_self (by linarith)
  have hπ : ‖Complex.log (Real.pi : ℂ)‖ ≤ 4 := by
    rw [←Complex.ofReal_log Real.pi_pos.le,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.one_le_pi_div_two]))]
    exact (Real.log_le_self Real.pi_pos.le).trans Real.pi_le_four
  unfold actualPhaseGammaError
  linarith only [hlog,hlogL,hπ,Real.pi_le_four,hL]

/-- Exact conductor growth with a proved logarithmic-height gamma envelope.
The explicit geometry includes all far sides at sigma=1/2 plus or minus L^9 once
the original source height inequalities are discharged. -/
theorem actualPhase_Z_horizontal_envelope {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hθ : θ.IsPrimitive) (hq : q ≠ 1)
    {s : ℂ} (ht : 24 ≤ s.im) (hr : |s.re|+3 ≤ s.im/4) :
    ‖lemma23DirichletZ θ s‖ ≤
      (q : ℝ)^(1/2-s.re) * Real.exp (actualPhaseGammaError s.im*|s.re-1/2|) ∧
    ‖(lemma23DirichletZ θ s)⁻¹‖ ≤
      (q : ℝ)^(s.re-1/2) * Real.exp (actualPhaseGammaError s.im*|s.re-1/2|) := by
  have htp : 0 < s.im := by linarith
  have hqp : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨H,hHnorm,hHd⟩ := lemma44_exists_horizontal_log_modulus
    (f := lemma23DirichletZ θ)
    (fun z hz => lemma23DirichletZ_differentiableAt_of_im_ne_zero θ hz.ne')
    (fun z hz => lemma23DirichletZ_ne_zero_of_im_pos θ hθ hq hz) htp
  have hzero : H (1/2) = 0 := by
    apply Real.exp_injective
    rw [hHnorm,Real.exp_zero]
    exact lemma23DirichletZ_norm_eq_one_on_critical_line θ hθ hq (by simp)
  let F : ℝ → ℝ := fun x => H x + (x-1/2)*Real.log (q : ℝ)
  have hFd (x : ℝ) : HasDerivAt F
      ((logDeriv (lemma23DirichletZ θ) ((x : ℂ)+I*(s.im : ℂ))).re+Real.log (q : ℝ)) x := by
    simpa only [one_mul] using
      (hHd x).add (((hasDerivAt_id x).sub_const (1/2)).mul_const (Real.log (q : ℝ)))
  have hb (x : ℝ) (hx : x ∈ uIcc (1/2) s.re) :
      ‖(logDeriv (lemma23DirichletZ θ) ((x : ℂ)+I*(s.im : ℂ))).re+Real.log (q : ℝ)‖ ≤
        actualPhaseGammaError s.im := by
    have hlo : -(|s.re|+1/2) ≤ min (1/2) s.re := by
      apply le_min
      · linarith only [abs_nonneg s.re]
      · linarith only [neg_abs_le s.re]
    have hhi : max (1/2) s.re ≤ |s.re|+1/2 := by
      apply max_le
      · linarith only [abs_nonneg s.re]
      · linarith only [le_abs_self s.re]
    have hax : |x| ≤ |s.re|+1/2 := abs_le.mpr ⟨hlo.trans hx.1,hx.2.trans hhi⟩
    have hh := lemma44_DirichletZ_logDeriv_bound θ hθ hq
      (s := (x : ℂ)+I*(s.im : ℂ))
      (by simpa only [add_im,ofReal_im,mul_im,I_re,ofReal_re,I_im,zero_mul,
        mul_one,one_mul,zero_add,add_zero,abs_of_pos htp] using ht)
      (by simp only [add_re,ofReal_re,mul_re,I_re,ofReal_im,I_im,zero_mul,
            mul_zero,sub_zero,add_zero,add_im,mul_im,mul_one,one_mul,zero_add,
            abs_of_pos htp]
          linarith only [hax,hr])
    have hb' := (Complex.abs_re_le_norm
      (logDeriv (lemma23DirichletZ θ) ((x : ℂ)+I*(s.im : ℂ))+
        Complex.log (q : ℂ))).trans hh
    simpa only [actualPhaseGammaError,Real.norm_eq_abs,add_re,←Complex.natCast_log,
      ofReal_re,add_im,ofReal_im,mul_im,I_re,I_im,zero_mul,mul_one,one_mul,
      zero_add,add_zero,abs_of_pos htp] using hb'
  have hbF := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hFd x).hasDerivWithinAt) hb (convex_uIcc (1/2) s.re)
    left_mem_uIcc right_mem_uIcc
  have hFzero : F (1/2) = 0 := by
    change H (1/2)+((1/2 : ℝ)-1/2)*Real.log (q : ℝ) = 0
    rw [hzero,sub_self,zero_mul,add_zero]
  rw [hFzero,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs] at hbF
  have hsEq : (s.re : ℂ)+I*(s.im : ℂ) = s := by apply Complex.ext <;> simp
  have he := hHnorm s.re
  rw [hsEq] at he
  have hu : H s.re ≤ (1/2-s.re)*Real.log (q : ℝ)+
      actualPhaseGammaError s.im*|s.re-1/2| := by
    have hh := (abs_le.mp hbF).2
    dsimp only [F] at hh
    linarith
  have hl : -H s.re ≤ (s.re-1/2)*Real.log (q : ℝ)+
      actualPhaseGammaError s.im*|s.re-1/2| := by
    have hh := (abs_le.mp hbF).1
    dsimp only [F] at hh
    linarith
  constructor
  · rw [←he,Real.rpow_def_of_pos hqp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hu]
  · rw [norm_inv,←he,←Real.exp_neg,Real.rpow_def_of_pos hqp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hl]

/-- Every shifted Y remains unit-modulus on the critical line. Consequently
the exact inherited B multiplier, and not just an approximation to it, has norm one. -/
theorem actualPhase_branch_norm_one {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hre : s.re = 1/2)
    (hs : 0 < s.im)
    (h₁ : 0 < (s+lemma52PaperBetaOne D c).im)
    (h₂ : 0 < (s+lemma52PaperBetaTwo D c).im)
    (h₃ : 0 < (s+lemma52PaperBetaThree D c).im) :
    ‖actualPhaseBranch D c Y s‖ = 1 := by
  have hn (z : ℂ) (hz : 0 < z.im) (hrez : z.re = 1/2) : ‖Y z‖ = 1 :=
    lemma23_Y_norm_eq_one_of_sq_eq_inv (hY.2 z hz)
      (lemma23DirichletZ_norm_eq_one_on_critical_line ψ hψ hp hrez)
  unfold actualPhaseBranch
  rw [norm_div,norm_mul,norm_mul,norm_pow,hn s hs hre,
    hn _ h₁ (by simpa [lemma52PaperBetaOne] using hre),
    hn _ h₂ (by simpa [lemma52PaperBetaTwo] using hre),
    hn _ h₃ (by simpa [lemma52PaperBetaThree] using hre)]
  norm_num


/-- The far real sides required by the accepted tail argument remain inside
the proven high-height gamma geometry, with the original T0 and H. -/
theorem actualPhase_source_far_rectangle_geometry {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hr : |s.re-1/2| ≤ lemma23PaperL D^9)
    (ht : |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1) :
    24 ≤ s.im ∧ |s.re|+3 ≤ s.im/4 := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have h9 : 3 ≤ lemma23PaperL D^9 := hL.trans (le_self_pow₀ hL1 (by norm_num))
  have h405 : lemma23PaperL D^405 ≤ lemma23PaperL D^519 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have h510 : 9 ≤ lemma23PaperL D^510 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 2
    have hp := pow_le_pow_right₀ hL1 (by norm_num : (2 : ℕ) ≤ 510)
    norm_num at hh
    exact hh.trans hp
  have h519 : 9*lemma23PaperL D^9 ≤ lemma23PaperL D^519 := by
    calc
      _ ≤ lemma23PaperL D^510 * lemma23PaperL D^9 :=
        mul_le_mul_of_nonneg_right h510 (pow_nonneg hLp.le _)
      _ = _ := by ring
  -- The already imported bound pi >= 2 suffices; the final geometry is unchanged.
  have hT : 2*lemma23PaperL D^519 ≤ s.im := by
    have hh := (abs_le.mp ht).1
    change -(lemma23PaperL D^405+1) ≤ s.im-2*Real.pi*lemma23PaperL D^519 at hh
    have hpi := mul_le_mul_of_nonneg_right Real.one_le_pi_div_two (pow_nonneg hLp.le 519)
    linarith only [hh,h405,h519,h9,hpi]
  have hreal : |s.re| ≤ lemma23PaperL D^9+1/2 := by
    have hh := abs_add_le (s.re-1/2) (1/2 : ℝ)
    rw [sub_add_cancel,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] at hh
    linarith only [hh,hr]
  constructor
  · nlinarith only [hT,h519,h9]
  · nlinarith only [hT,h519,h9,hreal]

theorem actualPhase_arch_norm_one {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hθ : θ.IsPrimitive) (hq : q ≠ 1)
    {s : ℂ} (hre : s.re = 1/2) : ‖actualPhaseArch θ s‖ = 1 := by
  have hh := lemma23DirichletZ_norm_eq_one_on_critical_line θ hθ hq hre
  rw [actualPhase_Z_eq_root_mul_arch,norm_mul,lemma23_rootNumber_norm_eq_one θ hθ hq,
    one_mul] at hh
  exact hh

end ZhangLS.Spec
