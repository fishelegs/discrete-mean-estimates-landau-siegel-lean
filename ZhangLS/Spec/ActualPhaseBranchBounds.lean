import ZhangLS.Spec.ActualPhaseArchBounds

/-! The inherited branch and its reciprocal on the full outward rectangle.
The genuine conductor powers cancel before estimates are combined. The
remaining gamma cost is derived from the actual four shifted Z factors.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Real Classical
set_option maxHeartbeats 2500000

noncomputable def actualPhaseShiftPoints (D : ℕ) (c : ℝ) (s : ℂ) : Finset ℂ :=
  {s,s+lemma52PaperBetaOne D c,s+lemma52PaperBetaTwo D c,s+lemma52PaperBetaThree D c}

/-- A geometric hypothesis, containing only source heights, real coordinates
and the explicit gamma error function. No branch norm bound is assumed. -/
def ActualPhaseShiftGeometry (D : ℕ) (c : ℝ) (s : ℂ) (G : ℝ) : Prop :=
  ∀ z ∈ actualPhaseShiftPoints D c s,
    24 ≤ z.im ∧ |z.re|+3 ≤ z.im/4 ∧ actualPhaseGammaError z.im ≤ G

theorem actualPhase_shift_point_real {D : ℕ} {c : ℝ} {s z : ℂ}
    (hz : z ∈ actualPhaseShiftPoints D c s) : z.re = s.re := by
  have hh : z=s ∨ z=s+lemma52PaperBetaOne D c ∨
      z=s+lemma52PaperBetaTwo D c ∨ z=s+lemma52PaperBetaThree D c := by
    simpa only [actualPhaseShiftPoints,Finset.mem_insert,Finset.mem_singleton] using hz
  rcases hh with rfl|rfl|rfl|rfl <;>
    simp [lemma52PaperBetaOne,lemma52PaperBetaTwo,lemma52PaperBetaThree]

/-- Derived bounds for the exact B branch and its reciprocal. The same
conductor occurs at all four purely imaginary shifts and cancels exactly. -/
theorem actualPhase_branch_norm_envelope {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} {G : ℝ}
    (hg : ActualPhaseShiftGeometry D c s G) :
    ‖actualPhaseBranch D c Y s‖ ≤ Real.exp (3*G*|s.re-1/2|) ∧
    ‖(actualPhaseBranch D c Y s)⁻¹‖ ≤ Real.exp (3*G*|s.re-1/2|) := by
  let u := (p : ℝ)^(1/2-s.re)
  let v := Real.exp (G*|s.re-1/2|)
  have hpp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hu : 0 < u := Real.rpow_pos_of_pos hpp _
  have hv : 0 ≤ v := Real.exp_nonneg _
  have hup : (p : ℝ)^(s.re-1/2) = u⁻¹ := by
    dsimp only [u]
    rw [←Real.rpow_neg hpp.le]
    congr 1
    ring
  have hzbound (z : ℂ) (hz : z ∈ actualPhaseShiftPoints D c s) :
      ‖lemma23DirichletZ ψ z‖ ≤ u*v ∧ ‖(lemma23DirichletZ ψ z)⁻¹‖ ≤ u⁻¹*v := by
    have hzre := actualPhase_shift_point_real hz
    have hgz := hg z hz
    have he := actualPhase_Z_horizontal_envelope ψ hψ hp hgz.1 hgz.2.1
    rw [hzre,hup] at he
    have hexp := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hgz.2.2 (abs_nonneg (s.re-1/2)))
    exact ⟨he.1.trans (mul_le_mul_of_nonneg_left hexp hu.le),
      he.2.trans (mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr hu.le))⟩
  have hm0 : s ∈ actualPhaseShiftPoints D c s := by simp [actualPhaseShiftPoints]
  have hm1 : s+lemma52PaperBetaOne D c ∈ actualPhaseShiftPoints D c s := by simp [actualPhaseShiftPoints]
  have hm2 : s+lemma52PaperBetaTwo D c ∈ actualPhaseShiftPoints D c s := by simp [actualPhaseShiftPoints]
  have hm3 : s+lemma52PaperBetaThree D c ∈ actualPhaseShiftPoints D c s := by simp [actualPhaseShiftPoints]
  have hs : 0 < s.im := by linarith only [(hg s hm0).1]
  have h1 : 0 < (s+lemma52PaperBetaOne D c).im := by linarith only [(hg _ hm1).1]
  have h2 : 0 < (s+lemma52PaperBetaTwo D c).im := by linarith only [(hg _ hm2).1]
  have h3 : 0 < (s+lemma52PaperBetaThree D c).im := by linarith only [(hg _ hm3).1]
  have hz0 := hzbound s hm0
  have hz1 := hzbound _ hm1
  have hz2 := hzbound _ hm2
  have hz3 := hzbound _ hm3
  have hb : ‖actualPhaseBranch D c Y s‖^2 ≤ v^6 := by
    calc
      _ = ‖lemma23DirichletZ ψ s‖^3 *
          ‖(lemma23DirichletZ ψ (s+lemma52PaperBetaOne D c))⁻¹‖ *
          ‖(lemma23DirichletZ ψ (s+lemma52PaperBetaTwo D c))⁻¹‖ *
          ‖(lemma23DirichletZ ψ (s+lemma52PaperBetaThree D c))⁻¹‖ := by
        rw [←norm_pow,actualPhase_branch_square c ψ Y hY hs h1 h2 h3]
        simp only [actualPhaseShiftRatio,norm_inv,norm_div,norm_mul,norm_pow,
          inv_div,div_eq_mul_inv,mul_inv_rev,inv_inv]
        ring
      _ ≤ (u*v)^3*(u⁻¹*v)*(u⁻¹*v)*(u⁻¹*v) := by
        gcongr <;> first | exact hz0.1 | exact hz1.2 | exact hz2.2 | exact hz3.2 | positivity
      _ = _ := by field_simp [hu.ne'] <;> ring
  have hbi : ‖(actualPhaseBranch D c Y s)⁻¹‖^2 ≤ v^6 := by
    calc
      _ = ‖(lemma23DirichletZ ψ s)⁻¹‖^3 *
          ‖lemma23DirichletZ ψ (s+lemma52PaperBetaOne D c)‖ *
          ‖lemma23DirichletZ ψ (s+lemma52PaperBetaTwo D c)‖ *
          ‖lemma23DirichletZ ψ (s+lemma52PaperBetaThree D c)‖ := by
        rw [←norm_pow,inv_pow,actualPhase_branch_square c ψ Y hY hs h1 h2 h3,inv_inv]
        simp only [actualPhaseShiftRatio,norm_inv,norm_div,norm_mul,norm_pow,
          div_eq_mul_inv,inv_pow]
        ring
      _ ≤ (u⁻¹*v)^3*(u*v)*(u*v)*(u*v) := by
        gcongr <;> first | exact hz0.2 | exact hz1.1 | exact hz2.1 | exact hz3.1 | positivity
      _ = _ := by field_simp [hu.ne'] <;> ring
  have hv3 : v^3 = Real.exp (3*G*|s.re-1/2|) := by
    dsimp only [v]
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [←hv3]
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (pow_nonneg hv 3)).mp
    convert hb using 1 <;> ring
  · apply (sq_le_sq₀ (norm_nonneg _) (pow_nonneg hv 3)).mp
    convert hbi using 1 <;> ring

/-- All original shifted points lie in the checked geometry, including the
small independent adjustment of the original zero-rectangle endpoints. -/
theorem actualPhase_source_shift_geometry {D : ℕ} {c : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10) {s : ℂ}
    (hr : |s.re-1/2| ≤ lemma23PaperL D^9)
    (ht : |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+lemma44PaperAlpha D/4) :
    ActualPhaseShiftGeometry D c s (60000*lemma23PaperL D) := by
  have ha := lemma51_alpha_le_quarter hL
  have hβ := lemma52_offset_bounds hL hc hsmall
  have hbase : |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 := by
    linarith only [ht,ha]
  have hshift (b : ℝ) (hb : 0 ≤ b) (hbhi : b ≤ 3*lemma44PaperAlpha D) :
      |(s+I*(b : ℂ)).im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 := by
    simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_im,Complex.ofReal_re,zero_mul,one_mul,zero_add]
    have hh := abs_add_le (s.im-(lemma23PaperCenter D).im) b
    rw [abs_of_nonneg hb] at hh
    have he : s.im+b-(lemma23PaperCenter D).im =
        (s.im-(lemma23PaperCenter D).im)+b := by ring
    rw [he]
    linarith only [hh,ht,hbhi,ha]
  intro z hz
  have hre := actualPhase_shift_point_real hz
  have hheight : |z.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 := by
    have hh : z=s ∨ z=s+lemma52PaperBetaOne D c ∨
        z=s+lemma52PaperBetaTwo D c ∨ z=s+lemma52PaperBetaThree D c := by
      simpa only [actualPhaseShiftPoints,Finset.mem_insert,Finset.mem_singleton] using hz
    rcases hh with rfl|rfl|rfl|rfl
    · exact hbase
    · exact hshift _ hβ.1.1 hβ.1.2
    · exact hshift _ hβ.2.1.1 hβ.2.1.2
    · exact hshift _ hβ.2.2.1 hβ.2.2.2
  have hgeom := actualPhase_source_far_rectangle_geometry hL (s := z)
    (by rw [hre]; exact hr) hheight
  refine ⟨hgeom.1,hgeom.2,?_⟩
  apply actualPhase_source_gamma_error_le hL
  exact hheight.trans (by linarith only [pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 405])

/-- A fully discharged bound for the literal inherited branch on the actual
source far rectangle. The exponent has no conductor loss. -/
theorem actualPhase_source_branch_envelope {D p : ℕ} [NeZero p] {c : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ}
    (hr : |s.re-1/2| ≤ lemma23PaperL D^9)
    (ht : |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+lemma44PaperAlpha D/4) :
    ‖actualPhaseBranch D c Y s‖ ≤ Real.exp (180000*lemma23PaperL D*|s.re-1/2|) ∧
    ‖(actualPhaseBranch D c Y s)⁻¹‖ ≤ Real.exp (180000*lemma23PaperL D*|s.re-1/2|) := by
  have hh := actualPhase_branch_norm_envelope c ψ hψ hp Y hY
    (actualPhase_source_shift_geometry hL hc hsmall hr ht)
  have he : (3 : ℝ)*(60000*lemma23PaperL D)*|s.re-1/2| =
      180000*lemma23PaperL D*|s.re-1/2| := by ring
  simpa only [he] using hh

end ZhangLS.Spec
