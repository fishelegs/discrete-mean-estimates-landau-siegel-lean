import ZhangLS.Spec.Lemma81BoundaryCut

/-! # Uniform actual boundary choice for the Lemma 8.1 rectangle

The new horizontal cuts preserve the exact strict (2.14) zero set, including
zeros at its original endpoints. Every point on the four resulting edges is
separated from every actual L-zero by at least α/4. Both facts are conclusions
of the actual extended Proposition 2.2 zero theorem.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set
set_option maxHeartbeats 2000000

noncomputable def lemma81BoundaryZeroOrdinates {p : ℕ} [NeZero p]
    (D : ℕ) (ψ : DirichletCharacter ℂ p) : Set ℝ :=
  {t | ψ.LFunction (⟨1/2,t⟩ : ℂ) = 0 ∧
    |t-(lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 1}

def Lemma81OpenRectangle (D : ℕ) (lo hi : ℝ) (s : ℂ) : Prop :=
  |s.re-1/2| < lemma44PaperAlpha D ∧ lo < s.im ∧ s.im < hi

def Lemma81ClosedRectangle (D : ℕ) (lo hi : ℝ) (s : ℂ) : Prop :=
  |s.re-1/2| ≤ lemma44PaperAlpha D ∧ lo ≤ s.im ∧ s.im ≤ hi

def Lemma81RectangleBoundary (D : ℕ) (lo hi : ℝ) (s : ℂ) : Prop :=
  Lemma81ClosedRectangle D lo hi s ∧
    (|s.re-1/2| = lemma44PaperAlpha D ∨ s.im = lo ∨ s.im = hi)

lemma lemma81_closed_rectangle_height {D : ℕ} {lo hi : ℝ}
    (hlo : |lo-((lemma23PaperCenter D).im-lemma23PaperL D ^ 405)| ≤ lemma44PaperAlpha D/4)
    (hhi : |hi-((lemma23PaperCenter D).im+lemma23PaperL D ^ 405)| ≤ lemma44PaperAlpha D/4)
    {s : ℂ} (hs : Lemma81ClosedRectangle D lo hi s) :
    |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + lemma44PaperAlpha D/4 := by
  apply abs_le.mpr
  have hl := (abs_le.mp hlo).1
  have hu := (abs_le.mp hhi).2
  exact ⟨by linarith only [hl,hs.2.1],by linarith only [hu,hs.2.2]⟩

/-- The uniform rectangle required by page 42, with exact original zero
membership and all-zero separation on every edge. -/
theorem lemma81_uniform_actual_rectangle_boundaries :
    ∃ N : ℕ, ∀ {D p : ℕ} [NeZero p]
      (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∃ lo hi : ℝ,
      |lo-((lemma23PaperCenter D).im-lemma23PaperL D ^ 405)| ≤ lemma44PaperAlpha D/4 ∧
      |hi-((lemma23PaperCenter D).im+lemma23PaperL D ^ 405)| ≤ lemma44PaperAlpha D/4 ∧
      lo < hi ∧
      (∀ ρ : ℂ, ψ.LFunction ρ = 0 →
        (Lemma81OpenRectangle D lo hi ρ ↔ Lemma23InZeroWindow D ρ)) ∧
      (∀ s : ℂ, Lemma81RectangleBoundary D lo hi s → Lemma59ZeroSeparated (D := D) ψ s (1/4)) := by
  obtain ⟨c,hc,Nzero,hzero⟩ := lemma59_uniform_extended_actual_product_zeros
  refine ⟨max Nzero lemma23SectionFourModulusThreshold,?_⟩
  intro D p _ χ ψ hD hψ
  have hDz := (le_max_left Nzero lemma23SectionFourModulusThreshold).trans hD
  have hsection := (le_max_right Nzero lemma23SectionFourModulusThreshold).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold hsection).1
  have hLp : 0 < lemma23PaperL D := by linarith
  have ha := (lemma44_alpha_pos_le_one hL).1
  have haq := lemma51_alpha_le_quarter hL
  have hH1 : 1 ≤ lemma23PaperL D ^ 405 := one_le_pow₀ (by linarith only [hL])
  have hall := hzero χ ψ hDz hψ
  let S := lemma81BoundaryZeroOrdinates D ψ
  have hprod {ρ : ℂ} (hz : ψ.LFunction ρ = 0) : lemma48ActualProduct χ ψ ρ = 0 := by
    simp only [lemma48ActualProduct,hz,zero_mul]
  have hcrit {ρ : ℂ} (hr : |ρ.re-1/2| < 1/2)
      (ht : |ρ.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 1)
      (hz : ψ.LFunction ρ = 0) : ρ.re = 1/2 :=
    (hall.2.2 ⟨hr,by linarith only [ht]⟩ (hprod hz)).1
  have hSmem {ρ : ℂ} (hr : ρ.re = 1/2)
      (ht : |ρ.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 1)
      (hz : ψ.LFunction ρ = 0) : ρ.im ∈ S := by
    have he : (⟨1/2,ρ.im⟩ : ℂ) = ρ := by apply Complex.ext <;> simp [hr]
    exact ⟨by rw [he]; exact hz,ht⟩
  have hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → lemma44PaperAlpha D/2 ≤ |x-y| := by
    intro x hx y hy hxy
    have hx' : ψ.LFunction (⟨1/2,x⟩ : ℂ) = 0 ∧
        |x-(lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 1 := hx
    have hy' : ψ.LFunction (⟨1/2,y⟩ : ℂ) = 0 ∧
        |y-(lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 1 := hy
    have hxr : Lemma59ExtendedZeroOmega D (⟨1/2,x⟩ : ℂ) :=
      ⟨by norm_num,by change |x-(lemma23PaperCenter D).im| < _; linarith only [hx'.2]⟩
    have hxdata := hall.2.2 hxr (hprod hx'.1)
    have hnorm : ‖(⟨1/2,y⟩ : ℂ)-(⟨1/2,x⟩ : ℂ)‖ = |x-y| := by
      simpa only [abs_sub_comm] using lemma59_critical_line_norm_eq_im_distance
        (ρ := (⟨1/2,x⟩ : ℂ)) (σ := (⟨1/2,y⟩ : ℂ)) rfl rfl
    by_contra hbad
    have hnpos : 0 < ‖(⟨1/2,y⟩ : ℂ)-(⟨1/2,x⟩ : ℂ)‖ := by
      rw [hnorm]
      exact abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hnlt : ‖(⟨1/2,y⟩ : ℂ)-(⟨1/2,x⟩ : ℂ)‖ < lemma46InnerRadius D c := by
      rw [hnorm]
      exact (lt_of_not_ge hbad).trans_le hall.1
    have hh := hxdata.2.2 ((⟨1/2,y⟩ : ℂ)-(⟨1/2,x⟩ : ℂ)) hnpos hnlt
    rw [add_sub_cancel] at hh
    exact hh (hprod hy'.1)
  obtain ⟨lo,hlo,hloCut⟩ := lemma81_separated_lower_cut S
    (H := (lemma23PaperCenter D).im-lemma23PaperL D ^ 405) (by positivity : 0 < lemma44PaperAlpha D/2) hsep
  obtain ⟨hi,hhi,hhiCut⟩ := lemma81_separated_upper_cut S
    (H := (lemma23PaperCenter D).im+lemma23PaperL D ^ 405) (by positivity : 0 < lemma44PaperAlpha D/2) hsep
  have hquarter : lemma44PaperAlpha D/2/2 = lemma44PaperAlpha D/4 := by ring
  rw [hquarter] at hlo hhi
  have horder : lo < hi := by
    have hl := (abs_le.mp hlo).2
    have hu := (abs_le.mp hhi).1
    linarith only [hl,hu,hH1,haq]
  refine ⟨lo,hi,hlo,hhi,horder,?_,?_⟩
  · intro ρ hz
    constructor
    · intro hρ
      have hρclosed : Lemma81ClosedRectangle D lo hi ρ := ⟨hρ.1.le,hρ.2.1.le,hρ.2.2.le⟩
      have ht := lemma81_closed_rectangle_height hlo hhi hρclosed
      have ht1 : |ρ.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405+1 := by
        linarith only [ht,haq]
      have hr : |ρ.re-1/2| < 1/2 := by linarith only [hρ.1,haq]
      have hm := hSmem (hcrit hr ht1 hz) ht1 hz
      have hlow := (hloCut ρ.im hm).2.mp hρ.2.1
      have hupp := (hhiCut ρ.im hm).2.mp hρ.2.2
      exact ⟨hr,abs_lt.mpr ⟨by linarith only [hlow],by linarith only [hupp]⟩⟩
    · intro hρ
      have ht1 : |ρ.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405+1 := by
        linarith only [hρ.2]
      have hr := hcrit hρ.1 ht1 hz
      have hm := hSmem hr ht1 hz
      refine ⟨by rw [hr]; simpa using ha,?_,?_⟩
      · exact (hloCut ρ.im hm).2.mpr (by linarith only [(abs_lt.mp hρ.2).1])
      · exact (hhiCut ρ.im hm).2.mpr (by linarith only [(abs_lt.mp hρ.2).2])
  · intro s hs ρ hz
    by_contra hbad
    have hnear : ‖s-ρ‖ < lemma44PaperAlpha D/4 := by
      have hh := lt_of_not_ge hbad
      linarith only [hh]
    have hre : |ρ.re-s.re| ≤ ‖s-ρ‖ := by
      simpa only [sub_re,abs_sub_comm] using Complex.abs_re_le_norm (s-ρ)
    have him : |ρ.im-s.im| ≤ ‖s-ρ‖ := by
      simpa only [sub_im,abs_sub_comm] using Complex.abs_im_le_norm (s-ρ)
    have hρr : |ρ.re-1/2| < 1/2 := by
      have hh := abs_add_le (ρ.re-s.re) (s.re-1/2)
      rw [sub_add_sub_cancel] at hh
      linarith only [hh,hre,hs.1.1,hnear,haq]
    have hsheight := lemma81_closed_rectangle_height hlo hhi hs.1
    have hρheight : |ρ.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405+1 := by
      have hh := abs_add_le (ρ.im-s.im) (s.im-(lemma23PaperCenter D).im)
      rw [sub_add_sub_cancel] at hh
      linarith only [hh,him,hsheight,hnear,haq]
    have hρcrit := hcrit hρr hρheight hz
    have hm := hSmem hρcrit hρheight hz
    rcases hs.2 with hvertical | hlower | hupper
    · have hh := Complex.abs_re_le_norm (s-ρ)
      rw [sub_re,hρcrit,hvertical] at hh
      linarith only [hh,hnear,ha]
    · have hh := (hloCut ρ.im hm).1
      rw [hquarter,← hlower] at hh
      linarith only [hh,him,hnear]
    · have hh := (hhiCut ρ.im hm).1
      rw [hquarter,← hupper] at hh
      linarith only [hh,him,hnear]

end ZhangLS.Spec
