import ZhangLS.Spec.Proposition71MellinInversion

/-! # Exact finite-sum/Mellin bridge with the full hr scale

This module proves the actual interchange used in (7.14). All powers use
positive real bases, and the factor (hr/l)^(σ+it) is retained explicitly.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Finset
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma proposition71_inverse_mellin_integrand_integrable {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {σ x : ℝ}
    (hσ : 1/2≤σ) (hx : 0<x) :
    Integrable (fun t : ℝ => (x : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))*
      lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)) := by
  have hδ := proposition71_actual_delta_vertical_integrable hD hL hσ
  have hp : Continuous (fun t : ℝ => (x : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hm := hp.aestronglyMeasurable.mul hδ.aestronglyMeasurable
  apply (hδ.norm.const_mul (x^(-σ))).mono' hm
  apply ae_of_all
  intro t
  dsimp only [Pi.mul_apply]
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma proposition71_scaled_mellin_power {p h r l : ℝ}
    (hp : 0<p) (hh : 0<h) (hr : 0<r) (hl : 0<l) (s : ℂ) :
    ((l/(p*h*r) : ℝ) : ℂ)^(-s)=
      ((h*r/l : ℝ) : ℂ)^s*(p : ℂ)^s := by
  have hx : 0<l/(p*h*r) := by positivity
  have harg : (((l/(p*h*r) : ℝ) : ℂ)).arg≠Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  have hinv : (((l/(p*h*r) : ℝ) : ℂ))⁻¹=
      ((h*r/l : ℝ) : ℂ)*(p : ℂ) := by
    push_cast
    field_simp
  rw [Complex.cpow_neg,←Complex.inv_cpow _ _ harg,hinv]
  exact Complex.mul_cpow_ofReal_nonneg (by positivity) hp.le s

/-- The scaling error flagged in the source is not hidden: on Re(s)=1,
the extracted factor has norm exactly hr/l. -/
theorem proposition71_extracted_scale_norm {h r l t : ℝ}
    (hh : 0<h) (hr : 0<r) (hl : 0<l) :
    ‖((h*r/l : ℝ) : ℂ)^((1 : ℂ)+(t : ℂ)*I)‖=h*r/l := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<h*r/l)]
  simp

/-- Exact finite prime-sum/Mellin inversion, before estimates or conductor
reduction. It applies to the genuine prime family and its actual coefficients. -/
theorem proposition71_actual_finite_mellin_sum {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {σ h r l : ℝ}
    (hσ : 1/2≤σ) (hh : 0<h) (hr : 0<r) (hl : 0<l)
    (S : Finset ℕ) (hS : ∀ p∈S, 0<p) (a : ℕ → ℂ) :
    (∑ p ∈ S, a p*lemma53PaperDelta D (l/((p : ℝ)*h*r)))=
      ((1/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ,
        lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)*
          ((h*r/l : ℝ) : ℂ)^((σ : ℂ)+(t : ℂ)*I)*
            ∑ p ∈ S, a p*(p : ℂ)^((σ : ℂ)+(t : ℂ)*I) := by
  let F : ℕ → ℝ → ℂ := fun p t =>
    ((l/((p : ℝ)*h*r) : ℝ) : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))*
      lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)
  have hF (p : ℕ) (hp : p∈S) : Integrable (F p) := by
    have hp' : 0<(p : ℝ) := by exact_mod_cast hS p hp
    exact proposition71_inverse_mellin_integrand_integrable hD hL hσ (by positivity)
  have hI (p : ℕ) (hp : p∈S) :
      lemma53PaperDelta D (l/((p : ℝ)*h*r))=
        ((1/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ, F p t :=
    proposition71_actual_scaled_delta_mellin hD hL hσ
      (by exact_mod_cast hS p hp) hh hr hl
  calc
    _=∑ p∈S, ((1/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ, a p*F p t := by
      apply sum_congr rfl
      intro p hp
      rw [hI p hp,integral_const_mul]
      ring
    _=((1/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ, ∑ p∈S, a p*F p t := by
      rw [←mul_sum,integral_finsetSum S (fun p hp => (hF p hp).const_mul (a p))]
    _=_ := by
      congr 1
      apply integral_congr_ae
      apply ae_of_all
      intro t
      dsimp only
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      dsimp [F]
      rw [proposition71_scaled_mellin_power (by exact_mod_cast hS p hp) hh hr hl]
      simp only [Complex.ofReal_natCast]
      ring

end ZhangLS.Spec
