import ZhangLS.Spec.Proposition141EighthPrimeIntegral
import ZhangLS.Spec.Proposition71MellinFiniteSum

/-! # Actual small-conductor Δ prime sum, with full scale and complex β

Only the independent exact finite-sum/Mellin bridge is shared with Section7.
No Proposition7.1 or Proposition14.1 target is imported as an estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped ComplexConjugate

noncomputable def proposition141ActualShiftedPrimeKernel {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N) (β : ℂ) (h r l : ℝ) : ℂ :=
  ∑ p ∈ lemma56PaperPrimes D, χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β*
    lemma53PaperDelta D (l/((p:ℝ)*h*r))

/-- Exact original-kernel transformation, retaining (hr/l)^s. -/
theorem proposition141_actual_shifted_prime_mellin_identity {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (β : ℂ) {h r l : ℝ}
    (hh : 0<h) (hr : 0<r) (hl : 0<l) :
    proposition141ActualShiftedPrimeKernel χ θ β h r l =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
        lemma54PaperDeltaMellin D (1+I*(t:ℂ))*
          ((h*r/l:ℝ):ℂ)^(1+I*(t:ℂ))*proposition141ShiftedProductPrimeSum χ θ β t := by
  have hS : ∀p∈lemma56PaperPrimes D, 0<p := by
    intro p hp
    exact ((lemma56_mem_paper_primes D p).mp hp).1.pos
  have he := proposition71_actual_finite_mellin_sum hD hL (σ := 1) (by norm_num)
    hh hr hl (lemma56PaperPrimes D) hS
    (fun p => χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β)
  change proposition141ActualShiftedPrimeKernel χ θ β h r l = _ at he
  rw [he]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [Complex.ofReal_one,mul_comm (t:ℂ) I]
  congr 1
  unfold proposition141ShiftedProductPrimeSum
  apply sum_congr rfl
  intro p hp
  have hp0 : (p:ℂ)≠0 := Nat.cast_ne_zero.mpr (hS p hp).ne'
  rw [Complex.cpow_add (1+I*(t:ℂ)) β hp0]
  ring

/-- Absolute convergence and norm control retain the exact hr/l scale. -/
theorem proposition141_actual_shifted_prime_kernel_integral_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (β : ℂ)
    (hβ : ‖β‖<5*lemma44PaperAlpha D) {h r l : ℝ}
    (hh : 0<h) (hr : 0<r) (hl : 0<l) :
    ‖proposition141ActualShiftedPrimeKernel χ θ β h r l‖ ≤
      (1/(2*Real.pi))*(h*r/l)*proposition141ActualPrimeMellinIntegral χ θ β := by
  let f := proposition141ShiftedProductPrimeSum χ θ β
  let F : ℝ → ℂ := fun t => lemma54PaperDeltaMellin D (1+I*(t:ℂ))*
    ((h*r/l:ℝ):ℂ)^(1+I*(t:ℂ))*f t
  have hscale : 0<h*r/l := by positivity
  have hnorm (t : ℝ) : ‖F t‖=(h*r/l)*
      (‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖*‖f t‖) := by
    dsimp [F]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hscale]
    simp only [add_re,one_re,mul_re,I_re,I_im,ofReal_re,ofReal_im,mul_zero,
      zero_mul,sub_zero,add_zero,Real.rpow_one]
    ring
  have hfc := proposition141_shifted_product_prime_continuous χ θ β
  have hi := lemma54_eighth_actual_product_integrable hD hL f hfc
    (mul_nonneg (Real.exp_nonneg _) (lemma56_prime_mass_nonneg D))
    (proposition141_shifted_product_prime_global_bound χ θ hL β hβ)
  have hFcont : Continuous F := by
    exact ((lemma54_eighth_actual_line_continuous hD hL).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hscale.ne')))).mul hfc
  have hFi : Integrable F := by
    apply (hi.const_mul (h*r/l)).mono' hFcont.aestronglyMeasurable
    exact ae_of_all _ (fun t => (hnorm t).le)
  rw [proposition141_actual_shifted_prime_mellin_identity χ θ hD hL β hh hr hl,norm_mul]
  have hπ : ‖((1/(2*Real.pi):ℝ):ℂ)‖=1/(2*Real.pi) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  rw [hπ]
  have hn := norm_integral_le_integral_norm (f := F) (μ := volume)
  simp_rw [hnorm] at hn
  rw [integral_const_mul] at hn
  have hh' := mul_le_mul_of_nonneg_left hn (show 0≤1/(2*Real.pi) by positivity)
  simpa only [F,f,proposition141ActualPrimeMellinIntegral,mul_assoc] using hh'

/-- Complete individual prime-kernel estimate at small conductor. The
D⁻⁷ tail is present, and no outer d,h,r summation has been suppressed. -/
theorem proposition141_uniform_small_shifted_prime_kernel_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ {D N : ℕ} [NeZero N] (χ : RealPrimitiveCharacter D)
      (hd : D∣N) (θ : DirichletCharacter ℂ N),
      D₀≤D → NormalizedAssumptionA χ → (N:ℝ)≤lemma23PaperP D →
      θ≠1 → θ≠χ.chi.changeLevel hd → θ.conductor<D^3 →
      ∀ β : ℂ, ‖β‖<5*lemma44PaperAlpha D → ∀ h r l : ℝ, 0<h → 0<r → 0<l →
        ‖proposition141ActualShiftedPrimeKernel χ θ β h r l‖ ≤
          C*lemma23PaperL D^7200*(h*r/l)*lemma56PrimeMass D*
            (lemma56Decay D+(D:ℝ)^(-(7:ℤ))) := by
  obtain ⟨Ci,hCi,Ni,hNi,hibound⟩ := proposition141_uniform_small_product_mellin_integral_bound
  obtain ⟨Nr,hrate⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨Ci/(2*Real.pi),by positivity,max Ni Nr,hNi.trans (le_max_left _ _),?_⟩
  intro D N _ χ hd θ hDN hA hNP hθ hne hcond β hβ h r l hh hr hl
  have hD : 1<D := by have := hNi.trans ((le_max_left Ni Nr).trans hDN); omega
  have hL := (hrate D ((le_max_right Ni Nr).trans hDN)).1
  have hfirst := proposition141_actual_shifted_prime_kernel_integral_bound χ θ hD hL β hβ hh hr hl
  have hsecond := hibound χ hd θ ((le_max_left Ni Nr).trans hDN) hA hNP hθ hne hcond β hβ
  have hm := mul_le_mul_of_nonneg_left hsecond
    (show 0≤(1/(2*Real.pi))*(h*r/l) by positivity)
  exact hfirst.trans (by convert hm using 1 <;> ring)

end ZhangLS.Spec
