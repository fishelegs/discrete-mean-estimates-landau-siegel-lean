import ZhangLS.Spec.Proposition71FiniteContourZBound
import ZhangLS.Spec.Proposition71FinitePolynomialGrowth
import ZhangLS.Spec.Lemma81ActualContourShift

/-! # The actual finite-polynomial J(1) to J(0) shift

The primitive functional-equation character θ and coefficient character ψ
remain independent. Every horizontal error is paid by the actual Gaussian.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable def proposition71FiniteFrontKernel {N p : ℕ} [NeZero N]
    (D : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ p)
    (Y X : ℕ) (c a : ℕ → ℂ) (s : ℂ) : ℂ :=
  (lemma23DirichletZ θ s)⁻¹*lemma81FiniteCharacterPolynomial Y c ψ s*
    lemma81FiniteCharacterPolynomial X a ψ⁻¹ (1-s)*lemma81Omega D s

lemma proposition71_finite_front_differentiableAt {N p : ℕ} [NeZero N]
    (D : ℕ) (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (ψ : DirichletCharacter ℂ p) (Y X : ℕ) (c a : ℕ → ℂ)
    {s : ℂ} (hs : 0<s.im) : DifferentiableAt ℂ (proposition71FiniteFrontKernel D θ ψ Y X c a) s := by
  have hz := (lemma23DirichletZ_differentiableAt_of_im_ne_zero θ hs.ne').inv
    (lemma23DirichletZ_ne_zero_of_im_pos θ hθ hN hs)
  have hc := (lemma23FiniteDirichletPolynomial_analyticAt Y (fun n => c n*ψ (n : ZMod p)) s).differentiableAt
  have ha := (lemma23FiniteDirichletPolynomial_analyticAt X (fun n => a n*ψ⁻¹ (n : ZMod p)) (1-s)).differentiableAt.comp s
    (show DifferentiableAt ℂ (fun z : ℂ => 1-z) s by fun_prop)
  exact ((hz.mul hc).mul ha).mul ((lemma81_omega_differentiable D) s)

lemma proposition71_finite_front_boundary_envelope {D N p : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (hlogN : Real.log (N : ℝ)≤3*lemma23PaperL D^9) (hL : 3≤lemma23PaperL D)
    (ψ : DirichletCharacter ℂ p) {Bc Ba : ℝ} (hBc : 0≤Bc) (hBa : 0≤Ba)
    (X : ℕ) (hX : X≤⌊lemma23PaperP D⌋₊) (c a : ℕ → ℂ)
    (hc : ∀n∈Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖c n‖≤Bc*(lemma34Tau 5 n : ℝ))
    (ha : ∀n∈Finset.Icc 1 X, ‖a n‖≤Ba) {s : ℂ}
    (hslo : 1/2≤s.re) (hshi : s.re≤3/2)
    (ht : |s.im-(lemma23PaperCenter D).im|=lemma23PaperL D^405) :
    ‖proposition71FiniteFrontKernel D θ ψ ⌊lemma23PaperP D^2⌋₊ X c a s‖≤
      (243*Bc*Ba)*Real.exp (649*lemma23PaperL D^9)*
        (2*Real.exp (-lemma23PaperL D^10/32)) := by
  have hZ := proposition71_inverse_Z_finite_contour_bound θ hθ hN hlogN hL hslo hshi
    (by rw [ht]; linarith)
  have hlong := proposition71_long_finite_polynomial_exponential hBc hL c hc ψ (by linarith : 0≤s.re)
  have hshort := proposition71_short_finite_polynomial_norm hBa X hX a ha ψ⁻¹
    (s := 1-s) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have hω := lemma81_gaussian_boundary_decay_at hL
    (show |s.re-1/2|≤1 from abs_le.mpr ⟨by linarith,by linarith⟩) (by rw [ht]; linarith)
  unfold proposition71FiniteFrontKernel
  simp only [norm_mul]
  calc
    _≤Real.exp (600*lemma23PaperL D^9)*(243*Bc*Real.exp (47*lemma23PaperL D^9))*
        (Ba*lemma23PaperP D^2)*(2*Real.exp (-lemma23PaperL D^10/32)) := by gcongr
    _=_ := by
      have hP : lemma23PaperP D^2=Real.exp (2*lemma23PaperL D^9) := by
        rw [lemma23PaperP,←Real.exp_nat_mul]; norm_num
      rw [hP]
      have he : Real.exp (600*lemma23PaperL D^9)*Real.exp (47*lemma23PaperL D^9)*
          Real.exp (2*lemma23PaperL D^9)=Real.exp (649*lemma23PaperL D^9) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      calc
        _=(243*Bc*Ba)*(Real.exp (600*lemma23PaperL D^9)*Real.exp (47*lemma23PaperL D^9)*
          Real.exp (2*lemma23PaperL D^9))*(2*Real.exp (-lemma23PaperL D^10/32)) := by ring
        _=_ := by rw [he]

/-- A uniform pointwise shift for the genuine finite model. No exceptional
family or averaged bound is assumed; its exact critical-line modulus is one. -/
theorem proposition71_finite_front_shift {Bc Ba : ℝ} (hBc : 0≤Bc) (hBa : 0≤Ba)
    {ε : ℝ} (hε : 0<ε) :
    ∃ D₀ : ℕ, lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ {D N p : ℕ} [NeZero N], D₀≤D →
      ∀ (θ : DirichletCharacter ℂ N), θ.IsPrimitive → N≠1 →
      Real.log (N : ℝ)≤3*lemma23PaperL D^9 →
      ∀ (ψ : DirichletCharacter ℂ p) (X : ℕ), X≤⌊lemma23PaperP D⌋₊ →
      ∀ c a : ℕ → ℂ,
      (∀n∈Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖c n‖≤Bc*(lemma34Tau 5 n : ℝ)) →
      (∀n∈Finset.Icc 1 X, ‖a n‖≤Ba) →
      ‖lemma81NormalizedSegmentIntegral D 1 (proposition71FiniteFrontKernel D θ ψ ⌊lemma23PaperP D^2⌋₊ X c a)-
        lemma81NormalizedSegmentIntegral D 0 (proposition71FiniteFrontKernel D θ ψ ⌊lemma23PaperP D^2⌋₊ X c a)‖≤ε := by
  obtain ⟨Ne,hNe⟩ := lemma81_uniform_boundary_envelope_small
    (show 0≤243*Bc*Ba by positivity) (by norm_num : (0 : ℝ)≤649) (ε/2) (by positivity)
  refine ⟨max lemma23SectionFourModulusThreshold Ne,le_max_left _ _,?_⟩
  intro D N p _ hD θ hθ hN hlogN ψ X hX c a hc ha
  have hDs := (le_max_left _ _).trans hD
  have hDe := (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold hDs).1
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hLp : 0<lemma23PaperL D := by linarith
  let lo := (lemma23PaperCenter D).im-lemma23PaperL D^405
  let hi := (lemma23PaperCenter D).im+lemma23PaperL D^405
  let F := proposition71FiniteFrontKernel D θ ψ ⌊lemma23PaperP D^2⌋₊ X c a
  have hH : 0<lemma23PaperL D^405 := pow_pos hLp _
  have hheight {s : ℂ} (hs : s.im∈Icc lo hi) :
      |s.im-(lemma23PaperCenter D).im|≤lemma23PaperL D^405 := by
    dsimp [lo,hi] at hs
    exact abs_le.mpr ⟨by linarith only [hs.1],by linarith only [hs.2]⟩
  have han : DifferentiableOn ℂ F (Icc (1/2 : ℝ) (3/2) ×ℂ Icc lo hi) := by
    intro s hs
    have hwide : |s.im-(lemma23PaperCenter D).im|≤2*lemma23PaperL D^405+3 := by
      have hh := hheight hs.2
      linarith
    have ht : 0<s.im := by linarith only [(lemma61_wide_height_data hL3 hwide).2.1]
    exact (proposition71_finite_front_differentiableAt D θ hθ hN ψ _ X c a ht).differentiableWithinAt
  have hedge (x t : ℝ) (hx : x∈Icc (1/2 : ℝ) (3/2)) (ht : t=lo ∨ t=hi) :
      ‖F ((x : ℂ)+(t : ℂ)*I)‖≤ε/2 := by
    have him : |((x : ℂ)+(t : ℂ)*I).im-(lemma23PaperCenter D).im|=lemma23PaperL D^405 := by
      simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero]
      rcases ht with rfl|rfl <;> dsimp [lo,hi]
      · rw [sub_sub_cancel_left,abs_neg,abs_of_pos hH]
      · rw [add_sub_cancel_left,abs_of_pos hH]
    exact (proposition71_finite_front_boundary_envelope θ hθ hN hlogN hL3 ψ hBc hBa X hX c a hc ha
      (by simpa using hx.1) (by simpa using hx.2) him).trans (hNe D hDe)
  have hvert := lemma81_rectangle_vertical_difference_bound F
    (by norm_num : (1/2 : ℝ)≤3/2) (by norm_num : (3/2 : ℝ)-1/2≤1)
    (by positivity : 0≤ε/2)
    (lemma81_rectangle_cauchy F (by norm_num) (by dsimp [lo,hi]; linarith) han)
    (fun x hx => hedge x lo hx (Or.inl rfl)) (fun x hx => hedge x hi hx (Or.inr rfl))
  rw [lemma81_normalized_segment_eq_vertical,lemma81_normalized_segment_eq_vertical,←mul_sub,norm_mul]
  norm_num only [add_zero,show (1/2 : ℝ)+1=3/2 by norm_num]
  have hv : ‖(∫ y in lo..hi, F (((3/2 : ℝ) : ℂ)+(y : ℂ)*I))-
      (∫ y in lo..hi, F (((1/2 : ℝ) : ℂ)+(y : ℂ)*I))‖≤ε := by
    rw [norm_sub_rev]
    exact hvert.trans_eq (by ring)
  exact (mul_le_of_le_one_left (norm_nonneg _) lemma81_normalization_factor_norm_le_one).trans hv

end ZhangLS.Spec
