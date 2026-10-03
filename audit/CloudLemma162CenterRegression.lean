import ZhangLS.Spec.Lemma162CorrectedQuantitative

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

-- Exceptional source branch: the baseline local numerator vanishes, but the
-- actual raw corrected center is 3/4. Neither test divides by the baseline.
example : lemma162M00 1 (1/2) 1 (1/2)=0 := by
  norm_num [lemma162M00,lemma162M01,lemma162LocalLambda]
example : lemma162RawPolynomial (lemma162M00 1 (1/2) 1 (1/2))
    (lemma162M01 1 (1/2) 1 (1/2)) (lemma162M10 (1/2) 1 (1/2))
    (lemma162M11 1 (1/2)) (lemma162LocalLambda 1 (1/2) 1) 1 1 (1/2)=3/4 := by
  norm_num [lemma162RawPolynomial,lemma162M00,lemma162M01,lemma162M10,lemma162M11,
    lemma162LocalLambda,lemma162RawP,lemma162RawQ,lemma162RawS]

-- The negative-character branch gives the identical finite-shift center.
example (a u b : ℂ) (hu : 1-u≠0) (hvu : 1+u≠0)
    (hub : 1-u*b≠0) (hvub : 1+u*b≠0) :
    lemma162RawPolynomial (lemma162M00 a u (-1) (u*b)) (lemma162M01 a u (-1) (u*b))
      (lemma162M10 u (-1) (u*b)) (lemma162M11 (-1) (u*b))
      (lemma162LocalLambda a u (-1)) b (-1) u=1-a*b*u^2 := by
  apply lemma162_raw_rational_center _ _ _ _ (Or.inr rfl) hu
  · simpa using hvu
  · exact hub
  · simpa using hvub

-- Genuine exceptional character conditional, not a fabricated character.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (h2 : χ.evalNat 2=1)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) :
    lemma162RawPrimeCorrection χ β γ lemma162PrimeTwo 1 =
      1-(2:ℂ)^(-β)*(2:ℂ)^γ*((2:ℂ)⁻¹)^2 := by
  have hd : ¬2∣D := by
    intro h
    have hh := χ.evalNat_eq_zero_of_dvd_modulus h (by norm_num : (2:ℕ)≠1)
    rw [h2] at hh
    norm_num at hh
  simpa [lemma162PrimeTwo,hd] using lemma162_actual_raw_center χ β hβ γ hγ lemma162PrimeTwo

example {D : ℕ} (χ : RealPrimitiveCharacter D) (h2 : χ.evalNat 2=1) :
    lemma161MainTerm χ=2*∏' q : {q : Nat.Primes // 2<q.val}, lemma161MainFactor χ q.val := by
  simp [lemma161MainTerm,h2]
example {D : ℕ} (χ : RealPrimitiveCharacter D) (h2 : χ.evalNat 2≠1) :
    lemma161MainTerm χ=∏' q : Nat.Primes, lemma161MainFactor χ q := by
  simp [lemma161MainTerm,h2]

example {D : ℕ} (χ : RealPrimitiveCharacter D) (q : Nat.Primes) (hq : q.val∣D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) :
    lemma162RawPrimeCorrection χ β γ q 1=(1-(q.val:ℂ)⁻¹)^2 := by
  simp [lemma162_actual_raw_center χ β hβ γ hγ q,hq]

-- Finite-D original beta1: exact numerator equality before any limit.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) :
    lemma162RawEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c 0) 1=
      lemma162RawEulerProduct χ 0 0 1 := by
  rw [lemma162_paper_shift_zero]
  exact lemma162_actual_raw_product_center_diagonal χ _ (lemma161_paper_beta_re D c)

-- The closed sector's real and angular boundary are included.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re=0)
    (γ : ℂ) (hγ : γ.re=0) (s : ℂ) (hs : s.re=9/10)
    (hphase : |s.im| *lemma23PaperL D=1) :
    ‖lemma162RawEulerProduct χ β γ s‖≤lemma162UnramifiedProductBound := by
  exact lemma162_raw_sector_bound χ β hβ γ hγ s hs.ge hphase.le

-- The disk boundary is included, with positive explicit radius.
example {D : ℕ} (hL : 3≤lemma23PaperL D) :
    9/10<(1+(((10*lemma23PaperL D)⁻¹:ℝ):ℂ)).re ∧
      |(1+(((10*lemma23PaperL D)⁻¹:ℝ):ℂ)).im| *lemma23PaperL D≤1 := by
  apply lemma162_disk_in_sector hL
  simp only [add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (inv_nonneg.mpr (by linarith : 0≤10*lemma23PaperL D))]

-- The actual beta1 and beta2 both receive the strong L^-9 comparison.
example (c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, 3≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c) 1-
        lemma162CorrectedCenterMain χ‖≤(lemma162CorrectedCenterAlphaConstant*Real.pi)/lemma23PaperL D^9 ∧
      ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c) 1-
        lemma162CorrectedCenterMain χ‖≤(lemma162CorrectedCenterAlphaConstant*Real.pi)/lemma23PaperL D^9 := by
  obtain ⟨D₀,hD₀,hs,h⟩ := lemma162_paper_corrected_center c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ
  exact ⟨by simpa using h D hD χ 0,by simpa using h D hD χ 1⟩

-- No derivative order or logarithmic power is absorbed into an O-symbol.
example (c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, 3≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
      ‖iteratedDeriv 2 (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c)
        (lemma162PaperShift D c j)) 1‖≤200*lemma162SectorConstant*lemma23PaperL D^2 := by
  obtain ⟨D₀,hD₀,hs,h⟩ := lemma162_paper_cauchy_bounds c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ j
  have hh := h D hD χ j 2
  norm_num [Nat.factorial] at hh
  convert hh using 1
  ring

end ZhangLS.Spec
