import ZhangLS.Spec.Proposition71LargeLPrimeKernel
import ZhangLS.Spec.Proposition71TauDirichlet

/-! # The actual infinite l>P² part of Section7 σ

The error object is the literal omitted tail, not a subtraction-defined
residual. Absolute convergence and its norm bound follow from actual Δ and
τ₅ estimates; the full prime sum and (l,h)=1 remain in the definition.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71SigmaTerm {r : ℕ} (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) (l : ℕ) : ℂ :=
  if 0<l ∧ l.Coprime h then
    (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
      ∑ p∈lemma56PaperPrimes D, (p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r)*
        lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ)))
  else 0

noncomputable def proposition71SigmaLargeLTerm {r : ℕ} (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) (l : ℕ) : ℂ :=
  if lemma23PaperP D^2<(l : ℝ) then proposition71SigmaTerm D c b a h d θ l else 0

noncomputable def proposition71SigmaLargeLTail {r : ℕ} (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) : ℂ :=
  ∑' l, proposition71SigmaLargeLTerm D c b a h d θ l

/-- A genuine pointwise summable majorant for the literal omitted terms. -/
theorem proposition71_large_l_term_majorant :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ {D r : ℕ} (θ : DirichletCharacter ℂ r),
      D₀≤D → 1<D → 2000≤lemma23PaperL D → ∀ c b B : ℝ, 0≤B →
        ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) → ∀ h d : ℕ, 0<h → 0<r →
          ((h*r : ℕ) : ℝ)≤lemma81Cutoff D → ∀ l : ℕ,
            ‖proposition71SigmaLargeLTerm D c b a h d θ l‖≤
              (2*proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*
                lemma23PaperP D*lemma56PrimeMass D*((h : ℝ)*(r : ℝ))^2*
                  B*(lemma34Tau 5 d : ℝ))*((lemma34Tau 5 l : ℝ)/(l : ℝ)^2) := by
  obtain ⟨D₀,hD₀,hkernel⟩ := proposition71_large_l_prime_kernel
  refine ⟨D₀,hD₀,?_⟩
  intro D r θ hDN hD hL c b B hB a ha h d hh hr hcut l
  have hC := proposition71_large_delta_tail_constant_pos
  have hM := lemma56_prime_mass_nonneg D
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hhp : 0<(h : ℝ) := by exact_mod_cast hh
  have hrp : 0<(r : ℝ) := by exact_mod_cast hr
  unfold proposition71SigmaLargeLTerm
  split_ifs with hl
  · unfold proposition71SigmaTerm
    split_ifs with hc
    · have hk := hkernel θ hDN hD hL b (h : ℝ) (l : ℝ) hhp hr (by simpa only [Nat.cast_mul] using hcut) hl
      have hf := proposition71_actual_dilated_kappa_majorant D c d hB a ha l
      rw [norm_mul,norm_mul]
      calc
        _≤(B*(lemma34Tau 5 d : ℝ)*(lemma34Tau 5 l : ℝ))*1*
            (2*proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*
              lemma23PaperP D*lemma56PrimeMass D*((h : ℝ)*(r : ℝ)/(l : ℝ))^2) := by
          gcongr
          exact θ.norm_le_one _
        _=_ := by ring
    · simp only [norm_zero]; positivity
  · simp only [norm_zero]; positivity

/-- The actual omitted series is absolutely convergent, uniformly with the
full h,r scale and the actual prime mass left visible. -/
theorem proposition71_large_l_tail_bound :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ {D r : ℕ} (θ : DirichletCharacter ℂ r),
      D₀≤D → 1<D → 2000≤lemma23PaperL D → ∀ c b B : ℝ, 0≤B →
        ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) → ∀ h d : ℕ, 0<h → 0<r →
          ((h*r : ℕ) : ℝ)≤lemma81Cutoff D →
            Summable (proposition71SigmaLargeLTerm D c b a h d θ) ∧
              ‖proposition71SigmaLargeLTail D c b a h d θ‖≤
                (2*proposition71LargeDeltaTailConstant*proposition71TauFiveQuadraticMass)*
                  B*(lemma34Tau 5 d : ℝ)*(h : ℝ)*(r : ℝ)*lemma56PrimeMass D*
                    lemma23PaperP D^2*Real.exp (-lemma23PaperL D^10/2) := by
  obtain ⟨D₀,hD₀,hterm⟩ := proposition71_large_l_term_majorant
  refine ⟨D₀,hD₀,?_⟩
  intro D r θ hDN hD hL c b B hB a ha h d hh hr hcut
  let K := 2*proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*
    lemma23PaperP D*lemma56PrimeMass D*((h : ℝ)*(r : ℝ))^2*B*(lemma34Tau 5 d : ℝ)
  have hC := proposition71_large_delta_tail_constant_pos
  have hM := lemma56_prime_mass_nonneg D
  have hτ := proposition71_tau_five_quadratic_mass_pos
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hK : 0≤K := by dsimp [K]; positivity
  have hf := hterm θ hDN hD hL c b B hB a ha h d hh hr hcut
  refine ⟨proposition71_tau_dominated_series_summable hK hf,?_⟩
  have hn := proposition71_tau_dominated_tsum_bound hK hf
  change ‖proposition71SigmaLargeLTail D c b a h d θ‖≤K*proposition71TauFiveQuadraticMass at hn
  apply hn.trans
  have hhrP : (h : ℝ)*(r : ℝ)≤lemma23PaperP D := by
    simpa only [Nat.cast_mul] using hcut.trans (proposition71_cutoff_le_P D)
  have hbudget : lemma23PaperP D*((h : ℝ)*(r : ℝ))^2≤
      lemma23PaperP D^2*((h : ℝ)*(r : ℝ)) := by
    have hv := mul_le_mul_of_nonneg_left hhrP (by positivity : 0≤lemma23PaperP D*((h : ℝ)*(r : ℝ)))
    convert hv using 1 <;> ring
  calc
    _=(2*proposition71LargeDeltaTailConstant*proposition71TauFiveQuadraticMass)*
        B*(lemma34Tau 5 d : ℝ)*lemma56PrimeMass D*Real.exp (-lemma23PaperL D^10/2)*
          (lemma23PaperP D*((h : ℝ)*(r : ℝ))^2) := by dsimp [K]; ring
    _≤(2*proposition71LargeDeltaTailConstant*proposition71TauFiveQuadraticMass)*
        B*(lemma34Tau 5 d : ℝ)*lemma56PrimeMass D*Real.exp (-lemma23PaperL D^10/2)*
          (lemma23PaperP D^2*((h : ℝ)*(r : ℝ))) := by gcongr
    _=_ := by ring

end ZhangLS.Spec
