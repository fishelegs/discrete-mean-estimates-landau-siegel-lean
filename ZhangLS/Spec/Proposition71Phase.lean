import ZhangLS.Spec.Lemma52Product
import ZhangLS.Spec.Lemma56
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Actual prime-dependent phase, replacing the undefined α₁ in Section 7

The bound is explicit in the *proved* parameters: O_c(αℒ)=O_c(ℒ⁻⁸).
In particular multiplication by the main α⁻¹ coefficient costs only O_c(ℒ).
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

lemma proposition71_imaginary_phase_distance (x : ℝ) :
    ‖Complex.exp (I * (x : ℂ)) + 1‖ ≤ |x - 3*Real.pi| := by
  have h3 : Complex.exp (I * ((3*Real.pi : ℝ) : ℂ)) = -1 := by
    rw [show I * ((3*Real.pi : ℝ) : ℂ) = 3 * ((Real.pi : ℂ)*I) by push_cast; ring]
    have he := Complex.exp_nat_mul ((Real.pi : ℂ)*I) 3
    norm_num [Complex.exp_pi_mul_I] at he
    exact he
  have he : Complex.exp (I * (x : ℂ)) + 1 =
      -(Complex.exp (I * ((x-3*Real.pi : ℝ) : ℂ)) - 1) := by
    have hx : I*(x : ℂ) = I*((x-3*Real.pi : ℝ) : ℂ)+I*((3*Real.pi : ℝ) : ℂ) := by
      push_cast; ring
    rw [hx,Complex.exp_add,h3]
    ring
  rw [he,norm_neg]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := x-3*Real.pi)

lemma proposition71_prime_window_log_error {D p : ℕ}
    (hpwin : p ∈ lemma56PaperPrimes D) :
    0 ≤ Real.log (p : ℝ)-Real.log (lemma23PaperP D) ∧
      Real.log (p : ℝ)-Real.log (lemma23PaperP D) ≤ lemma23PaperL D^(-68 : ℤ) := by
  have hpwin := (lemma56_mem_paper_primes D p).mp hpwin
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hp : 0 < (p : ℝ) := hP.trans hpwin.2.1
  have hlo := Real.log_le_log hP hpwin.2.1.le
  have hratio : (p : ℝ)/lemma23PaperP D ≤ 1+lemma23PaperL D^(-68 : ℤ) :=
    (div_le_iff₀ hP).mpr (by simpa [lemma56PrimeUpper,mul_comm] using hpwin.2.2.le)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp hP)
  rw [Real.log_div hp.ne' hP.ne'] at hlog
  exact ⟨by linarith,by linarith⟩

/-- Explicit uniform phase rate on the actual prime family. No α₁ is introduced. -/
theorem proposition71_actual_prime_phase_rate {D p : ℕ}
    (hpwin : p ∈ lemma56PaperPrimes D)
    {c : ℝ} (hc : 0 ≤ c) (hL : 3 ≤ lemma23PaperL D)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1) :
    ‖(((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c + 1‖ ≤
      (1560 + 3*c*Real.pi) * lemma44PaperAlpha D * lemma23PaperL D := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hp : 0 < (p : ℝ) := (Real.exp_pos _).trans
    ((lemma56_mem_paper_primes D p).mp hpwin).2.1
  have ht : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hlog := proposition71_prime_window_log_error hpwin
  have hlogP : Real.log (lemma23PaperP D) = lemma23PaperL D^9 := by
    simp [lemma23PaperP]
  have hlogT : Real.log (lemma51PaperT0 D) = 519*Real.log (lemma23PaperL D) := by
    rw [lemma51PaperT0,Real.log_pow]; norm_num
  let u := Real.log ((p : ℝ)*lemma51PaperT0 D) - lemma23PaperL D^9
  have hu : 0 ≤ u ∧ u ≤ 520*lemma23PaperL D := by
    dsimp [u]
    rw [Real.log_mul hp.ne' ht.ne',hlogT]
    rw [hlogP] at hlog
    have hz : lemma23PaperL D^(-68 : ℤ) ≤ 1 :=
      zpow_le_one_of_nonpos₀ hL1 (by norm_num)
    have hl0 := Real.log_nonneg hL1
    have hl1 := Real.log_le_self hLp.le
    constructor <;> nlinarith
  have hbase : lemma44PaperAlpha D * lemma23PaperL D^9 = Real.pi := by
    simp only [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
    field_simp
  have hrange : 0 ≤ 1-c*lemma44PaperAlpha D*lemma23PaperL D ∧
      1-c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1 := by
    constructor
    · linarith
    · have hn : 0 ≤ c*lemma44PaperAlpha D*lemma23PaperL D := by positivity
      linarith
  have hx : lemma23PaperOffsetThree D c *
      Real.log ((p : ℝ)*lemma51PaperT0 D) - 3*Real.pi =
      3*lemma44PaperAlpha D*(1-c*lemma44PaperAlpha D*lemma23PaperL D)*u -
        3*c*Real.pi*lemma44PaperAlpha D*lemma23PaperL D := by
    dsimp [u,lemma23PaperOffsetThree]
    rw [← hbase]
    ring
  have habs : |lemma23PaperOffsetThree D c *
      Real.log ((p : ℝ)*lemma51PaperT0 D)-3*Real.pi| ≤
      (1560+3*c*Real.pi)*lemma44PaperAlpha D*lemma23PaperL D := by
    rw [hx]
    have hv : 0 ≤ 3*lemma44PaperAlpha D*(1-c*lemma44PaperAlpha D*lemma23PaperL D)*u :=
      mul_nonneg (mul_nonneg (by positivity) hrange.1) hu.1
    have hvb : 3*lemma44PaperAlpha D*(1-c*lemma44PaperAlpha D*lemma23PaperL D)*u ≤
        1560*lemma44PaperAlpha D*lemma23PaperL D := by
      calc
        _ ≤ 3*lemma44PaperAlpha D*1*(520*lemma23PaperL D) := by gcongr <;> first | exact hu.1 | exact hrange.2 | exact hu.2
        _ = _ := by ring
    have hw : 0 ≤ 3*c*Real.pi*lemma44PaperAlpha D*lemma23PaperL D := by positivity
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hv,abs_of_nonneg hw]; nlinarith)
  have hpow : (((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c =
      Complex.exp (I * ((lemma23PaperOffsetThree D c *
        Real.log ((p : ℝ)*lemma51PaperT0 D) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hp ht).ne'),
      ← Complex.ofReal_log (mul_pos hp ht).le]
    unfold lemma52PaperBetaThree
    congr 1
    push_cast
    ring
  rw [hpow]
  exact (proposition71_imaginary_phase_distance _).trans habs

/-- The same explicit bound on the original character family. -/
theorem proposition71_actual_phase_rate {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {c : ℝ} (hc : 0 ≤ c) (hL : 3 ≤ lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1) :
    ‖(((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c+1‖ ≤
      (1560+3*c*Real.pi)*lemma44PaperAlpha D*lemma23PaperL D :=
  proposition71_actual_prime_phase_rate ((lemma56_paper_prime_family ψ).mp hψ).1 hc hL hsmall

/-- With c fixed before the threshold, the phase error has the absolute
budget αℒ². This is the original E scale after multiplying by α⁻¹. -/
theorem proposition71_uniform_phase_budget {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D →
      3 ≤ lemma23PaperL D ∧ ∀ p ∈ lemma56PaperPrimes D,
        ‖(((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c+1‖ ≤
          lemma44PaperAlpha D*lemma23PaperL D^2 := by
  obtain ⟨Ds,hDs,hsmall⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp (1560+3*c*Real.pi))
  refine ⟨max Ds N,?_⟩
  intro D hD
  have hDsD := (le_max_left _ _).trans hD
  have hND := (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hDs.trans hDsD)).1
  have hLD : 1560+3*c*Real.pi ≤ lemma23PaperL D := by
    have hdexp : Real.exp (1560+3*c*Real.pi) ≤ (D : ℝ) :=
      hN.le.trans (by exact_mod_cast hND)
    have hh := Real.log_le_log (Real.exp_pos _) hdexp
    simpa [lemma23PaperL] using hh
  refine ⟨by linarith,?_⟩
  intro p hp
  have hb := proposition71_actual_prime_phase_rate hp hc.le (by linarith) (by linarith [hsmall D hDsD])
  apply hb.trans
  have ha := (lemma44_alpha_pos_le_one (by linarith : 3≤lemma23PaperL D)).1
  calc
    _ ≤ lemma23PaperL D*lemma44PaperAlpha D*lemma23PaperL D := by gcongr
    _ = _ := by ring

end ZhangLS.Spec
