import ZhangLS.Spec.AppendixBTailBoundaryMass
import ZhangLS.Spec.AppendixBTailFarBoundary
import ZhangLS.Spec.AppendixBRoughReplacementB2

/-! Application of the checked pointwise rho estimates to genuine finite and
infinite Gaussian terms. No coefficient-error premise remains in these wrappers. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical

noncomputable def appendixBRhoMonomialCoefficient (X : ℝ) (β γ : ℂ) (n : ℕ) : ℂ :=
  lemma151Rho β n/n*((X/n : ℝ) : ℂ)^γ

lemma appendixB_rho_monomial_norm {X : ℝ} (hX : 0<X) (β : ℂ)
    {γ : ℂ} (hγ : γ.re=0) (n : ℕ) :
    ‖appendixBRhoMonomialCoefficient X β γ n‖=‖lemma151Rho β n‖/(n : ℝ) := by
  by_cases hn : n=0
  · simp [hn,appendixBRhoMonomialCoefficient]
  have hnp : 0<n := Nat.pos_of_ne_zero hn
  have hnr : 0<(n : ℝ) := Nat.cast_pos.mpr hnp
  rw [appendixBRhoMonomialCoefficient,norm_mul,norm_div,Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hX hnr),hγ,Real.rpow_zero,mul_one]

lemma appendixB_original_rho_monomial_bound {D : ℕ} (hL : 0<lemma23PaperL D)
    {X : ℝ} (hX : 0<X) {β γ : ℂ} (hβre : β.re=0)
    (hβ : ‖β‖≤3*lemma44PaperAlpha D) (hγ : γ.re=0)
    {n : ℕ} (hn : 0<n) (hnP : (n : ℝ)≤lemma23PaperP D) :
    ‖appendixBRhoMonomialCoefficient X β γ n‖≤Real.exp (3*Real.pi)/(n : ℝ) := by
  rw [appendixB_rho_monomial_norm hX β hγ]
  exact div_le_div_of_nonneg_right (appendixB_original_rho_norm hL hn hnP hβre hβ)
    (Nat.cast_nonneg _)

lemma appendixB_global_rho_monomial_bound {X : ℝ} (hX : 0<X)
    {β γ : ℂ} (hβre : β.re=0) (hβ : ‖β‖≤1) (hγ : γ.re=0) (n : ℕ) :
    ‖appendixBRhoMonomialCoefficient X β γ n‖≤1 := by
  by_cases hn : n=0
  · simp [hn,appendixBRhoMonomialCoefficient]
  have hnr : 0<(n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [appendixB_rho_monomial_norm hX β hγ]
  exact (div_le_one hnr).mpr (appendixB_rho_norm_le_index hβre hβ n)

lemma appendixB_log_ratio_step {x : ℝ} (hx : 0<x) {n : ℕ} (hn : 0<n) :
    appendixBStrictLogStep (Real.log (x/(n : ℝ)))=
      if (n : ℝ)<x then 1 else 0 := by
  have hnr : 0<(n : ℝ) := Nat.cast_pos.mpr hn
  have hiff : 0<Real.log (x/(n : ℝ)) ↔ (n : ℝ)<x := by
    rw [Real.log_pos_iff (div_pos hx hnr).le,lt_div_iff₀ hnr,one_mul]
  unfold appendixBStrictLogStep
  simp only [hiff]

/-- The genuine finite rho sum has the constant exp(3*pi) boundary weight,
without a divisor-function or log(P) loss on the boundary interval. -/
theorem appendixB_actual_rho_finite_unsmoothing {D : ℕ} (hD : 1<D)
    (hL : 0<lemma23PaperL D) {X x K : ℝ} (hX : 0<X) (hx : 0<x) (hK : 0<K)
    {β γ : ℂ} (hβre : β.re=0) (hβ : ‖β‖≤3*lemma44PaperAlpha D) (hγ : γ.re=0)
    (S : Finset ℕ) (hS : ∀ n∈S, 0<n ∧ (n : ℝ)≤lemma23PaperP D) :
    ‖∑ n∈S, appendixBRhoMonomialCoefficient X β γ n*
      ((zhangGaussianWeight D (x/n)-(if (n : ℝ)<x then 1 else 0) : ℝ) : ℂ)‖≤
      Real.exp (3*Real.pi)*
        (∑ n∈appendixBGaussianBoundaryBand D K (fun n => Real.log (x/(n : ℝ))) S, (1 : ℝ)/n)+
      ((Real.sqrt Real.pi)⁻¹*Real.exp (-(K^2))/K)*Real.exp (3*Real.pi)*
        (∑ n∈S\appendixBGaussianBoundaryBand D K (fun n => Real.log (x/(n : ℝ))) S, (1 : ℝ)/n) := by
  let u := fun n : ℕ => Real.log (x/(n : ℝ))
  let a := appendixBRhoMonomialCoefficient X β γ
  have ha : ∀ n∈S, ‖a n‖≤Real.exp (3*Real.pi)/(n : ℝ) := by
    intro n hn
    exact appendixB_original_rho_monomial_bound hL hX hβre hβ hγ (hS n hn).1 (hS n hn).2
  have hh := appendixB_gaussian_finite_unsmoothing hD S u a hK (Real.exp_pos _).le ha
  have he : (∑ n∈S, appendixBRhoMonomialCoefficient X β γ n*
      ((zhangGaussianWeight D (x/n)-(if (n : ℝ)<x then 1 else 0) : ℝ) : ℂ))=
      ∑ n∈S, a n*((zhangGaussianWeight D (Real.exp (u n))-
        appendixBStrictLogStep (u n) : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [u,a]
    rw [Real.exp_log (div_pos hx (Nat.cast_pos.mpr (hS n hn).1)),
      appendixB_log_ratio_step hx (hS n hn).1]
  rw [he]
  exact hh

/-- The actual rho coefficient discharges the elementary far-tail premise. -/
theorem appendixB_actual_rho_far_gaussian {D : ℕ} (hD : 1<D)
    (hL : 3≤lemma23PaperL D) {X x : ℝ} (hX : 0<X) (hx : 0<x)
    (hlog : Real.log x≤2*lemma23PaperL D^9) (N : ℕ) (hcut : 2*x≤(N : ℝ))
    {β γ : ℂ} (hβre : β.re=0) (hβ : ‖β‖≤1) (hγ : γ.re=0) :
    Summable (fun n : ℕ => if N<n then appendixBRhoMonomialCoefficient X β γ n*
      (zhangGaussianWeight D (x/n) : ℂ) else 0) ∧
    ‖∑' n : ℕ, if N<n then appendixBRhoMonomialCoefficient X β γ n*
      (zhangGaussianWeight D (x/n) : ℂ) else 0‖≤
      lemma44InverseSquareMass*Real.exp (-(lemma23PaperL D^10)) :=
  appendixB_far_gaussian_summable_bound hD hL hx hlog N hcut _
    (appendixB_global_rho_monomial_bound hX hβre hβ hγ)

end ZhangLS.Spec
