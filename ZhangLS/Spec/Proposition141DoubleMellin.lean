import ZhangLS.Spec.Proposition141SmallCoefficientSum
import ZhangLS.Spec.Proposition71MellinDoubleSum

/-! # The actual Section14 two-polynomial Mellin transformation

This attaches arbitrary κ*(D₁dl), θ(l), χ(p)conj θ(p), and the full complex
p^β shift to the independent exact finite-sum inversion theorem. It keeps
(hr)^s, and proves absolute integrability before any weighted Cauchy step.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical ComplexConjugate

noncomputable def proposition141DoubleMellinIntegrand {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N) (β : ℂ)
    (κ : ℕ→ℂ) (D₁ d : ℕ) (h r : ℝ) (S : Finset ℕ) (t : ℝ) : ℂ :=
  let s : ℂ := 1+I*(t:ℂ)
  lemma54PaperDeltaMellin D s*((h*r:ℝ):ℂ)^s*
    (∑l∈S,(κ (D₁*d*l)/(l:ℂ)^s)*θ (l:ZMod N))*
    (∑p∈lemma56PaperPrimes D,χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^(s+β))

lemma proposition141_double_mellin_integrand_eq {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N) (β : ℂ)
    (κ : ℕ→ℂ) (D₁ d : ℕ) (h r : ℝ) (S : Finset ℕ) (t : ℝ) :
    proposition141DoubleMellinIntegrand χ θ β κ D₁ d h r S t =
    proposition71DoubleMellinIntegrand D 1 h r S (lemma56PaperPrimes D)
      (fun l => κ (D₁*d*l)*θ (l:ZMod N))
      (fun p => χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β) t := by
  unfold proposition141DoubleMellinIntegrand proposition71DoubleMellinIntegrand
  simp only [Complex.ofReal_one,mul_comm (t:ℂ) I]
  have hK : (∑l∈S,(κ (D₁*d*l)/(l:ℂ)^(1+I*(t:ℂ)))*θ (l:ZMod N)) =
      ∑l∈S,(κ (D₁*d*l)*θ (l:ZMod N))*(l:ℂ)^(-(1+I*(t:ℂ))) := by
    apply sum_congr rfl
    intro l hl
    rw [Complex.cpow_neg,div_eq_mul_inv]
    ring
  have hP : (∑p∈lemma56PaperPrimes D,
      χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^((1+I*(t:ℂ))+β)) =
      ∑p∈lemma56PaperPrimes D,
        (χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β)*(p:ℂ)^(1+I*(t:ℂ)) := by
    apply sum_congr rfl
    intro p hp
    have hp0 : (p:ℂ)≠0 := Nat.cast_ne_zero.mpr ((lemma56_mem_paper_primes D p).mp hp).1.ne_zero
    rw [Complex.cpow_add _ _ hp0]
    ring
  rw [hK,hP]

/-- Absolute integrability of the actual factored Section14 integrand. -/
theorem proposition141_double_mellin_integrable {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (β : ℂ)
    (κ : ℕ→ℂ) (D₁ d : ℕ) {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (S : Finset ℕ) (hS : ∀l∈S,0<l) :
    Integrable (proposition141DoubleMellinIntegrand χ θ β κ D₁ d h r S) := by
  have he : proposition141DoubleMellinIntegrand χ θ β κ D₁ d h r S =
      proposition71DoubleMellinIntegrand D 1 h r S (lemma56PaperPrimes D)
        (fun l => κ (D₁*d*l)*θ (l:ZMod N))
        (fun p => χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β) :=
    funext (proposition141_double_mellin_integrand_eq χ θ β κ D₁ d h r S)
  rw [he]
  exact proposition71_double_mellin_integrand_integrable hD hL (by norm_num) hh hr S
    (lemma56PaperPrimes D) hS (fun p hp => ((lemma56_mem_paper_primes D p).mp hp).1.pos) _ _

/-- Exact actual finite character-sum transformation, with no cancellation
or mean estimate as a premise. The infinite l-tail is a separate obligation. -/
theorem proposition141_actual_double_mellin_identity {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (β : ℂ)
    (κ : ℕ→ℂ) (D₁ d : ℕ) {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (S : Finset ℕ) (hS : ∀l∈S,0<l) :
    proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r S =
      ((1/(2*Real.pi):ℝ):ℂ)*∫t:ℝ,proposition141DoubleMellinIntegrand χ θ β κ D₁ d h r S t := by
  have he := proposition71_actual_double_mellin_sum hD hL (σ:=1) (by norm_num) hh hr S
    (lemma56PaperPrimes D) hS (fun p hp => ((lemma56_mem_paper_primes D p).mp hp).1.pos)
    (fun l => κ (D₁*d*l)*θ (l:ZMod N))
    (fun p => χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β)
  change proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r S = _ at he
  rw [he]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun t => (proposition141_double_mellin_integrand_eq χ θ β κ D₁ d h r S t).symm)

end ZhangLS.Spec
