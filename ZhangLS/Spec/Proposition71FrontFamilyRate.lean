import ZhangLS.Spec.Proposition71FrontContourObjects
import ZhangLS.Spec.Lemma34ShortMean

/-! # Actual primitive-prime-family normalization of the common front error

Character count is paid by the literal prime mass. A bounded outer weight is
allowed, so the original complex-beta weight in Section14 remains visible.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 4000000

lemma proposition71_actual_family_card_le_mass {D : ℕ} (hL : 3≤lemma23PaperL D) :
    ((lemma33ActualFamily D).card : ℝ)≤lemma33ActualPrimeMass D := by
  have hP : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg (by linarith : 0≤lemma23PaperL D) 9)
  have hshort : 1≤⌊lemma23PaperP D⌋₊ := Nat.le_floor (by exact_mod_cast hP)
  have hmean := lemma34_actual_short_mean_bound D 1 hshort (fun _ => (1 : ℂ))
  simpa [lemma33ActualMean] using hmean

/-- Both q=p and q=Dp are permitted through the actual conductor function N.
The character governing Z is independent of the coefficient characters.
No Assumption (A), prime number theorem or positive prime-mass lower bound is
needed for this analytic transformation. -/
theorem proposition71_front_actual_family_rate {D : ℕ} (hD : 1<D)
    (hL : 20000≤lemma23PaperL D)
    (G : Finset (lemma33CharacterIndex D)) (hG : G⊆lemma33ActualFamily D)
    (N : lemma33CharacterIndex D → ℕ) [∀ψ, NeZero (N ψ)]
    (θ : (ψ : lemma33CharacterIndex D) → DirichletCharacter ℂ (N ψ))
    (hθ : ∀ψ∈G, (θ ψ).IsPrimitive) (hN : ∀ψ∈G, N ψ≠1)
    (hNP : ∀ψ∈G, (N ψ : ℝ)≤2*lemma23PaperP D^2)
    {Bc Ba W : ℝ} (hBc : 0≤Bc) (hBa : 0≤Ba) (hW : 0≤W)
    (c a : lemma33CharacterIndex D → ℕ → ℂ)
    (hc : ∀ψ∈G, ∀n, 0<n → ‖c ψ n‖≤Bc*(lemma34Tau 5 n : ℝ))
    (S : lemma33CharacterIndex D → Finset ℕ)
    (hS : ∀ψ∈G, ∀n∈S ψ, 0<n ∧ (n : ℝ)≤lemma23PaperP D)
    (ha : ∀ψ∈G, ∀n∈S ψ, ‖a ψ n‖≤Ba)
    (w : lemma33CharacterIndex D → ℂ) (hw : ∀ψ∈G, ‖w ψ‖≤W) :
    ‖∑ψ∈G, w ψ*(lemma81NormalizedSegmentIntegral D 1
        (proposition71FrontActualKernel D (θ ψ) (c ψ) (S ψ) (a ψ))-
      (gaussSum (θ ψ)⁻¹ ZMod.stdAddChar/(N ψ : ℂ))*
        (∑' m, proposition71DeltaOneDoubleTerm D (c ψ) (S ψ) (a ψ) (N ψ : ℝ) m))‖≤
      (W*proposition71FrontErrorConstant*Bc*Ba/(D : ℝ))*lemma33ActualPrimeMass D := by
  have hK : 0≤proposition71FrontErrorConstant*Bc*Ba/(D : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg proposition71_front_error_constant_pos.le hBc) hBa) (Nat.cast_nonneg D)
  have hcard : (G.card : ℝ)≤lemma33ActualPrimeMass D :=
    (by exact_mod_cast card_le_card hG : (G.card : ℝ)≤(lemma33ActualFamily D).card).trans
      (proposition71_actual_family_card_le_mass (by linarith))
  calc
    _≤∑ψ∈G, ‖w ψ*(lemma81NormalizedSegmentIntegral D 1
        (proposition71FrontActualKernel D (θ ψ) (c ψ) (S ψ) (a ψ))-
      (gaussSum (θ ψ)⁻¹ ZMod.stdAddChar/(N ψ : ℂ))*
        (∑' m, proposition71DeltaOneDoubleTerm D (c ψ) (S ψ) (a ψ) (N ψ : ℝ) m))‖ := norm_sum_le _ _
    _≤∑_ψ∈G, W*(proposition71FrontErrorConstant*Bc*Ba/(D : ℝ)) := by
      apply sum_le_sum
      intro ψ hψ
      rw [norm_mul,proposition71_front_original_contour_exact]
      exact mul_le_mul (hw ψ hψ)
        (proposition71_front_transform_uniform_rate hD hL (hNP ψ hψ) (θ ψ) (hθ ψ hψ)
          (hN ψ hψ) hBc hBa (c ψ) (hc ψ hψ) (S ψ) (hS ψ hψ) (a ψ) (ha ψ hψ)).2
        (norm_nonneg _) hW
    _=(W*(proposition71FrontErrorConstant*Bc*Ba/(D : ℝ)))*(G.card : ℝ) := by simp [mul_comm]
    _≤(W*(proposition71FrontErrorConstant*Bc*Ba/(D : ℝ)))*lemma33ActualPrimeMass D :=
      mul_le_mul_of_nonneg_left hcard (mul_nonneg hW hK)
    _=_ := by ring

end ZhangLS.Spec
