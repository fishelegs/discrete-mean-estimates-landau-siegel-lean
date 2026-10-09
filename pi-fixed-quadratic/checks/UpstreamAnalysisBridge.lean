import checks.UpstreamPacketArithmetic
import FixedQuadratic.Weights
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds

namespace FixedQuadratic.UpstreamAnalysis
open scoped BigOperators
open OAI.PiExponent
open FixedQuadratic.UpstreamPacketArithmetic

noncomputable def centerError {m : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) (j : ℕ) : Fin m → ℂ :=
  fun i => (j : ℂ)*(2*Complex.I*((β i : ℝ) : ℂ)-2*(Real.pi : ℂ)*Complex.I)

/-- The actual primitive-height approximation supplies precisely the source's
exponential scalar input, including the exp(nu) ceiling cost. -/
theorem actual_center_error_exp {m : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (j k : ℕ) (ν : ℝ) (hk : 1 ≤ k) (hj : j ≤ k) (hν : 0 ≤ ν)
    (happrox : ∀ i, |Real.pi-(β i : ℝ)| ≤
      (primitiveMinpolyHeight (β i : ℝ) : ℝ)^(-ν)) :
    ∀ i, ‖centerError F β j i‖ ≤
      Real.exp (Real.log (2*(k : ℝ))+ν-ν*primitiveWeights F β i) := by
  intro i
  have hH : (1 : ℝ) ≤ primitiveMinpolyHeight (β i : ℝ) := by
    exact_mod_cast primitiveMinpolyHeight_pos (β i : ℝ) (hβ i)
  have hp : (0 : ℝ) < 2*k := by exact_mod_cast (by omega : 0 < 2*k)
  have hh := quadratic_center_period_error (β i : ℝ)
    (primitiveMinpolyHeight (β i : ℝ) : ℝ) ν j k hH hν hj (happrox i)
  simpa only [centerError, primitiveWeights, sub_eq_add_neg,
    Real.exp_add, Real.exp_log hp, neg_mul] using hh

/-- Changed centers are accepted by the proved source translation estimate.
This is a row-scalar theorem; collision and determinant summation remain open. -/
theorem actual_rowScalar_exp {m : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (j k : ℕ) (ν N wmin v scale : ℝ) (hk : 1 ≤ k) (hj : j ≤ k)
    (hν : 0 ≤ ν) (hwmin : 0 < wmin) (hv : 0 < v) (hscale : 0 < scale)
    (hw : ∀ i, wmin ≤ primitiveWeights F β i)
    (happrox : ∀ i, |Real.pi-(β i : ℝ)| ≤
      (primitiveMinpolyHeight (β i : ℝ) : ℝ)^(-ν))
    (b a : Fin m →₀ ℕ) (d : ∀ i, Fin (a i-b i+1)) (ell : ℕ)
    (ha : MatrixTranslationBounds.weight (primitiveWeights F β) (fun i => a i) ≤ N)
    (hell : (ell : ℝ) ≤ N/v) :
    ‖RowTranslation.rowScalar (centerError F β j)
      (fun i => RowTranslation.tail
        (MatrixTranslationBounds.truncationOrder scale v (primitiveWeights F β i)) (PowerSeries.log ℂ))
      b a d ell‖ ≤
      Real.exp (-ν*(MatrixTranslationBounds.weight (primitiveWeights F β) (fun i => a i)-
        MatrixTranslationBounds.weight (primitiveWeights F β) (fun i => b i))+
        N*(ν/scale+Real.log 2/v+(Real.log 4+Real.log (2*(k : ℝ))+ν)/wmin)) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hC : 0 ≤ Real.log (2*(k : ℝ))+ν :=
    add_nonneg (Real.log_nonneg (by linarith)) hν
  have hh := MatrixTranslationBounds.norm_rowScalar_exp_weight_difference
    (centerError F β j)
    (fun i => MatrixTranslationBounds.truncationOrder scale v (primitiveWeights F β i))
    b a d ell (primitiveWeights F β) (Real.log (2*(k : ℝ))+ν) ν N wmin v scale
    hC hν hwmin hv hscale hw ha hell
    (fun i => MatrixTranslationBounds.truncationOrder_pos hscale hv (hwmin.trans_le (hw i)))
    (fun i => MatrixTranslationBounds.truncationOrder_budget hv)
    (actual_center_error_exp F β hβ j k ν hk hj hν happrox)
  simpa only [add_assoc] using hh

end FixedQuadratic.UpstreamAnalysis
#check @FixedQuadratic.UpstreamAnalysis.centerError
#print axioms FixedQuadratic.UpstreamAnalysis.centerError
#check @FixedQuadratic.UpstreamAnalysis.actual_center_error_exp
#print axioms FixedQuadratic.UpstreamAnalysis.actual_center_error_exp
#check @FixedQuadratic.UpstreamAnalysis.actual_rowScalar_exp
#print axioms FixedQuadratic.UpstreamAnalysis.actual_rowScalar_exp
