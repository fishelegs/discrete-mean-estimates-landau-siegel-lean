import ZhangLS.Spec.Lemma32QuarticCubicSums
import ZhangLS.Spec.Lemma32MonicCubicNormalization
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_quadratic_normalized_cubic_sum_identity {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hq : χ^2=1) (a b c d : F)
    (hA : lemma32CubicLeadingCoefficient a b c d ≠ 0) :
    (∑ u : F, χ (lemma32TransformedCubic a b c d u)) =
      ∑ X : F, χ (lemma32NormalizedMonicCubic a b c d X) := by
  exact Fintype.sum_bijective (fun u => lemma32CubicLeadingCoefficient a b c d*u)
    (mulLeft_bijective₀ _ hA) _ _
    (fun u => (lemma32_quadratic_monic_cubic_point_identity χ hq a b c d u hA).symm)

lemma lemma32_quadratic_quartic_normalized_cubic_sum_identity {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hq : χ^2=1) (a b c d : F)
    (hA : lemma32CubicLeadingCoefficient a b c d ≠ 0) :
    (∑ x : F, χ (lemma32QuarticRootProduct a b c d x)) =
      (∑ X : F, χ (lemma32NormalizedMonicCubic a b c d X))-1 := by
  rw [lemma32_quadratic_quartic_cubic_sum_identity χ hq,
    lemma32_quadratic_normalized_cubic_sum_identity χ hq a b c d hA]

end ZhangLS.Spec
