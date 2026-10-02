import ZhangLS.Spec.Lemma32ProductDifference
import Mathlib.Topology.MetricSpace.Cauchy
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_regular_products_uniform_cauchy {D : ℕ} (χ : RealPrimitiveCharacter D)
    (σ : ℝ) (hσ : 1/2 < σ) :
    UniformCauchySeqOn
      (fun S : Finset Nat.Primes => fun s : ℂ =>
        ∏ p ∈ S, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s))
      atTop {s : ℂ | σ ≤ s.re} := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let b (x : ℝ) := lemma32RegularProductBound σ*(Real.exp (7659*x)-1)
  have hb : ContinuousAt b 0 := by dsimp [b]; fun_prop
  have hb0 : b 0 = 0 := by simp [b]
  have hu : {x : ℝ | b x < ε/2} ∈ 𝓝 0 := by
    change b ⁻¹' Set.Iio (ε/2) ∈ 𝓝 0
    apply hb.preimage_mem_nhds
    change Set.Iio (ε/2) ∈ 𝓝 (b 0)
    rw [hb0]
    exact Iio_mem_nhds (by linarith)
  have hn : Summable (fun n : ℕ => (n : ℝ)^(-2*σ)) := Real.summable_nat_rpow.mpr (by linarith)
  have hp : Summable (fun p : Nat.Primes => (p.val : ℝ)^(-2*σ)) := hn.subtype _
  obtain ⟨S₀,hS₀⟩ := hp.vanishing hu
  refine ⟨S₀,?_⟩
  intro S hS T hT s hs
  have hdS : Disjoint ((S∪T)\S) S₀ := Finset.disjoint_left.mpr (by
    intro p hp hp0
    exact (Finset.mem_sdiff.mp hp).2 (hS hp0))
  have hdT : Disjoint ((S∪T)\T) S₀ := Finset.disjoint_left.mpr (by
    intro p hp hp0
    exact (Finset.mem_sdiff.mp hp).2 (hT hp0))
  have hbS := hS₀ ((S∪T)\S) hdS
  have hbT := hS₀ ((S∪T)\T) hdT
  have hhS := (lemma32_regular_finite_product_difference χ σ hσ s hs S (S∪T)
    Finset.subset_union_left).trans_lt hbS
  have hhT := (lemma32_regular_finite_product_difference χ σ hσ s hs T (S∪T)
    Finset.subset_union_right).trans_lt hbT
  rw [← dist_eq_norm_sub] at hhS hhT
  have htri := dist_triangle
    (∏ p ∈ S, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s))
    (∏ p ∈ S∪T, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s))
    (∏ p ∈ T, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s))
  rw [dist_comm] at hhS
  linarith

lemma lemma32_regular_products_uniform_limit {D : ℕ} (χ : RealPrimitiveCharacter D)
    (σ : ℝ) (hσ : 1/2 < σ) :
    TendstoUniformlyOn
      (fun S : Finset Nat.Primes => fun s : ℂ =>
        ∏ p ∈ S, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s))
      (lemma32RegularEulerProduct χ) atTop {s : ℂ | σ ≤ s.re} := by
  apply (lemma32_regular_products_uniform_cauchy χ σ hσ).tendstoUniformlyOn_of_tendsto
  intro s hs
  change σ ≤ s.re at hs
  exact (lemma32_regular_euler_product_multipliable χ s (by linarith [hs])).hasProd

end ZhangLS.Spec
