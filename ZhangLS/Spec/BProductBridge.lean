import ZhangLS.Spec.BSourceKernels

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical ComplexConjugate

lemma b_LSeries_weighted_linear {X Y : ℝ} {a b : ℕ → ℂ}
    (ha : BStrictSupport X a) (hb : BStrictSupport Y b)
    (w : ℕ → ℂ) (c d s : ℂ) :
    LSeries (fun n => w n*(c*a n+d*b n)) s =
      c*LSeries (fun n => w n*a n) s+d*LSeries (fun n => w n*b n) s := by
  have he : (fun n => w n*(c*a n+d*b n)) =
      c • (fun n => w n*a n)+d • (fun n => w n*b n) := by
    funext n
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,LSeries_add ((b_strict_support_summable (b_strict_support_mul_left ha w) s).smul c)
    ((b_strict_support_summable (b_strict_support_mul_left hb w) s).smul d),
    LSeries_smul,LSeries_smul]

lemma b_source_first_eq_LSeries {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceH14 χ ψ s+lemma151Iota2*bSourceH12 χ ψ s =
      LSeries (fun n => χ.evalNat n*ψ (n : ZMod p)*lemma151First D n) s := by
  rw [b_source_H14_eq_LSeries,b_source_H12_eq_LSeries]
  simpa only [one_mul] using
    (b_LSeries_weighted_linear (b_h14_strict_support D)
      (b_kernel_strict_support (lemma151P2 D) (lemma151Beta7 D))
      (fun n => χ.evalNat n*ψ (n : ZMod p)) 1 lemma151Iota2 s).symm

lemma b_source_second_eq_LSeries {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceH2 χ ψ s =
      LSeries (fun n => χ.evalNat n*ψ (n : ZMod p)*lemma151Second D n) s := by
  rw [bSourceH2,b_source_H12_eq_LSeries,b_source_H13_eq_LSeries]
  exact (b_LSeries_weighted_linear
    (b_kernel_strict_support (lemma151P3 D) (lemma151Beta6 D))
    (b_kernel_strict_support (lemma151P2 D) (lemma151Beta7 D))
    (fun n => χ.evalNat n*ψ (n : ZMod p)) (conj lemma151Iota3) (conj lemma151Iota4) s).symm

/-- Multiplicativity is valid at ramified indices too; it does not require division by χ. -/
lemma b_twisted_product_coefficient {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) :
    LSeries.convolution (fun n => χ.evalNat n*ψ (n : ZMod p)*lemma151First D n)
      (fun n => χ.evalNat n*ψ (n : ZMod p)*lemma151Second D n) =
    (fun n => χ.evalNat n*ψ (n : ZMod p)*lemma151BChiPsi D n) := by
  funext n
  rw [LSeries.convolution_def,lemma151BChiPsi,mul_sum]
  apply sum_congr rfl
  intro a ha
  rw [← (Nat.mem_divisorsAntidiagonal.mp ha).1]
  simp only [RealPrimitiveCharacter.evalNat,Nat.cast_mul,map_mul]
  ring

/-- Exact (12.2)→(15.1) bridge, derived from the original H14/H12/H13 sums. -/
theorem b_source_product_eq_chiPsi_series {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceB χ ψ s =
      LSeries (fun n => χ.evalNat n*ψ (n : ZMod p)*lemma151BChiPsi D n) s := by
  rw [bSourceB,b_source_first_eq_LSeries,b_source_second_eq_LSeries,
    ← LSeries_convolution'
      (b_strict_support_summable (b_strict_support_mul_left (b_first_strict_support D)
        (fun n => χ.evalNat n*ψ (n : ZMod p))) s)
      (b_strict_support_summable (b_strict_support_mul_left (b_second_strict_support D)
        (fun n => χ.evalNat n*ψ (n : ZMod p))) s),
    b_twisted_product_coefficient]

/-- The ψ coefficient is χ b0 everywhere, including its canonical zero at χ(n)=0. -/
theorem b_source_product_eq_psi_series {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceB χ ψ s = LSeries (fun n => ψ (n : ZMod p)*lemma151BPsi χ n) s := by
  rw [b_source_product_eq_chiPsi_series]
  apply LSeries_congr
  intro n _
  unfold lemma151BPsi
  ring

/-- Both displayed coefficient bases evaluate to the same existing finite polynomial. -/
theorem b_source_product_eq_chiPsi_polynomial {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceB χ ψ s = lemma23FiniteDirichletPolynomial ⌈bProductCutoff D⌉₊
      (fun n => χ.evalNat n*ψ (n : ZMod p)*lemma151BChiPsi D n) s := by
  rw [b_source_product_eq_chiPsi_series,
    b_strict_support_LSeries_eq_polynomial (b_strict_support_mul_left
      (b_canonical_strict_support D) (fun n => χ.evalNat n*ψ (n : ZMod p)))]

theorem b_source_product_eq_psi_polynomial {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceB χ ψ s = lemma23FiniteDirichletPolynomial ⌈bProductCutoff D⌉₊
      (fun n => ψ (n : ZMod p)*lemma151BPsi χ n) s := by
  rw [b_source_product_eq_psi_series,
    b_strict_support_LSeries_eq_polynomial (b_strict_support_mul_left
      (b_psi_strict_support χ) (fun n => ψ (n : ZMod p)))]

/-- The untwisted extension is fixed by the source kernel convolution, not by division by χ. -/
theorem b_canonical_four_kernel_expansion (D n : ℕ) :
    lemma151BChiPsi D n = ∑ a ∈ n.divisorsAntidiagonal,
      (bH14Coefficient D a.1 + lemma151Iota2*
        lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) a.1)*
      (conj lemma151Iota3*lemma151Kernel (lemma151P3 D) (lemma151Beta6 D) a.2+
        conj lemma151Iota4*lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) a.2) := rfl

/-- Ramified coefficients are invisible in the χψ display. This is no uniqueness assertion. -/
theorem b_ramified_display_invariance {D p n : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (hχ : χ.evalNat n = 0) (z : ℂ) :
    χ.evalNat n*ψ (n : ZMod p)*(lemma151BChiPsi D n+z) =
      χ.evalNat n*ψ (n : ZMod p)*lemma151BChiPsi D n := by simp [hχ]

theorem b_psi_ramified_zero {D n : ℕ} (χ : RealPrimitiveCharacter D)
    (hχ : χ.evalNat n = 0) : lemma151BPsi χ n = 0 := by simp [lemma151BPsi,hχ]

end ZhangLS.Spec
