import ZhangLS.Spec.BFinitePolynomial

/-! The original kernels (2.24), (2.25), (12.1), and their product (12.2).
The coefficient identity is derived from these finite sums, not used to define B. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical ComplexConjugate

noncomputable def bH14Coefficient (D n : ℕ) : ℂ :=
  if (n : ℝ) < (lemma23PaperP D)^(1/2 : ℝ)
  then lemma151Kernel (lemma151P1 D) (lemma151Beta6 D) n else 0

lemma b_kernel_strict_support (X : ℝ) (β : ℂ) :
    BStrictSupport X (lemma151Kernel X β) := by
  intro n hn
  by_contra h
  exact hn (by simp [lemma151Kernel,h])

lemma b_h14_strict_support (D : ℕ) :
    BStrictSupport ((lemma23PaperP D)^(1/2 : ℝ)) (bH14Coefficient D) := by
  intro n hn
  unfold bH14Coefficient at hn
  split_ifs at hn with h
  · exact ⟨(b_kernel_strict_support _ _ n hn).1,h⟩
  · exact (hn rfl).elim

noncomputable def bFirstCutoff (D : ℕ) : ℝ :=
  max ((lemma23PaperP D)^(1/2 : ℝ)) (lemma151P2 D)
noncomputable def bSecondCutoff (D : ℕ) : ℝ :=
  max (lemma151P3 D) (lemma151P2 D)
noncomputable def bProductCutoff (D : ℕ) : ℝ := bFirstCutoff D*bSecondCutoff D

lemma b_first_strict_support (D : ℕ) :
    BStrictSupport (bFirstCutoff D) (lemma151First D) :=
  b_strict_support_add (b_h14_strict_support D)
    (b_strict_support_mul_left (b_kernel_strict_support _ _) (fun _ => lemma151Iota2))

lemma b_second_strict_support (D : ℕ) :
    BStrictSupport (bSecondCutoff D) (lemma151Second D) :=
  b_strict_support_add
    (b_strict_support_mul_left (b_kernel_strict_support _ _) (fun _ => conj lemma151Iota3))
    (b_strict_support_mul_left (b_kernel_strict_support _ _) (fun _ => conj lemma151Iota4))

lemma b_canonical_eq_convolution (D : ℕ) :
    lemma151BChiPsi D = LSeries.convolution (lemma151First D) (lemma151Second D) := by
  funext n
  simp only [LSeries.convolution_def,lemma151BChiPsi]

lemma b_canonical_strict_support (D : ℕ) :
    BStrictSupport (bProductCutoff D) (lemma151BChiPsi D) := by
  rw [b_canonical_eq_convolution]
  exact b_strict_support_convolution (b_first_strict_support D) (b_second_strict_support D)

/-- The entire endpoint and upper half-line vanish; this is stronger than n > cutoff. -/
theorem b_canonical_zero_at_or_above (D n : ℕ) (hn : bProductCutoff D ≤ (n : ℝ)) :
    lemma151BChiPsi D n = 0 := by
  by_contra hne
  exact (not_lt_of_ge hn) ((b_canonical_strict_support D n hne).2)

lemma b_psi_strict_support {D : ℕ} (χ : RealPrimitiveCharacter D) :
    BStrictSupport (bProductCutoff D) (lemma151BPsi χ) :=
  b_strict_support_mul_left (b_canonical_strict_support D) χ.evalNat

/-- The source finite sum: χψ(n)/n^s times the original kernel, with strict n < Y.
For H14, X=P1 and Y=P^(1/2); for H12 and H13, Y=X. -/
noncomputable def bSourceH {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (X : ℝ) (β : ℂ) (Y : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ (Icc 1 ⌈Y⌉₊).filter (fun n : ℕ => (n : ℝ) < Y),
    (χ.evalNat n*ψ (n : ZMod p)/(n : ℂ)^s)*lemma151Kernel X β n

noncomputable def bSourceH14 {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  bSourceH χ ψ (lemma151P1 D) (lemma151Beta6 D) ((lemma23PaperP D)^(1/2 : ℝ)) s
noncomputable def bSourceH12 {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  bSourceH χ ψ (lemma151P2 D) (lemma151Beta7 D) (lemma151P2 D) s
noncomputable def bSourceH13 {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  bSourceH χ ψ (lemma151P3 D) (lemma151Beta6 D) (lemma151P3 D) s
noncomputable def bSourceH2 {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  conj lemma151Iota3*bSourceH13 χ ψ s + conj lemma151Iota4*bSourceH12 χ ψ s

/-- B is defined as the original source product (12.2). -/
noncomputable def bSourceB {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  (bSourceH14 χ ψ s + lemma151Iota2*bSourceH12 χ ψ s)*bSourceH2 χ ψ s

lemma b_source_H_eq_LSeries {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (X : ℝ) (β : ℂ) (Y : ℝ) (s : ℂ) :
    bSourceH χ ψ X β Y s = LSeries (fun n => χ.evalNat n*ψ (n : ZMod p)*
      (if (n : ℝ) < Y then lemma151Kernel X β n else 0)) s := by
  have ha : BStrictSupport Y (fun n => χ.evalNat n*ψ (n : ZMod p)*
      (if (n : ℝ) < Y then lemma151Kernel X β n else 0)) := by
    intro n hn
    have hc := right_ne_zero_of_mul hn
    split_ifs at hc with h
    · exact ⟨(b_kernel_strict_support _ _ n hc).1,h⟩
    · exact (hc rfl).elim
  unfold bSourceH LSeries
  rw [tsum_eq_sum (fun n hn => b_strict_support_term_zero ha s hn),sum_filter]
  apply sum_congr rfl
  intro n hn
  rw [LSeries.term_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp hn).1)]
  split_ifs
  · ring
  · simp only [mul_zero,zero_div]

lemma b_kernel_cut_self (X : ℝ) (β : ℂ) (n : ℕ) :
    (if (n : ℝ) < X then lemma151Kernel X β n else 0) = lemma151Kernel X β n := by
  split_ifs with h
  · rfl
  · simp [lemma151Kernel,h]

lemma b_source_H14_eq_LSeries {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceH14 χ ψ s = LSeries (fun n => χ.evalNat n*ψ (n : ZMod p)*bH14Coefficient D n) s :=
  b_source_H_eq_LSeries χ ψ _ _ _ s

lemma b_source_H12_eq_LSeries {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceH12 χ ψ s = LSeries (fun n => χ.evalNat n*ψ (n : ZMod p)*
      lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) n) s := by
  unfold bSourceH12
  simp only [b_source_H_eq_LSeries,b_kernel_cut_self]

lemma b_source_H13_eq_LSeries {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceH13 χ ψ s = LSeries (fun n => χ.evalNat n*ψ (n : ZMod p)*
      lemma151Kernel (lemma151P3 D) (lemma151Beta6 D) n) s := by
  unfold bSourceH13
  simp only [b_source_H_eq_LSeries,b_kernel_cut_self]

end ZhangLS.Spec
