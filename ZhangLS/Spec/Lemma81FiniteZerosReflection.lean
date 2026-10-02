import ZhangLS.Spec.Lemma56ActualLocalZeros
import ZhangLS.Spec.Lemma33FirstMean

/-! # Exact finite zeros and contour reflection for Lemma 8.1

This bounded component uses the actual L-function, strict support/window
endpoints, Gaussian weight, inverse character, and oriented segment integral.
It does not assert the full discrete-mean identity.

The paper's undefined tilde on Z̃(ψ) in Lemma 8.1 is interpreted as the
strict L-zero window Z(ψ) defined in (2.14), also used by the applications
on page 44. The higher module will identify the exact local window predicate
with Lemma23InZeroWindow by reflexivity.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Metric Set MeasureTheory MeromorphicOn
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The genuine finite good-character family. -/
noncomputable def lemma81GoodFamily {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Finset (lemma33CharacterIndex D) := by
  classical
  exact (lemma33ActualFamily D).filter (fun ψ => Lemma23GoodPartialSums χ ψ.2)

lemma lemma81_mem_good_family {D : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : lemma33CharacterIndex D) :
    ψ ∈ lemma81GoodFamily χ ↔ Lemma23InPsi1 χ ψ.2 := by
  classical
  rcases ψ with ⟨p,ψ⟩
  simp only [lemma81GoodFamily,Finset.mem_filter,Lemma23InPsi1]
  exact and_congr (lemma33_actual_family_mem p ψ) Iff.rfl

/-- Exactly the original strict (2.14) window; the higher module will identify
this predicate with Lemma23InZeroWindow by reflexivity. -/
def Lemma81InZeroWindow (D : ℕ) (ρ : ℂ) : Prop :=
  |ρ.re - 1 / 2| < 1 / 2 ∧
    |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405

/-- A compact superset used only to enumerate the actual finite zero set. -/
noncomputable def lemma81ZeroContainer (D : ℕ) : Set ℂ :=
  closedBall (lemma23PaperCenter D) (lemma23PaperL D ^ 405 + 1)

noncomputable def lemma81ContainerZeroFinset {p : ℕ} [NeZero p]
    (D : ℕ) (ψ : DirichletCharacter ℂ p) : Finset ℂ :=
  ((divisor ψ.LFunction (lemma81ZeroContainer D)).finiteSupport
    (isCompact_closedBall _ _)).toFinset

/-- Exactly the distinct actual L-zeros in the original strict (2.14) window. -/
noncomputable def lemma81ZeroFinset {p : ℕ} [NeZero p]
    (D : ℕ) (ψ : DirichletCharacter ℂ p) : Finset ℂ := by
  classical
  exact (lemma81ContainerZeroFinset D ψ).filter (Lemma81InZeroWindow D)

lemma lemma81_zero_window_subset_container {D : ℕ} {ρ : ℂ}
    (hρ : Lemma81InZeroWindow D ρ) : ρ ∈ lemma81ZeroContainer D := by
  apply mem_closedBall_iff_norm.mpr
  have hh := Complex.norm_le_abs_re_add_abs_im (ρ - lemma23PaperCenter D)
  change ‖ρ - lemma23PaperCenter D‖ ≤
    |ρ.re - 1 / 2| + |ρ.im - (lemma23PaperCenter D).im| at hh
  linarith only [hh,hρ.1,hρ.2]

lemma lemma81_container_divisor_eq_order {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) {ρ : ℂ}
    (hρ : ρ ∈ lemma81ZeroContainer D) :
    divisor ψ.LFunction (lemma81ZeroContainer D) ρ =
      (analyticOrderNatAt ψ.LFunction ρ : ℤ) := by
  have ha := (lemma56_actual_L_analyticOnNhd ψ hψ).mono
    (subset_univ (lemma81ZeroContainer D))
  rw [ha.divisor_apply hρ, ← Nat.cast_analyticOrderNatAt
    (lemma56_actual_analytic_order_finite ψ hψ ρ)]
  simp

lemma lemma81_mem_container_zero_finset {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) (ρ : ℂ) :
    ρ ∈ lemma81ContainerZeroFinset D ψ ↔
      ρ ∈ lemma81ZeroContainer D ∧ ψ.LFunction ρ = 0 := by
  classical
  let d := divisor ψ.LFunction (lemma81ZeroContainer D)
  have hmem : ρ ∈ lemma81ContainerZeroFinset D ψ ↔ ρ ∈ Function.support d := by
    simp [lemma81ContainerZeroFinset,d]
  rw [hmem]
  constructor
  · intro hsupp
    have hρ := d.supportWithinDomain hsupp
    have hn : analyticOrderNatAt ψ.LFunction ρ ≠ 0 := by
      intro hz
      have hd := lemma81_container_divisor_eq_order ψ hψ hρ
      rw [hz,Nat.cast_zero] at hd
      exact hsupp hd
    exact ⟨hρ,apply_eq_zero_of_analyticOrderNatAt_ne_zero hn⟩
  · rintro ⟨hρ,hzero⟩
    change d ρ ≠ 0
    dsimp [d]
    rw [lemma81_container_divisor_eq_order ψ hψ hρ]
    have hn : analyticOrderNatAt ψ.LFunction ρ ≠ 0 := by
      intro hnat
      have ho : analyticOrderAt ψ.LFunction ρ = 0 := by
        rw [← Nat.cast_analyticOrderNatAt (lemma56_actual_analytic_order_finite ψ hψ ρ),hnat]
        rfl
      exact ((lemma56_actual_L_analyticOnNhd ψ hψ) ρ (mem_univ ρ)).analyticOrderAt_eq_zero.mp ho hzero
    exact_mod_cast hn

/-- Membership proves that no model zeros or product zeros replaced Z(ψ). -/
theorem lemma81_mem_zero_finset {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) (ρ : ℂ) :
    ρ ∈ lemma81ZeroFinset D ψ ↔ Lemma81InZeroWindow D ρ ∧ ψ.LFunction ρ = 0 := by
  classical
  rw [lemma81ZeroFinset,Finset.mem_filter,lemma81_mem_container_zero_finset ψ hψ]
  constructor
  · exact fun h => ⟨h.2,h.1.2⟩
  · exact fun h => ⟨⟨lemma81_zero_window_subset_container h.1,h.2⟩,h.1⟩

noncomputable def lemma81Cutoff (D : ℕ) : ℝ :=
  lemma23PaperP D * lemma56PaperT D ^ (-2 : ℤ)

noncomputable def lemma81PolynomialIndices (D : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌈lemma81Cutoff D⌉₊).filter
    (fun n : ℕ => (n : ℝ) < lemma81Cutoff D)

/-- The explicit uniform coefficient bound and strict support in (7.2). -/
def Lemma81AdmissibleSequence (D : ℕ) (B : ℝ) (a : ℕ → ℂ) : Prop :=
  (∀ n : ℕ, ‖a n‖ ≤ B) ∧
    ∀ n : ℕ, lemma81Cutoff D ≤ (n : ℝ) → a n = 0

noncomputable def lemma81ConjugateSequence (a : ℕ → ℂ) : ℕ → ℂ := fun n => conj (a n)

/-- Exactly A(a;s,ψ), with positive natural indices and strict cutoff. -/
noncomputable def lemma81Polynomial {p : ℕ} (D : ℕ) (a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑ n ∈ lemma81PolynomialIndices D, a n * ψ (n : ZMod p) / (n : ℂ) ^ s

theorem lemma81_conjugate_sequence_admissible {D : ℕ} {B : ℝ} {a : ℕ → ℂ}
    (ha : Lemma81AdmissibleSequence D B a) :
    Lemma81AdmissibleSequence D B (lemma81ConjugateSequence a) := by
  constructor
  · intro n
    simpa only [lemma81ConjugateSequence,Complex.norm_conj] using ha.1 n
  · intro n hn
    simp only [lemma81ConjugateSequence,ha.2 n hn,map_zero]

/-- Termwise conjugation changes the actual character to its inverse. -/
theorem lemma81_polynomial_conjugate {p : ℕ} (D : ℕ) (a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    conj (lemma81Polynomial D a ψ s) =
      lemma81Polynomial D (lemma81ConjugateSequence a) ψ⁻¹ (conj s) := by
  unfold lemma81Polynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hchar : conj (ψ (n : ZMod p)) = ψ⁻¹ (n : ZMod p) :=
    MulChar.star_apply' ψ (n : ZMod p)
  have hpow : conj ((n : ℂ)^s) = (n : ℂ)^(conj s) := by
    have harg : (n : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    simpa only [map_natCast] using (Complex.cpow_conj (n : ℂ) s harg).symm
  simp only [map_div₀,map_mul,hchar,hpow,lemma81ConjugateSequence]

/-- The original ω(s), not a surrogate smoothing kernel. -/
noncomputable def lemma81Omega (D : ℕ) (s : ℂ) : ℂ :=
  ((Real.sqrt Real.pi / lemma23PaperL D ^ 400 : ℝ) : ℂ) *
    Complex.exp ((s - lemma23PaperCenter D)^2 /
      ((4 * (lemma23PaperL D ^ 400)^2 : ℝ) : ℂ))

/-- Reflection in the critical line fixes the center used by ω. -/
lemma lemma81_center_reflection (D : ℕ) :
    1 - conj (lemma23PaperCenter D) = lemma23PaperCenter D := by
  apply Complex.ext <;> simp [lemma23PaperCenter]
  ring

/-- Exact Gaussian reflection, with no asymptotic approximation. -/
theorem lemma81_omega_reflection (D : ℕ) (s : ℂ) :
    lemma81Omega D (1 - conj s) = conj (lemma81Omega D s) := by
  have he : 1 - conj s - lemma23PaperCenter D = -conj (s - lemma23PaperCenter D) := by
    rw [map_sub]
    have hcenter := lemma81_center_reflection D
    linear_combination hcenter
  unfold lemma81Omega
  rw [he,neg_sq,map_mul,Complex.conj_ofReal,← Complex.exp_conj]
  congr 2
  simp only [map_div₀,map_pow,Complex.conj_ofReal]

/-- The actual two-polynomial factor and weight reflect by swapping and
conjugating the coefficient sequences, exactly as on page 43. -/
theorem lemma81_polynomial_weight_reflection {p : ℕ} (D : ℕ)
    (a₁ a₂ : ℕ → ℂ) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    conj (lemma81Polynomial D a₁ ψ s *
      lemma81Polynomial D a₂ ψ⁻¹ (1 - s) * lemma81Omega D s) =
    lemma81Polynomial D (lemma81ConjugateSequence a₂) ψ (1 - conj s) *
      lemma81Polynomial D (lemma81ConjugateSequence a₁) ψ⁻¹ (1 - (1 - conj s)) *
      lemma81Omega D (1 - conj s) := by
  rw [map_mul,map_mul,lemma81_polynomial_conjugate,lemma81_polynomial_conjugate,
    inv_inv,map_sub,map_one,lemma81_omega_reflection,sub_sub_cancel]
  ring

/-- Upward-oriented J(x), parameterized by the original closed height interval. -/
noncomputable def lemma81SegmentPoint (D : ℕ) (x t : ℝ) : ℂ :=
  lemma23PaperCenter D + (x : ℂ) + I * (t : ℂ)

/-- (1/(2πi))∫_{J(x)}f(s)ds; ds=i dt cancels the i in the denominator. -/
noncomputable def lemma81NormalizedSegmentIntegral (D : ℕ) (x : ℝ) (f : ℂ → ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-(lemma23PaperL D ^ 405))..(lemma23PaperL D ^ 405),
      f (lemma81SegmentPoint D x t)


/-- Explicit finiteness for exactly the original actual L-zero set. -/
theorem lemma81_actual_zero_set_finite {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) :
    {ρ : ℂ | Lemma81InZeroWindow D ρ ∧ ψ.LFunction ρ = 0}.Finite := by
  have he : {ρ : ℂ | Lemma81InZeroWindow D ρ ∧ ψ.LFunction ρ = 0} =
      (lemma81ZeroFinset D ψ : Set ℂ) := by
    ext ρ
    exact (lemma81_mem_zero_finset ψ hψ ρ).symm
  rw [he]
  exact (lemma81ZeroFinset D ψ).finite_toSet

lemma lemma81_segment_point_reflection (D : ℕ) (x t : ℝ) :
    1 - conj (lemma81SegmentPoint D x t) = lemma81SegmentPoint D (-x) t := by
  unfold lemma81SegmentPoint
  rw [map_add,map_add,Complex.conj_ofReal,map_mul,Complex.conj_I,Complex.conj_ofReal]
  have hcenter := lemma81_center_reflection D
  push_cast
  linear_combination hcenter

/-- Complex conjugation of the actual parametrized contour includes
reflection across the critical line; this records the orientation exactly. -/
theorem lemma81_normalized_segment_conjugation (D : ℕ) (x : ℝ) (f : ℂ → ℂ) :
    conj (lemma81NormalizedSegmentIntegral D x f) =
      lemma81NormalizedSegmentIntegral D (-x) (fun s => conj (f (1 - conj s))) := by
  unfold lemma81NormalizedSegmentIntegral
  rw [map_mul,map_inv₀,Complex.conj_ofReal]
  congr 1
  have hconj : conj (∫ t in (-(lemma23PaperL D ^ 405))..(lemma23PaperL D ^ 405),
      f (lemma81SegmentPoint D x t)) =
      ∫ t in (-(lemma23PaperL D ^ 405))..(lemma23PaperL D ^ 405),
        conj (f (lemma81SegmentPoint D x t)) := by
    simp only [intervalIntegral,map_sub,integral_conj]
  rw [hconj]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [lemma81_segment_point_reflection,neg_neg]

end ZhangLS.Spec
