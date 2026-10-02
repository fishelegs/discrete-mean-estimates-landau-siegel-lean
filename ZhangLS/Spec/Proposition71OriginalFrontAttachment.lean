import ZhangLS.Spec.Proposition71ActualKappaSeries
import ZhangLS.Spec.Proposition71InfiniteExceptionalContour
import ZhangLS.Spec.Proposition71LargeLArgument

/-! # Exact original Section7 coefficient and short-support attachment

The original C integrand, β₃ phase, κ*a₁ coefficient and strict n<PT⁻²
sequences are identified with the proved common infinite-long contour model.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 3500000
set_option maxRecDepth 4096

lemma proposition71_original_polynomial_eq_cutoff_prefix {D p : ℕ} {B : ℝ}
    (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma81Polynomial D a ψ s=
      lemma81FiniteCharacterPolynomial ⌊lemma81Cutoff D⌋₊ a ψ s := by
  rw [lemma81_finite_character_polynomial_eq_cpow_sum]
  unfold lemma81Polynomial
  have hsub : lemma81PolynomialIndices D⊆Icc 1 ⌊lemma81Cutoff D⌋₊ := by
    intro n hn
    have hh := (proposition71_mem_indices D n).mp hn
    exact mem_Icc.mpr ⟨hh.1,Nat.le_floor hh.2.le⟩
  apply sum_subset hsub
  intro n hn hnot
  have hcut : lemma81Cutoff D≤(n : ℝ) := by
    by_contra hh
    exact hnot ((proposition71_mem_indices D n).mpr ⟨(mem_Icc.mp hn).1,lt_of_not_ge hh⟩)
  simp only [ha.2 n hcut,zero_mul,zero_div]

/-- Equality of the genuine original C kernel and its actual coefficient series. -/
theorem proposition71_actual_C_infinite_kernel {D p : ℕ} [NeZero p]
    {B₁ B₂ : ℝ} (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) (ha₂ : Lemma81AdmissibleSequence D B₂ a₂)
    (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 1<s.re) :
    lemma81CIntegrand D c ψ a₁ a₂ s=
      (-I*(((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)*
        proposition71InfiniteFrontKernel D ψ ψ ⌊lemma81Cutoff D⌋₊
          (fun n => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) n) a₂ s := by
  unfold lemma81CIntegrand proposition71InfiniteFrontKernel
  rw [←proposition71_actual_ratio_convolution ψ c a₁ ha₁ hs,
    ←proposition71_original_polynomial_eq_cutoff_prefix a₂ ha₂ ψ⁻¹ (1-s)]
  unfold lemma81ActualC
  ring

/-- Exact upward J(1) attachment, including the original prime-dependent phase. -/
theorem proposition71_actual_C_contour_eq_infinite {D p : ℕ} [NeZero p]
    {B₁ B₂ : ℝ} (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) (ha₂ : Lemma81AdmissibleSequence D B₂ a₂)
    (ψ : DirichletCharacter ℂ p) :
    lemma81NormalizedSegmentIntegral D 1 (lemma81CIntegrand D c ψ a₁ a₂)=
      (-I*(((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)*
        lemma81NormalizedSegmentIntegral D 1
          (proposition71InfiniteFrontKernel D ψ ψ ⌊lemma81Cutoff D⌋₊
            (fun n => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) n) a₂) := by
  have hp (t : ℝ) := proposition71_actual_C_infinite_kernel c a₁ a₂ ha₁ ha₂ ψ
    (s := lemma81SegmentPoint D 1 t) (by norm_num [lemma81SegmentPoint,lemma23PaperCenter])
  unfold lemma81NormalizedSegmentIntegral
  simp_rw [hp]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The true support is sufficiently short for the literal m≥P² Δ₁ tail;
no restriction is silently imposed on its long index. -/
theorem proposition71_original_short_support_geometry :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      3≤lemma23PaperL D ∧ ⌊lemma81Cutoff D⌋₊≤⌊lemma23PaperP D⌋₊ ∧
      ∀ p∈lemma56PaperPrimes D,
        (p : ℝ)≤2*lemma23PaperP D^2 ∧
        ∀n∈Icc 1 ⌊lemma81Cutoff D⌋₊,
          ((p : ℝ)*(n : ℝ))*lemma51PaperT0 D^(51/50 : ℝ)<lemma23PaperP D^2 := by
  obtain ⟨D₀,hD₀,hgeo⟩ := proposition71_uniform_large_l_geometry
  refine ⟨D₀,hD₀,?_⟩
  intro D hD
  obtain ⟨hL,hT0,hTinv⟩ := hgeo D hD
  have hLp : 0< lemma23PaperL D := by linarith
  have hDpos : 0<D := by omega
  have hDp : 0<(D : ℝ) := by exact_mod_cast hDpos
  have hP : 0< lemma23PaperP D := Real.exp_pos _
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp (pow_nonneg hLp.le _)
  have hcut0 : 0≤lemma81Cutoff D := by unfold lemma81Cutoff lemma56PaperT lemma23PaperP; positivity
  have hcut : lemma81Cutoff D≤lemma23PaperP D/(D : ℝ) := by
    unfold lemma81Cutoff
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hTinv hP.le
  refine ⟨hL,Nat.floor_mono (lemma81_cutoff_le_P hL),?_⟩
  intro p hp
  have hpP : (p : ℝ)≤2*lemma23PaperP D :=
    (proposition71_paper_prime_le_three_halves_P hL hp).trans (by nlinarith only [hP.le])
  have hpp : 0<(p : ℝ) := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.pos
  refine ⟨hpP.trans (by nlinarith only [hP1]),?_⟩
  intro n hn
  have hnp : 0<(n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
  have hncut : (n : ℝ)≤lemma81Cutoff D :=
    (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ)≤⌊lemma81Cutoff D⌋₊).trans (Nat.floor_le hcut0)
  have hpn : (p : ℝ)*(n : ℝ)≤2*lemma23PaperP D^2/(D : ℝ) := by
    exact (mul_le_mul hpP (hncut.trans hcut) hnp.le (by positivity)).trans_eq (by ring)
  calc
    _≤(2*lemma23PaperP D^2/(D : ℝ))*((D : ℝ)/4) :=
      mul_le_mul hpn hT0 (Real.rpow_nonneg (pow_nonneg hLp.le _) _) (by positivity)
    _=lemma23PaperP D^2/2 := by field_simp; ring
    _<_ := by nlinarith only [sq_pos_of_pos hP]

end ZhangLS.Spec
