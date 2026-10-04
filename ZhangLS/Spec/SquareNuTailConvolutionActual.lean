import ZhangLS.Spec.SquareNuTailConvolution
import ZhangLS.Spec.SquareNuTailConvolutionSquare
import ZhangLS.Spec.SquareNuTailLinear

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Filter
open scoped Topology

lemma squareNu_actual_tail_eq_floor {D : ℕ} (χ : RealPrimitiveCharacter D) (N : ℕ) :
    squareNuHarmonicTail (squareNu χ) ((D:ℝ)^(21/20:ℝ)) N =
      ∑ n ∈ Ioc ⌊(D:ℝ)^(21/20:ℝ)⌋₊ N, lemma31NuReal χ n * (n:ℝ)⁻¹ := by
  have hs : (Icc 1 N).filter (fun n : ℕ => (D:ℝ)^(21/20:ℝ) < n) =
      Ioc ⌊(D:ℝ)^(21/20:ℝ)⌋₊ N := by
    ext n
    simp only [mem_filter, mem_Icc, mem_Ioc]
    rw [← squareNuTailLinear_strict_floor]
    omega
  unfold squareNuHarmonicTail
  rw [hs]
  rfl

/-- Explicit finite convolution bound with the actual character and original assumption (A). -/
theorem squareNu_actual_convolution_explicit {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (q N : ℕ) (hq : 1 ≤ q) (hq9 : q ≤ 9) (hNP : (N:ℝ) ≤ lemma23PaperP D^4) :
    squareNuHarmonicTail (squareNu χ^(2*q)*squareTau (q*q-2*q)) ((D:ℝ)^20) N ≤
      (2*q:ℕ)*(5*lemma23PaperL D^(-2013:ℤ)+36*(D:ℝ)^(-1/40:ℝ))*
        (32*lemma23PaperL D^2)^(2*q-1)*squareTauMomentConstant (q*q-2*q) +
      (32*lemma23PaperL D^2)^(2*q)*
        ((D:ℝ)^(-1/4:ℝ)*squareTauMomentConstant (q*q-2*q)) := by
  apply squareNu_square_assembly_le _ _ (squareNu_nonneg χ) (squareTau_nonneg _)
    (D:ℝ) (by exact_mod_cast hD.le) (2*q) N (by omega) (by omega)
  · positivity
  · positivity
  · exact squareTauMomentConstant_nonneg _
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg D) _) (squareTauMomentConstant_nonneg _)
  · exact squareNuTailLinear_mass_le χ hD hL hA N hNP
  · rw [squareNu_actual_tail_eq_floor]
    exact squareNuTailLinear_actual_le χ hD hL hA N hNP
  · exact squareTau_harmonic_le_moment _ N
  · simpa only [squareNuHarmonicTail,div_eq_mul_inv,neg_mul] using
      squareTau_strict_tail_le_moment (q*q-2*q) (D:ℝ) (by exact_mod_cast hD.le) N

lemma squareNu_square_exponential_absorption_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      1 < D ∧ 1 ≤ lemma23PaperL D ∧
        (D : ℝ)^(-1/4:ℝ) ≤ lemma23PaperL D^(-2015:ℤ) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hf : Tendsto (fun D : ℕ => lemma23PaperL D^2015 *
      Real.exp (-(1/4:ℝ)*lemma23PaperL D)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat, Function.comp_apply] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2015:ℝ) (1/4)
        (by norm_num)).comp ht
  have he : ∀ᶠ D : ℕ in atTop, 1 < D ∧ 1 ≤ lemma23PaperL D ∧
      (D:ℝ)^(-1/4:ℝ) ≤ lemma23PaperL D^(-2015:ℤ) := by
    filter_upwards [hf.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
      ht.eventually (eventually_ge_atTop 1), eventually_ge_atTop (2:ℕ)]
      with D hsmall hL hD
    refine ⟨by omega,hL,?_⟩
    have hl : 0 < lemma23PaperL D := by linarith
    have hd : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
    have hexp : (D:ℝ)^(-1/4:ℝ) = Real.exp (-(1/4:ℝ)*lemma23PaperL D) := by
      rw [Real.rpow_def_of_pos hd]
      congr 1
      unfold lemma23PaperL
      ring
    rw [hexp]
    simp only [zpow_neg,zpow_ofNat]
    rw [← one_mul ((lemma23PaperL D^2015)⁻¹)]
    apply (le_mul_inv_iff₀ (pow_pos hl 2015)).mpr
    simpa only [mul_comm] using hsmall.le
  exact eventually_atTop.mp he

lemma squareNu_main_scale (L : ℝ) (hL : 0 < L) (r : ℕ) (hr : 1 ≤ r) :
    L^(-2013:ℤ)*(L^2)^(r-1) = L^((2*r:ℕ)-2015:ℤ) := by
  rw [← pow_mul]
  have he : (-2013:ℤ)+(2*(r-1):ℕ) = (2*r:ℕ)-2015 := by omega
  simpa only [he,zpow_natCast] using
    (zpow_add₀ hL.ne' (-2013:ℤ) (2*(r-1):ℕ)).symm

lemma squareNu_square_scale (L : ℝ) (hL : 0 < L) (r : ℕ) :
    (L^2)^r * L^(-2015:ℤ) = L^((2*r:ℕ)-2015:ℤ) := by
  rw [← pow_mul]
  simpa only [sub_eq_add_neg,zpow_natCast] using
    (zpow_add₀ hL.ne' (2*r:ℕ) (-2015:ℤ)).symm

noncomputable def squareNuTailConstant (q : ℕ) : ℝ :=
  ((2*q:ℕ)*41*32^(2*q-1)+32^(2*q))*squareTauMomentConstant (q*q-2*q)

lemma squareNuTailConstant_nonneg (q : ℕ) : 0 ≤ squareNuTailConstant q := by
  unfold squareNuTailConstant
  exact mul_nonneg (by positivity) (squareTauMomentConstant_nonneg _)

/-- Uniform threshold precedes q, the actual character, and the finite endpoint. -/
theorem squareNu_actual_convolution_uniform :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ q : ℕ, 1 ≤ q → q ≤ 9 → ∀ N : ℕ,
      (N:ℝ) ≤ lemma23PaperP D^4 →
      squareNuHarmonicTail (squareNu χ^(2*q)*squareTau (q*q-2*q)) ((D:ℝ)^20) N ≤
        squareNuTailConstant q * lemma23PaperL D^((4*q:ℕ)-2015:ℤ) := by
  obtain ⟨D₁,hD₁,hlinear⟩ := squareNuTailLinear_uniform_inputs
  obtain ⟨D₂,hsquare⟩ := squareNu_square_exponential_absorption_threshold
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D hD χ hA q hq hq9 N hNP
  obtain ⟨hL,hin⟩ := hlinear D ((le_max_left _ _).trans hD)
  obtain ⟨hd,hl,hs⟩ := hsquare D ((le_max_right _ _).trans hD)
  obtain ⟨hT,hH⟩ := hin χ hA N hNP
  have hLp : 0 < lemma23PaperL D := by linarith
  have hbound := squareNu_square_assembly_le (squareNu χ) (squareTau (q*q-2*q))
    (squareNu_nonneg χ) (squareTau_nonneg _) (D:ℝ) (by exact_mod_cast hd.le)
    (2*q) N (by omega) (by omega) (32*lemma23PaperL D^2)
    (41*lemma23PaperL D^(-2013:ℤ)) (squareTauMomentConstant (q*q-2*q))
    (lemma23PaperL D^(-2015:ℤ)*squareTauMomentConstant (q*q-2*q))
    (by positivity) (by positivity) (squareTauMomentConstant_nonneg _)
    (mul_nonneg (zpow_pos hLp _).le (squareTauMomentConstant_nonneg _)) hH
    (by rw [squareNu_actual_tail_eq_floor]; exact hT)
    (squareTau_harmonic_le_moment _ N)
    (by
      have ht := squareTau_strict_tail_le_moment (q*q-2*q) (D:ℝ) (by exact_mod_cast hd.le) N
      simp only [div_eq_mul_inv, neg_mul] at ht hs
      exact ht.trans (mul_le_mul_of_nonneg_right hs (squareTauMomentConstant_nonneg _)))
  calc
    _ ≤ _ := hbound
    _ = squareNuTailConstant q * lemma23PaperL D^((4*q:ℕ)-2015:ℤ) := by
      rw [mul_pow, mul_pow]
      have hm := squareNu_main_scale (lemma23PaperL D) hLp (2*q) (by omega)
      have hs := squareNu_square_scale (lemma23PaperL D) hLp (2*q)
      have he : 2*(2*q)=4*q := by omega
      rw [he] at hm hs
      unfold squareNuTailConstant
      calc
        _ = ((2*q:ℕ)*41*32^(2*q-1)*
              (lemma23PaperL D^(-2013:ℤ)*(lemma23PaperL D^2)^(2*q-1)) +
              32^(2*q)*((lemma23PaperL D^2)^(2*q)*lemma23PaperL D^(-2015:ℤ)))*
                squareTauMomentConstant (q*q-2*q) := by ring
        _ = _ := by rw [hm,hs]; ring

end ZhangLS.Spec
