import ZhangLS.Spec.ActualGramUniformSubstitution
import ZhangLS.Spec.ActualGramSmoothProfileBinding

/-! The common-threshold theorem for the literal P7 arithmetic residual.
The data package contains only fixed C² profile data, their actual traces,
and global profile bounds. It contains no arithmetic norm hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace ZhangLS.Spec
open Complex Set Finset
open scoped Classical Interval ContDiff

structure ActualGramUniformProfileData where
  f : ℝ → ℂ
  f' : ℝ → ℂ
  f'' : ℝ → ℂ
  g : ℝ → ℂ
  g' : ℝ → ℂ
  g'' : ℝ → ℂ
  b : ℝ
  C : ℝ
  hb0 : 0 ≤ b
  hb : b ≤ 201/400
  hC : 0 ≤ C
  hf : ∀ x, HasDerivAt f (f' x) x
  hf' : ∀ x, HasDerivAt f' (f'' x) x
  hf'' : Continuous f''
  hfz : ∀ v, b ≤ v → f v = 0
  hft : f' b = 0
  hf0 : f 0 = 0
  hfp0 : f' 0 = 0
  hg : ∀ x, HasDerivAt g (g' x) x
  hg' : ∀ x, HasDerivAt g' (g'' x) x
  hg'' : Continuous g''
  hgz : ∀ v, b ≤ v → g v = 0
  hgt : g' b = 0
  hfpz : ∀ v, b ≤ v → f' v = 0
  hfd : ∀ v, ‖actualGramRampDensity (3*I*(Real.pi : ℂ)/2) f f' f'' v‖ ≤ C
  hgd : ∀ v, ‖actualGramRampDensity (-(3*I*(Real.pi : ℂ)/2)) g g' g'' v‖ ≤ C
  hg0 : ∀ v, ‖g v‖ ≤ C
  hg1 : ∀ v, ‖g' v‖ ≤ C

noncomputable def actualGramUniformArithmeticResidual {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (U : ActualGramUniformProfileData) : ℂ :=
  proposition71ArithmeticSum D c j
    (actualGramProfileSequence χ (fun n => U.f (Real.log n/Real.log (lemma23PaperP D))))
    (actualGramProfileSequence χ (fun n => U.g (Real.log n/Real.log (lemma23PaperP D)))) -
    (LDerivAtOne χ^2/(Real.log (lemma23PaperP D) : ℂ)^2)*
      (∑ n ∈ lemma81PolynomialIndices D,
        (‖χ.evalNat n‖ : ℂ)*lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j)/
          (Nat.totient n : ℂ)*actualGramFiniteProfileKernel D c j
            (Real.log (lemma23PaperP D)) U.b U.f U.f' U.g U.g' n)

/-- The four scalar slots of weighted assembly are proved internally at one
threshold. The true harmonic mass is charged only up to exp(B*b). -/
theorem actualGramUniform_assembled_error (c : ℝ) (hc : 0 < c)
    (U : ActualGramUniformProfileData) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ D : ℕ, N ≤ D → 2000 ≤ lemma23PaperL D ∧
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖actualGramUniformArithmeticResidual χ c j U‖ ≤
        (4*lemma84WeightScale (Real.log (lemma23PaperP D))*Real.log (lemma23PaperP D))*
          (actualGramUniformFirstNorm D U.C*actualGramUniformSecondError D U.C+
            actualGramUniformFirstError D U.C*actualGramUniformSecondMain D U.C) := by
  obtain ⟨N,hN,hbounds⟩ := actualGramUniform_four_bounds c hc U.f U.f' U.f''
    U.g U.g' U.g'' U.b U.C U.hb0 U.hb U.hC U.hf U.hf' U.hf'' U.hfz U.hft
    U.hg U.hg' U.hg'' U.hgz U.hgt U.hfd U.hgd U.hg0 U.hg1
  refine ⟨N,hN,?_⟩
  intro D hDN
  obtain ⟨hL,hall⟩ := hbounds D hDN
  refine ⟨hL,?_⟩
  intro χ hA j
  have hD : 1 < D := by omega
  have hB : 0 < Real.log (lemma23PaperP D) := actualGram_original_log_scale_pos hD
  have hB1 : 1 < Real.log (lemma23PaperP D) := by
    rw [lemma23PaperP,Real.log_exp]
    exact one_lt_pow₀ (by linarith : 1 < lemma23PaperL D) (by norm_num)
  have hb1 : U.b ≤ 1 := by linarith [U.hb]
  have hnn := actualGramUniform_envelopes_nonneg (by linarith : 1 ≤ lemma23PaperL D) U.hC
  have hlog (dr : ℕ × ℕ) (hdr : dr ∈ actualGramUniformPairs D (Real.log (lemma23PaperP D)) U.b) :
      Real.log (dr.1*dr.2 : ℕ) ≤ Real.log (lemma23PaperP D) := by
    have hgeom := actualGramUniform_pair_geometry D hB dr hdr
    have hh := (div_le_iff₀ hB).mp hgeom.2.2.2.1
    nlinarith
  have hbound := actualGram_weighted_profile_error_bound χ c j (Real.log (lemma23PaperP D)) U.b
    U.f U.f' U.g U.g' (actualGramUniformPairs D (Real.log (lemma23PaperP D)) U.b)
    ⌊Real.exp (Real.log (lemma23PaperP D)*U.b)⌋₊ (actualGramUniform_pairs_subset D hB)
    hB1 hnn.1 hnn.2.1 hnn.2.2.1 hnn.2.2.2 hlog
    (fun dr hdr => (hall χ hA j dr hdr).1)
    (fun dr hdr => (hall χ hA j dr hdr).2.1)
    (fun dr hdr => (hall χ hA j dr hdr).2.2.1)
    (fun dr hdr => (hall χ hA j dr hdr).2.2.2)
  have hceil := actualGramUniform_support_ceiling (by linarith : 3 ≤ lemma23PaperL D) U.hb
  have hid := actualGram_P7_main_error_supported χ c j (Real.log (lemma23PaperP D)) U.b
    U.f U.f' U.g U.g' hB hceil U.hf0 U.hfp0 U.hfz U.hfpz
  have hraw : ‖actualGramUniformArithmeticResidual χ c j U‖ ≤
      (2*lemma84WeightScale (Real.log (lemma23PaperP D))*
        (harmonic ⌊Real.exp (Real.log (lemma23PaperP D)*U.b)⌋₊ : ℝ))*
      (actualGramUniformFirstNorm D U.C*actualGramUniformSecondError D U.C+
        actualGramUniformFirstError D U.C*actualGramUniformSecondMain D U.C) := by
    unfold actualGramUniformArithmeticResidual
    rw [hid]
    simpa only [actualGramUniformPairs,actualGramProfileProductResidual] using hbound
  apply hraw.trans
  have hh := actualGramUniform_harmonic_bound hB1.le U.hb0 hb1
  have hm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 2*lemma84WeightScale (Real.log (lemma23PaperP D)) by
      exact mul_nonneg (by norm_num) (lemma84_weight_scale_nonneg _))
  have hpoly : 0 ≤ actualGramUniformFirstNorm D U.C*actualGramUniformSecondError D U.C+
      actualGramUniformFirstError D U.C*actualGramUniformSecondMain D U.C :=
    add_nonneg (mul_nonneg hnn.1 hnn.2.2.1) (mul_nonneg hnn.2.1 hnn.2.2.2)
  exact (mul_le_mul_of_nonneg_right hm hpoly).trans_eq (by ring)

/-- Fixed smooth profiles on the original [251/500,201/400] window supply
the C² data and one common D-independent positive profile bound. -/
theorem actualGramUniform_smooth_data (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hsf : tsupport f ⊆ Icc (251/500 : ℝ) (201/400))
    (hsg : tsupport g ⊆ Icc (251/500 : ℝ) (201/400)) :
    ∃ U : ActualGramUniformProfileData,
      U.f = f ∧ U.f' = deriv f ∧ U.g = g ∧ U.g' = deriv g ∧ U.b = 201/400 ∧ 0 < U.C := by
  obtain ⟨Cf,hCf,hfd⟩ := actualGram_smooth_profile_density_bound (3*I*(Real.pi : ℂ)/2) f hf hsf
  obtain ⟨Cg,hCg,hgd⟩ := actualGram_smooth_profile_density_bound (-(3*I*(Real.pi : ℂ)/2)) g hg hsg
  obtain ⟨Cm,hCm,hgm⟩ := actualGram_smooth_profile_global_bound g hg hsg
  have hdf := actualGram_smooth_profile_derivatives f hf hsf
  have hdg := actualGram_smooth_profile_derivatives g hg hsg
  have htf := actualGram_smooth_profile_traces (3*I*(Real.pi : ℂ)/2) f hf hsf
  have htg := actualGram_smooth_profile_traces (-(3*I*(Real.pi : ℂ)/2)) g hg hsg
  let U : ActualGramUniformProfileData := {
    f := f, f' := deriv f, f'' := deriv (deriv f),
    g := g, g' := deriv g, g'' := deriv (deriv g), b := 201/400, C := Cf+Cg+Cm,
    hb0 := by norm_num, hb := le_rfl, hC := by positivity,
    hf := hdf.1, hf' := hdf.2.1, hf'' := hdf.2.2.1,
    hfz := fun v hv => htf.1 v (Or.inr hv), hft := htf.2.1 _ (Or.inr le_rfl),
    hf0 := htf.1 _ (Or.inl (by norm_num)), hfp0 := htf.2.1 _ (Or.inl (by norm_num)),
    hg := hdg.1, hg' := hdg.2.1, hg'' := hdg.2.2.1,
    hgz := fun v hv => htg.1 v (Or.inr hv), hgt := htg.2.1 _ (Or.inr le_rfl),
    hfpz := fun v hv => htf.2.1 v (Or.inr hv),
    hfd := fun v => (hfd v).trans (by linarith),
    hgd := fun v => (hgd v).trans (by linarith),
    hg0 := fun v => by have hh := hgm v; nlinarith [norm_nonneg (deriv g v),norm_nonneg (deriv (deriv g) v)],
    hg1 := fun v => by have hh := hgm v; nlinarith [norm_nonneg (g v),norm_nonneg (deriv (deriv g) v)] }
  exact ⟨U,rfl,rfl,rfl,rfl,rfl,by dsimp [U]; positivity⟩

end ZhangLS.Spec
