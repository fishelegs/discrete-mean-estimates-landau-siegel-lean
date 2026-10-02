import ZhangLS.Spec.Proposition141LocalizedGeometry
import ZhangLS.Spec.Proposition141LargeMellinMean

/-! # Actual localized Section14 large-conductor mean

The κ* sequence, χ-conjugate-character prime factor, full complex β disk,
arbitrary modulus congruence filter and all τ₅(D₁),τ₅(d) factors are present.
The support condition is the genuine d h R≤2 D P₄, with its extra D.
-/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141LocalizedWeightedMean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) (D₁ d h:ℕ) (R:ℝ) (Q:Finset ℕ) : ℝ :=
  proposition141WeightedFiniteMean χ β κ D₁ d h (proposition141LocalizedIndices D R h) Q

lemma proposition141_localized_mean_nonneg {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) (D₁ d h:ℕ) (R:ℝ) (Q:Finset ℕ) :
    0≤proposition141LocalizedWeightedMean χ β κ D₁ d h R Q := by
  unfold proposition141LocalizedWeightedMean proposition141WeightedFiniteMean
  exact sum_nonneg (fun _ _=>mul_nonneg (by positivity) (norm_nonneg _))

noncomputable def proposition141LargeMeanSquareConstant : ℝ :=
  30*(32+Real.pi^2)^2*lemma54MellinStripConstant^2*(Real.exp 40)^2*4^25

lemma proposition141_large_mean_square_constant_pos : 0<proposition141LargeMeanSquareConstant := by
  have hC := lemma54_mellin_strip_constant_pos
  unfold proposition141LargeMeanSquareConstant
  positivity

/-- The genuine localized weighted mean-square estimate, before conversion
to a D power saving. Its actual prime mass is retained exactly. -/
theorem proposition141_actual_localized_large_mean_square {D D₁ d h:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (ht:lemma51PaperT0 D≤(D:ℝ)) (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D) {B:ℝ} (hB:0≤B)
    {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) (hD₁:0<D₁) (hd:0<d) (hh:0<h)
    {R:ℝ} (hR:1≤R) (hcut:((d*h:ℕ):ℝ)*R≤2*(D:ℝ)*lemma61PaperP4 D)
    (Q:Finset ℕ) (hQ1:∀r∈Q,1<r) (hQ:∀r∈Q,(r:ℝ)≤2*R) :
    proposition141LocalizedWeightedMean χ β κ D₁ d h R Q^2 ≤
      proposition141LargeMeanSquareConstant*B^2*(lemma34Tau 5 D₁:ℝ)^2*(lemma34Tau 5 d:ℝ)^2*
        (h:ℝ)^2*R^2*(R^2+2*lemma23PaperP D)*lemma23PaperP D*lemma56PrimeMass D*lemma23PaperL D^6625 := by
  have hg := proposition141_localized_geometry hD hL ht hmod hR hd hh hcut
  have hlength := proposition141_localized_length_budget hL hg.1 hg.2.2.1
  let Z := proposition141LocalScale D R h
  let X := ⌊4*Z⌋₊
  let S := proposition141LocalizedIndices D R h
  have hZ : 0<Z := lt_of_lt_of_le (by norm_num) hg.1
  have hX : 1≤X := hlength.1
  have hS : S⊆Icc 1 X := filter_subset _ _
  have hYl : ∀l∈S,Z/3≤(l:ℝ) := fun l hl=>(mem_filter.mp hl).2.1
  have hNX : (X:ℝ)≤4*Z := Nat.floor_le (by positivity)
  have hlog : 0≤1+Real.log (X:ℝ) := by
    have hx := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)
    linarith
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hmass := lemma56_prime_mass_nonneg D
  have hR0 : 0≤R := by linarith
  have hhR : 0<(h:ℝ) := by exact_mod_cast hh
  have hCM := lemma54_mellin_strip_constant_pos
  let Af := (32+Real.pi^2)*(R^2+(X:ℝ))*
    (((B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))^2/(Z/3))*(1+Real.log (X:ℝ))^25)
  let Ag := (32+Real.pi^2)*(R^2+2*lemma23PaperP D)*
    (2*(Real.exp 40)^2*lemma23PaperP D*lemma56PrimeMass D)
  have hAf : 0≤Af := by dsimp [Af]; positivity
  have hAg : 0≤Ag := by dsimp [Ag]; positivity
  have hm := proposition141_actual_weighted_finite_mellin_mean χ hD hL hB
    (show 0<Z/3 by positivity) hR hhR hκ hD₁ hd hX S hS hYl Q hQ1 hQ hβ
  change proposition141LocalizedWeightedMean χ β κ D₁ d h R Q≤
    lemma54MellinStripConstant*lemma23PaperL D^3200*(h:ℝ)*R*Real.sqrt Af*Real.sqrt Ag at hm
  have hs := (sq_le_sq₀ (proposition141_localized_mean_nonneg χ β κ D₁ d h R Q) (by positivity)).mpr hm
  simp only [mul_pow,Real.sq_sqrt hAf,Real.sq_sqrt hAg,←pow_mul] at hs
  have hscale : (R^2+(X:ℝ))/(Z/3)≤15 := by
    apply (div_le_iff₀ (by positivity : 0<Z/3)).mpr
    have hrZ : R^2≤Z := hg.2.1
    linarith
  have hAf1 : Af≤15*(32+Real.pi^2)*B^2*(lemma34Tau 5 D₁:ℝ)^2*(lemma34Tau 5 d:ℝ)^2*
      (1+Real.log (X:ℝ))^25 := by
    have hb := mul_le_mul_of_nonneg_right hscale
      (show 0≤(32+Real.pi^2)*(B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))^2*
        (1+Real.log (X:ℝ))^25 by positivity)
    convert hb using 1 <;> dsimp [Af] <;> ring
  have hAf2 : Af≤15*(32+Real.pi^2)*B^2*(lemma34Tau 5 D₁:ℝ)^2*(lemma34Tau 5 d:ℝ)^2*
      (4^25*lemma23PaperL D^225) := by
    exact hAf1.trans (mul_le_mul_of_nonneg_left hlength.2 (by positivity))
  calc
    _ ≤ lemma54MellinStripConstant^2*lemma23PaperL D^6400*(h:ℝ)^2*R^2*Af*Ag := by
      convert hs using 1
    _ ≤ lemma54MellinStripConstant^2*lemma23PaperL D^6400*(h:ℝ)^2*R^2*
      (15*(32+Real.pi^2)*B^2*(lemma34Tau 5 D₁:ℝ)^2*(lemma34Tau 5 d:ℝ)^2*(4^25*lemma23PaperL D^225))*Ag := by gcongr
    _ = _ := by unfold proposition141LargeMeanSquareConstant; dsimp [Ag]; ring

end ZhangLS.Spec
