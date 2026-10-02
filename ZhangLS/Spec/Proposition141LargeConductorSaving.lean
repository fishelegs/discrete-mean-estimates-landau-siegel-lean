import ZhangLS.Spec.Proposition141LocalizedLargeMean
import ZhangLS.Spec.Proposition71CharacterConductorWeights

/-! # Original D³ split gives a genuine Section14 large-conductor saving

The actual support d h R≤2 D P₄ and T≥D⁴ imply D³(R²+2P)≤4RP.
Combining the proved χ-twisted/complex-β mean with the actual prime-mass
lower bound retains every divisor factor and gives an explicit D^(-3/2)
normalized dyadic saving, before the extra exterior D weight.
-/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition141_large_conductor_geometric_budget {D d h:ℕ}
    (hD:1<D) (ht:lemma51PaperT0 D≤(D:ℝ)) (hT:(D:ℝ)^4≤lemma56PaperT D)
    {R:ℝ} (hR:(D:ℝ)^3≤R) (hd:0<d) (hh:0<h)
    (hcut:((d*h:ℕ):ℝ)*R≤2*(D:ℝ)*lemma61PaperP4 D) :
    (D:ℝ)^3*(R^2+2*lemma23PaperP D)≤4*R*lemma23PaperP D := by
  have hD1 : 1≤(D:ℝ) := by exact_mod_cast (by omega : 1≤D)
  have hDp : 0<(D:ℝ) := by exact_mod_cast (by omega : 0<D)
  have hRp : 0<R := (pow_pos hDp 3).trans_le hR
  have hdh : 1≤((d*h:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos hd hh
  have hRu : R≤2*(D:ℝ)*lemma61PaperP4 D := by
    have hb := mul_le_mul_of_nonneg_right hdh hRp.le
    have hle : R≤((d*h:ℕ):ℝ)*R := by simpa only [one_mul] using hb
    exact hle.trans hcut
  have hT2 : (D:ℝ)^4*lemma51PaperT0 D≤lemma56PaperT D^2 := by
    calc
      _≤(D:ℝ)^4*(D:ℝ) := mul_le_mul_of_nonneg_left ht (by positivity)
      _=(D:ℝ)^5 := by ring
      _≤(D:ℝ)^8 := pow_le_pow_right₀ hD1 (by norm_num)
      _=((D:ℝ)^4)^2 := by ring
      _≤_ := pow_le_pow_left₀ (by positivity) hT 2
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hTpos : 0<lemma56PaperT D^2 := sq_pos_of_pos (Real.exp_pos _)
  have hP4 : (D:ℝ)^4*lemma61PaperP4 D≤lemma23PaperP D := by
    apply (mul_le_mul_iff_left₀ hTpos).mp
    calc
      ((D:ℝ)^4*lemma61PaperP4 D)*lemma56PaperT D^2 =
        lemma23PaperP D*((D:ℝ)^4*lemma51PaperT0 D) := by
          rw [mul_assoc,lemma61_complementary_scales]; ring
      _≤lemma23PaperP D*lemma56PaperT D^2 := mul_le_mul_of_nonneg_left hT2 hP
  have hD3R : (D:ℝ)^3*R≤2*lemma23PaperP D := by
    have hb := mul_le_mul_of_nonneg_left hRu (show 0≤(D:ℝ)^3 by positivity)
    calc
      _≤(D:ℝ)^3*(2*(D:ℝ)*lemma61PaperP4 D) := hb
      _=2*((D:ℝ)^4*lemma61PaperP4 D) := by ring
      _≤_ := mul_le_mul_of_nonneg_left hP4 (by norm_num)
  have h1 := mul_le_mul_of_nonneg_right hD3R hRp.le
  have h2 := mul_le_mul_of_nonneg_right hR (mul_nonneg (by norm_num : (0:ℝ)≤2) hP)
  nlinarith only [h1,h2]

noncomputable def proposition141LargeMeanConstant : ℝ :=
  4*Real.sqrt proposition141LargeMeanSquareConstant

lemma proposition141_large_mean_constant_pos : 0<proposition141LargeMeanConstant :=
  mul_pos (by norm_num) (Real.sqrt_pos.mpr proposition141_large_mean_square_constant_pos)

/-- Quantitative saving with the actual mass lower bound as a separate,
already proved arithmetic input. Neither moment nor cancellation is assumed. -/
theorem proposition141_actual_localized_large_mean_saving {D D₁ d h:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (ht:lemma51PaperT0 D≤(D:ℝ)) (hT:(D:ℝ)^4≤lemma56PaperT D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hmass:(1/4:ℝ)*lemma23PaperP D^2/lemma23PaperL D^77≤lemma56PrimeMass D)
    {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D) {B:ℝ} (hB:0≤B)
    {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) (hD₁:0<D₁) (hd:0<d) (hh:0<h)
    {R:ℝ} (hR:(D:ℝ)^3≤R) (hcut:((d*h:ℕ):ℝ)*R≤2*(D:ℝ)*lemma61PaperP4 D)
    (Q:Finset ℕ) (hQ1:∀r∈Q,1<r) (hQ:∀r∈Q,(r:ℝ)≤2*R) :
    proposition141LocalizedWeightedMean χ β κ D₁ d h R Q/R^(3/2:ℝ) ≤
      proposition141LargeMeanConstant*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*(h:ℝ)*
        lemma56PrimeMass D*lemma23PaperL D^3351/(D:ℝ)^(3/2:ℝ) := by
  have hD1 : 1≤(D:ℝ) := by exact_mod_cast (by omega : 1≤D)
  have hDp : 0<(D:ℝ) := by exact_mod_cast (by omega : 0<D)
  have hR1 : 1≤R := (one_le_pow₀ hD1 : 1≤(D:ℝ)^3).trans hR
  have hRp : 0<R := by linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hM := lemma56_prime_mass_nonneg D
  have hC := proposition141_large_mean_square_constant_pos.le
  have hCM := proposition141_large_mean_constant_pos.le
  have hW := proposition141_localized_mean_nonneg χ β κ D₁ d h R Q
  have hs := proposition141_actual_localized_large_mean_square χ hD hL ht hmod hβ hB hκ hD₁ hd hh hR1 hcut Q hQ1 hQ
  have hg := proposition141_large_conductor_geometric_budget hD ht hT hR hd hh hcut
  have hmass' : lemma23PaperP D^2≤4*lemma23PaperL D^77*lemma56PrimeMass D := by
    have hb := (div_le_iff₀ (pow_pos hLp 77)).mp hmass
    nlinarith only [hb]
  let A := proposition141LargeMeanSquareConstant*B^2*(lemma34Tau 5 D₁:ℝ)^2*(lemma34Tau 5 d:ℝ)^2*(h:ℝ)^2
  have hA : 0≤A := by dsimp [A]; positivity
  have hsD : proposition141LocalizedWeightedMean χ β κ D₁ d h R Q^2*(D:ℝ)^3 ≤
      16*A*R^3*(lemma56PrimeMass D)^2*lemma23PaperL D^6702 := by
    calc
      _ ≤ (A*R^2*(R^2+2*lemma23PaperP D)*lemma23PaperP D*lemma56PrimeMass D*lemma23PaperL D^6625)*(D:ℝ)^3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [A] using hs
      _ = (A*R^2*lemma23PaperP D*lemma56PrimeMass D*lemma23PaperL D^6625)*
          ((D:ℝ)^3*(R^2+2*lemma23PaperP D)) := by ring
      _ ≤ (A*R^2*lemma23PaperP D*lemma56PrimeMass D*lemma23PaperL D^6625)*(4*R*lemma23PaperP D) := by gcongr
      _ = (4*A*R^3*lemma56PrimeMass D*lemma23PaperL D^6625)*lemma23PaperP D^2 := by ring
      _ ≤ (4*A*R^3*lemma56PrimeMass D*lemma23PaperL D^6625)*(4*lemma23PaperL D^77*lemma56PrimeMass D) := by gcongr
      _ = _ := by ring
  rw [proposition71_three_halves_eq_mul_sqrt hRp.le,proposition71_three_halves_eq_mul_sqrt hDp.le]
  apply (div_le_div_iff₀ (mul_pos hRp (Real.sqrt_pos.mpr hRp)) (mul_pos hDp (Real.sqrt_pos.mpr hDp))).mpr
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow,Real.sq_sqrt hDp.le,Real.sq_sqrt hRp.le,proposition141LargeMeanConstant,
    Real.sq_sqrt hC,←pow_mul]
  convert hsD using 1; dsimp [A]; ring

end ZhangLS.Spec
