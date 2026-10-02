import ZhangLS.Spec.Proposition141DoubleMellin
import ZhangLS.Spec.Proposition141WeightedBilinear

/-! # Genuine weighted all-conductor Mellin mean for Section14

The exact finite character sum, actual Mellin integrand, primitive family,
r/φ(r), χ twist and complex β are retained. Both polynomial means come from
the proved sieve, and all finite integral interchanges use proved integrability.
The arbitrary modulus filter Q may retain the original congruence restriction.
-/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical ComplexConjugate

lemma proposition141_double_mellin_norm {D N:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ N) (β:ℂ)
    (κ:ℕ→ℂ) (D₁ d:ℕ) {h r:ℝ} (hh:0<h) (hr:0<r) (S:Finset ℕ) (t:ℝ) :
    ‖proposition141DoubleMellinIntegrand χ θ β κ D₁ d h r S t‖ =
      ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖*(h*r)*
      ‖∑l∈S,(κ (D₁*d*l)/(l:ℂ)^(1+I*(t:ℂ)))*θ (l:ZMod N)‖*
      ‖∑p∈lemma56PaperPrimes D,χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^((1+I*(t:ℂ))+β)‖ := by
  unfold proposition141DoubleMellinIntegrand
  rw [norm_mul,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hh hr)]
  simp

lemma proposition141_delta_line_norm_integrable {D:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) :
    Integrable (fun t:ℝ=>‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖) := by
  have hh := lemma54_eighth_actual_product_integrable hD hL (fun _ : ℝ=>(1:ℂ))
    continuous_const (by norm_num : (0:ℝ)≤1) (by intro t; norm_num)
  simpa only [norm_one,mul_one] using hh

lemma proposition141_delta_line_norm_integral {D:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) :
    (∫t:ℝ,‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖)≤
      lemma54MellinStripConstant*lemma23PaperL D^3200*Real.pi := by
  have hb (t:ℝ) : ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖≤
      (lemma54MellinStripConstant*lemma23PaperL D^3200)*(1+t^2)⁻¹ := by
    have hh := lemma54_actual_mellin_closed_strip_bound hD hL
      (s:=1+I*(t:ℂ)) (by norm_num) (by norm_num)
    have hn : ‖(1:ℂ)+I*(t:ℂ)‖^2=1+t^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp [pow_two]
    simpa only [hn,Real.rpow_ofNat,div_eq_mul_inv] using hh
  have hi := integral_mono_ae (proposition141_delta_line_norm_integrable hD hL)
    (integrable_inv_one_add_sq.const_mul (lemma54MellinStripConstant*lemma23PaperL D^3200))
    (ae_of_all _ hb)
  simpa only [integral_const_mul,integral_univ_inv_one_add_sq] using hi

noncomputable def proposition141PrimitiveModulusPairs (Q:Finset ℕ) :
    Finset (Σr:ℕ,DirichletCharacter ℂ r) :=
  Q.sigma (fun r=>(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive))

noncomputable def proposition141WeightedFiniteMean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) (D₁ d:ℕ) (h:ℝ) (S Q:Finset ℕ) : ℝ :=
  ∑i∈proposition141PrimitiveModulusPairs Q,((i.1:ℝ)/i.1.totient)*
    ‖proposition141FiniteSmallCharacterSum χ i.2 β κ D₁ d h i.1 S‖

/-- Actual weighted finite character mean, with all polynomial moments
proved from the original coefficients and the arbitrary-modulus sieve. -/
theorem proposition141_actual_weighted_finite_mellin_mean {D D₁ d X:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    {B Y R h:ℝ} (hB:0≤B) (hY:0<Y) (hR:1≤R) (hh:0<h)
    {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) (hD₁:0<D₁) (hd:0<d) (hX:1≤X)
    (S:Finset ℕ) (hS:S⊆Icc 1 X) (hYl:∀l∈S,Y≤(l:ℝ))
    (Q:Finset ℕ) (hQ1:∀r∈Q,1<r) (hQ:∀r∈Q,(r:ℝ)≤2*R)
    {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D) :
    proposition141WeightedFiniteMean χ β κ D₁ d h S Q ≤
      lemma54MellinStripConstant*lemma23PaperL D^3200*h*R*
      Real.sqrt ((32+Real.pi^2)*(R^2+(X:ℝ))*
        (((B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))^2/Y)*(1+Real.log (X:ℝ))^25))*
      Real.sqrt ((32+Real.pi^2)*(R^2+2*lemma23PaperP D)*
        (2*(Real.exp 40)^2*lemma23PaperP D*lemma56PrimeMass D)) := by
  let U := proposition141PrimitiveModulusPairs Q
  let w : (Σr:ℕ,DirichletCharacter ℂ r)→ℝ := fun i=>(i.1:ℝ)/i.1.totient
  let F : (Σr:ℕ,DirichletCharacter ℂ r)→ℝ→ℂ := fun i t=>
    proposition141DoubleMellinIntegrand χ i.2 β κ D₁ d h i.1 S t
  let M := Real.sqrt ((32+Real.pi^2)*(R^2+(X:ℝ))*
        (((B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))^2/Y)*(1+Real.log (X:ℝ))^25))*
      Real.sqrt ((32+Real.pi^2)*(R^2+2*lemma23PaperP D)*
        (2*(Real.exp 40)^2*lemma23PaperP D*lemma56PrimeMass D))
  have hM : 0≤M := by dsimp [M]; positivity
  have hR0 : 0≤R := by linarith
  have hw (i:Σr:ℕ,DirichletCharacter ℂ r) : 0≤w i := by dsimp [w]; positivity
  have hmem (i:Σr:ℕ,DirichletCharacter ℂ r) (hi:i∈U) : i.1∈Q := (mem_sigma.mp hi).1
  have hrpos (i:Σr:ℕ,DirichletCharacter ℂ r) (hi:i∈U) : 0<(i.1:ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (hQ1 _ (hmem i hi)))
  have hFi (i:Σr:ℕ,DirichletCharacter ℂ r) (hi:i∈U) : Integrable (F i) :=
    proposition141_double_mellin_integrable χ i.2 hD hL β κ D₁ d hh (hrpos i hi) S
      (fun l hl=>(mem_Icc.mp (hS hl)).1)
  have hsum : Integrable (fun t:ℝ=>∑i∈U,w i*‖F i t‖) :=
    integrable_finsetSum U (fun i hi=>(hFi i hi).norm.const_mul _)
  have hpoint (t:ℝ) : (∑i∈U,w i*‖F i t‖)≤(h*(2*R)*M)*‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖ := by
    have hp := proposition141_actual_weighted_bilinear_mean χ hL hB hY hR hκ hD₁ hd hX S hS hYl
      Q hQ1 hQ (s:=1+I*(t:ℂ)) (by simp) hβ
    change _≤M at hp
    calc
      _ ≤ (h*(2*R)*‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖)*
          (∑i∈U,w i*
            ‖∑l∈S,(κ (D₁*d*l)/(l:ℂ)^(1+I*(t:ℂ)))*i.2 (l:ZMod i.1)‖*
            ‖∑p∈lemma56PaperPrimes D,χ.chi (p:ZMod D)*conj (i.2 (p:ZMod i.1))*(p:ℂ)^((1+I*(t:ℂ))+β)‖) := by
        rw [mul_sum]
        apply sum_le_sum
        intro i hi
        dsimp [F]
        rw [proposition141_double_mellin_norm χ i.2 β κ D₁ d hh (hrpos i hi)]
        have hh' := hQ _ (hmem i hi)
        have hw' := hw i
        calc
          _ ≤ w i*(‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖*(h*(2*R))*
            ‖∑l∈S,(κ (D₁*d*l)/(l:ℂ)^(1+I*(t:ℂ)))*i.2 (l:ZMod i.1)‖*
            ‖∑p∈lemma56PaperPrimes D,χ.chi (p:ZMod D)*conj (i.2 (p:ZMod i.1))*(p:ℂ)^((1+I*(t:ℂ))+β)‖) := by gcongr
          _ = _ := by ring
      _ ≤ (h*(2*R)*‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖)*M := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [U,w,proposition141PrimitiveModulusPairs,sum_sigma,mul_sum,mul_assoc] using hp
      _ = _ := by ring
  have hint := integral_mono_ae hsum
    ((proposition141_delta_line_norm_integrable hD hL).const_mul (h*(2*R)*M)) (ae_of_all _ hpoint)
  rw [integral_const_mul] at hint
  have hint' := hint.trans (mul_le_mul_of_nonneg_left (proposition141_delta_line_norm_integral hD hL)
    (show 0≤h*(2*R)*M by positivity))
  have hnorm (i:Σr:ℕ,DirichletCharacter ℂ r) (hi:i∈U) :
      w i*‖proposition141FiniteSmallCharacterSum χ i.2 β κ D₁ d h i.1 S‖≤
        (1/(2*Real.pi))*∫t:ℝ,w i*‖F i t‖ := by
    rw [proposition141_actual_double_mellin_identity χ i.2 hD hL β κ D₁ d hh (hrpos i hi) S
      (fun l hl=>(mem_Icc.mp (hS hl)).1),norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0<(1/(2*Real.pi):ℝ)),integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm (f:=F i) (μ:=volume))
      (show 0≤w i*(1/(2*Real.pi)) by positivity)
    convert hb using 1 <;> dsimp [F] <;> ring
  unfold proposition141WeightedFiniteMean
  change (∑i∈U,w i*‖proposition141FiniteSmallCharacterSum χ i.2 β κ D₁ d h i.1 S‖)≤_
  calc
    _ ≤ ∑i∈U,(1/(2*Real.pi))*∫t:ℝ,w i*‖F i t‖ := sum_le_sum hnorm
    _ = (1/(2*Real.pi))*∫t:ℝ,∑i∈U,w i*‖F i t‖ := by
      rw [←mul_sum,integral_finsetSum U (fun i hi=>(hFi i hi).norm.const_mul _)]
    _ ≤ (1/(2*Real.pi))*((h*(2*R)*M)*(lemma54MellinStripConstant*lemma23PaperL D^3200*Real.pi)) :=
      mul_le_mul_of_nonneg_left hint' (by positivity)
    _ = _ := by dsimp [M]; field_simp

end ZhangLS.Spec
