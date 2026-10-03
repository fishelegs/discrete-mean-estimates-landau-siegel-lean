import ZhangLS.Spec.Proposition71PrincipalContourErrorIdentity
import ZhangLS.Spec.Proposition71PrincipalFiniteEdges
import ZhangLS.Spec.Proposition71PrincipalRightTails
import ZhangLS.Spec.Proposition71PrincipalBudgetAbsorption
import ZhangLS.Spec.Proposition71PrincipalLocalScales
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical Topology
set_option maxHeartbeats 3500000

/-- An absolute contour constant; no arithmetic index, D, q or c enters it. -/
noncomputable def proposition71PrincipalContourConstant : ℝ :=
  4*lemma54MellinStripConstant*(9*Real.exp 1)^4+
    32*Real.exp (10*Real.pi)*lemma54MellinStripConstant*(9*Real.exp 1)^4+
    1296*Real.exp (10*Real.pi)*lemma54MellinStripConstant

lemma proposition71_principal_contour_constant_pos : 0<proposition71PrincipalContourConstant := by
  have hh := lemma54_mellin_strip_constant_pos
  unfold proposition71PrincipalContourConstant
  positivity

/-- Actual contour error before discharging the c-dependent parameter threshold.
The hypotheses describe source geometry, never a desired mean or contour bound. -/
theorem proposition71_principal_pointwise_at_threshold {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → 2000≤lemma23PaperL D →
      c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 →
      ∀ d m : ℕ, d≠0 → m≠0 → ∀ q : ℝ, 1≤q → lemma56PaperT D^2≤q → q≤lemma23PaperP D^10 →
      ‖proposition71PrincipalDeltaSum D c d m q-proposition71PrincipalResidueSum D c d m q‖≤
        proposition71PrincipalContourConstant*proposition71PrincipalArithmeticBound D d m*q*
          lemma23PaperL D^3244*Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  obtain ⟨NE,hNE,herror⟩ := proposition71_principal_five_edge_error hc
  obtain ⟨NF,hNF,hfinite⟩ := proposition71_principal_finite_edges
  refine ⟨max NE NF,hNE.trans (le_max_left _ _),?_⟩
  intro D hDN hL hsmall d m hd hm q hq1 hqlo hqhi
  have hDE := (le_max_left _ _).trans hDN
  have hDF := (le_max_right _ _).trans hDN
  have hD : 1<D := by omega
  have hq : 0<q := by linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have hH := proposition71_zeta_aux_height_pos D
  have hA := proposition71_principal_arithmetic_bound_nonneg hL d m
  have hCM := lemma54_mellin_strip_constant_pos
  let F := proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
  let a := 1-1/lemma23PaperL D
  let b := 1+lemma44PaperAlpha D
  let H := proposition71ZetaAuxHeight D
  let B := proposition71PrincipalArithmeticBound D d m*q*lemma23PaperL D^3244*
    Real.exp (-(lemma23PaperL D)^(1/10 : ℝ))
  let CL := 4*lemma54MellinStripConstant*(9*Real.exp 1)^4
  let CH := 16*Real.exp (10*Real.pi)*lemma54MellinStripConstant*(9*Real.exp 1)^4
  let CT := 1296*Real.exp (10*Real.pi)*lemma54MellinStripConstant
  have he := herror D hDE hL d m hd hm q hq
  have hf := hfinite D hDF hL c hc hsmall d m hd q hq1
  have ht := proposition71_principal_right_tails hD hL c hd hm hq
  dsimp only at he hf ht
  have hleft : ‖∫t : ℝ in -(H/2)..(H/2),F ((a : ℂ)+(t : ℂ)*I)‖≤CL*B := by
    apply (hf.1.trans (proposition71_principal_left_budget hLp hq
      (show 0≤4*lemma54MellinStripConstant*(9*Real.exp 1)^4*proposition71PrincipalArithmeticBound D d m by positivity)
      hqlo 3244)).trans_eq
    dsimp [CL,B]
    ring
  have hhorizontal (t : ℝ) (ht : |t|=H/2) :
      ‖∫σ : ℝ in a..b,F ((σ : ℂ)+(t : ℂ)*I)‖≤CH*B := by
    apply ((hf.2 t ht).trans (proposition71_principal_horizontal_budget hLp hq
      (show 0≤16*lemma54MellinStripConstant*(9*Real.exp 1)^4*proposition71PrincipalArithmeticBound D d m by positivity)
      hqhi 3244)).trans_eq
    dsimp [CH,B]
    ring
  have hhalf : 0<H/2 := div_pos hH (by norm_num)
  have hbottom := hhorizontal (-(H/2)) (by rw [abs_neg,abs_of_pos hhalf])
  have htop := hhorizontal (H/2) (abs_of_pos hhalf)
  have htails : ‖∫t : ℝ in Iic (-(H/2)),F ((b : ℂ)+(t : ℂ)*I)‖+
      ‖∫t : ℝ in Ioi (H/2),F ((b : ℂ)+(t : ℂ)*I)‖≤CT*B := by
    apply (ht.trans (proposition71_principal_tail_budget (by linarith) hq
      (show 0≤1296*lemma54MellinStripConstant*proposition71PrincipalArithmeticBound D d m by positivity)
      hqhi (by norm_num : 3236≤3244))).trans_eq
    dsimp [CT,B]
    ring
  calc
    _≤‖∫t : ℝ in -(H/2)..(H/2),F ((a : ℂ)+(t : ℂ)*I)‖+
      ‖∫σ : ℝ in a..b,F ((σ : ℂ)+((-(H/2) : ℝ) : ℂ)*I)‖+
      ‖∫σ : ℝ in a..b,F ((σ : ℂ)+((H/2 : ℝ) : ℂ)*I)‖+
      ‖∫t : ℝ in Iic (-(H/2)),F ((b : ℂ)+(t : ℂ)*I)‖+
      ‖∫t : ℝ in Ioi (H/2),F ((b : ℂ)+(t : ℂ)*I)‖ := he
    _≤CL*B+CH*B+CH*B+CT*B := by linarith only [hleft,hbottom,htop,htails]
    _=_ := by dsimp [CL,CH,CT,B,proposition71PrincipalContourConstant]; ring

/-- The complete local source contour estimate, retaining all three residues,
q, τ₅(d), both finite-prime factors, and a single absolute error constant. -/
theorem proposition71_actual_principal_pointwise {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ d m : ℕ, d≠0 → m≠0 → ∀ q : ℝ, 1≤q → lemma56PaperT D^2≤q → q≤lemma23PaperP D^10 →
      ‖proposition71PrincipalDeltaSum D c d m q-proposition71PrincipalResidueSum D c d m q‖≤
        proposition71PrincipalContourConstant*proposition71PrincipalArithmeticBound D d m*q*
          lemma23PaperL D^3244*Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  obtain ⟨N,hN,hbound⟩ := proposition71_principal_pointwise_at_threshold hc
  obtain ⟨K,_,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max N (max K ⌈Real.exp 2000⌉₊),hN.trans (le_max_left _ _),?_⟩
  intro D hD d m hd hm q hq1 hqlo hqhi
  have hND := (le_max_left _ _).trans hD
  have hKD := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  exact hbound D hND hL (hsmall D hKD) d m hd hm q hq1 hqlo hqhi

/-- The literal local term of source (7.18)–(7.19), using only original strict
support to prove its q scale. The displayed loss is explicitly nonuniform in d₁. -/
theorem proposition71_original_principal_contour {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ p d₁ d₂ k l₂ : ℕ,
      p∈lemma56PaperPrimes D → 0<d₁ → 0<d₂ → 0<k → 0<l₂ →
      d₂*l₂∈lemma81PolynomialIndices D → d₁*d₂*k∈lemma81PolynomialIndices D →
      ‖(∑' n : Proposition71CoprimeIndex (d₂*k),
        lemma83Kappa (lemma83PaperBeta D c) (d₁*n.val)*
          lemma53PaperDelta D ((n.val : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ))))-
        (∑j : Fin 3, proposition71ActualR D c j*
          lemma83ModifiedKappa (lemma83PaperBeta D c) d₁ (d₂*k) (1-lemma83PaperBeta D c j)*
          lemma83Lambda (lemma83PaperBeta D c) (d₁*d₂*k) (1-lemma83PaperBeta D c j)*
          (((p : ℝ)*(k : ℝ)/(l₂ : ℝ) : ℝ) : ℂ)^(1-lemma83PaperBeta D c j))‖≤
        proposition71PrincipalContourConstant*(lemma34Tau 5 d₁ : ℝ)*
          proposition71KappaEulerEnvelope d₁ (1-1/lemma23PaperL D)*
          proposition71LambdaEulerEnvelope (d₁*d₂*k) (1-1/lemma23PaperL D)*
          ((p : ℝ)*(k : ℝ)/(l₂ : ℝ))*lemma23PaperL D^3244*
          Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  obtain ⟨N,hN,hbound⟩ := proposition71_actual_principal_pointwise hc
  refine ⟨max N ⌈Real.exp 2000⌉₊,hN.trans (le_max_left _ _),?_⟩
  intro D hD p d₁ d₂ k l₂ hp hd₁ hd₂ hk hl₂ hs₂ hsk
  have hND := (le_max_left _ _).trans hD
  have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hD)
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  have hsc := proposition71_principal_local_scales (by linarith : 3≤lemma23PaperL D)
    hp hd₁ hd₂ hk hl₂ hs₂ hsk
  have hb := hbound D hND d₁ (d₂*k) hd₁.ne' (Nat.mul_pos hd₂ hk).ne'
    ((p : ℝ)*(k : ℝ)/(l₂ : ℝ)) hsc.2.2.1 hsc.2.2.2.2.le hsc.2.2.2.1
  have ha (n : ℕ) : (n : ℝ)/((p : ℝ)*(k : ℝ)/(l₂ : ℝ))=
      (n : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ)) := by
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  simpa only [proposition71PrincipalDeltaSum,proposition71PrincipalResidueSum,
    proposition71PrincipalArithmeticBound,ha,Nat.mul_assoc,mul_assoc] using hb

end ZhangLS.Spec
