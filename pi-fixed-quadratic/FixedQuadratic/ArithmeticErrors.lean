import FixedQuadratic.MinorArithmetic

open scoped BigOperators
open Polynomial
namespace FixedQuadratic

noncomputable def formalLcmConstant : ℝ := Real.log 4+4

theorem formalLcmConstant_pos : 0 < formalLcmConstant := by
  have hh : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  dsimp [formalLcmConstant]
  linarith

/-- Uses the actual formal Chebyshev constant log 4+4, without claiming the
paper's sharper 4 log 2. -/
theorem log_logDenominator_le (T : ℕ) :
    Real.log (logDenominator T : ℝ) ≤ formalLcmConstant*T := by
  rw [logDenominator, ← Chebyshev.psi_eq_log_lcmUpto]
  apply (Chebyshev.psi_le_const_mul_self (by positivity)).trans
  apply mul_le_mul_of_nonneg_left _ formalLcmConstant_pos.le
  exact_mod_cast (show T-1 ≤ T by omega)

theorem log_minorDenominator_le {ι : Type*} [Fintype ι] {m : ℕ}
    (T : Fin m → ℕ) (a b : ι → Fin m → ℕ) :
    Real.log (minorDenominator T a b : ℝ) ≤
      formalLcmConstant * ∑ i, (minorDegrees a b i : ℝ)*T i := by
  simp only [minorDenominator, Nat.cast_prod, Nat.cast_pow]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (by exact_mod_cast (logDenominator_pos (T i)).ne'))]
  simp only [Real.log_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hh := mul_le_mul_of_nonneg_left (log_logDenominator_le (T i))
    (show 0 ≤ (minorDegrees a b i : ℝ) by positivity)
  convert hh using 1
  ring

/-- Logarithm of the actual norm replacement keeps both Q costs. -/
theorem logarithmic_norm_product_lower {m : ℕ} (q C : ℝ)
    (R M : Fin m → ℝ) (e : Fin m → ℕ) (z : ℂ)
    (hq : 0 < q) (hC : 0 < C) (hR : ∀ i, 0 < R i) (hM : ∀ i, 0 < M i)
    (hz : z ≠ 0)
    (hprod : (∏ i, (R i)^e i) ≤ q^2*C*(∏ i, (M i)^e i)*‖z‖) :
    -2*Real.log q-Real.log C-(∑ i, (e i : ℝ)*Real.log (M i))+
      (∑ i, (e i : ℝ)*Real.log (R i)) ≤ Real.log ‖z‖ := by
  have hRp : 0 < ∏ i, (R i)^e i := Finset.prod_pos (fun i _ => pow_pos (hR i) _)
  have hMp : 0 < ∏ i, (M i)^e i := Finset.prod_pos (fun i _ => pow_pos (hM i) _)
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hh := Real.log_le_log hRp hprod
  rw [Real.log_mul (mul_pos (mul_pos (sq_pos_of_pos hq) hC) hMp).ne' hn.ne',
    Real.log_mul (mul_pos (sq_pos_of_pos hq) hC).ne' hMp.ne',
    Real.log_mul (sq_pos_of_pos hq).ne' hC.ne', Real.log_pow,
    Real.log_prod (fun i _ => (pow_pos (hR i) _).ne'),
    Real.log_prod (fun i _ => (pow_pos (hM i) _).ne')] at hh
  simp only [Real.log_pow, Nat.cast_ofNat] at hh
  linarith

/-- The actual degree rebate controls the full height cost jointly. -/
theorem joint_height_log_cost {m : ℕ} (e : Fin m → ℕ) (w M : Fin m → ℝ)
    (c budget : ℝ) (hM : ∀ i, Real.log (M i) ≤ w i+c)
    (hbudget : ∑ i, w i*(e i : ℝ) ≤ budget) :
    (∑ i, (e i : ℝ)*Real.log (M i)) ≤ budget+c*∑ i, (e i : ℝ) := by
  calc
    _ ≤ ∑ i, (e i : ℝ)*(w i+c) := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hM i) (by positivity))
    _ = (∑ i, w i*(e i : ℝ))+c*∑ i, (e i : ℝ) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ ≤ _ := add_le_add hbudget (le_refl _)

theorem sum_degrees_le_of_joint_budget {m : ℕ} (e : Fin m → ℕ)
    (w : Fin m → ℝ) (wmin budget : ℝ) (hwmin : 0 < wmin)
    (hw : ∀ i, wmin ≤ w i) (hbudget : ∑ i, w i*(e i : ℝ) ≤ budget) :
    (∑ i, (e i : ℝ)) ≤ budget/wmin := by
  apply (le_div_iff₀ hwmin).mpr
  calc
    _ = ∑ i, wmin*(e i : ℝ) := by rw [Finset.sum_mul]; simp_rw [mul_comm]
    _ ≤ ∑ i, w i*(e i : ℝ) := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_right (hw i) (by positivity))
    _ ≤ _ := hbudget


noncomputable def minorCoefficientEnvelope {ι : Type*} [Fintype ι] {m : ℕ}
    (k : ℕ) (s h : ι → ℕ) (a b : ι → Fin m → ℕ) : ℝ :=
  (Fintype.card ι).factorial * 2^(∑ r, s r) * (3/2)^(∑ c, h c) *
    2^(∑ c, ∑ i, a c i) * (2*k+2)^(∑ i, minorDegrees a b i)

theorem minorCoefficientEnvelope_pos {ι : Type*} [Fintype ι] {m : ℕ}
    (k : ℕ) (s h : ι → ℕ) (a b : ι → Fin m → ℕ) :
    0 < minorCoefficientEnvelope k s h a b := by
  unfold minorCoefficientEnvelope
  positivity

/-- The logarithmic estimate for the actual minor, with no independent norm
or coefficient hypothesis. The tower and true root-pair data remain explicit. -/
theorem formal_minor_fixed_field_log_lower {G K ι : Type*} [Field G] [Field K]
    [NumberField K] [Algebra GaussianInt G] [IsFractionRing GaussianInt G]
    [Algebra G K] [Algebra GaussianInt K] [IsScalarTower GaussianInt G K]
    [FiniteDimensional G K] [IsGalois G K] [Fintype ι] [DecidableEq ι] {m : ℕ}
    (hdegree : Module.finrank G K = 2) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1)
    (T : Fin m → ℕ) (k : ℕ) (j s h : ι → ℕ) (b a : ι → Fin m → ℕ)
    (hj : ∀ r, j r ≤ k) (la lb lc : Fin m → ℤ) (x : Fin m → K)
    (hprim : ∀ i, Int.gcd (Int.gcd (la i) (lb i) : ℤ) (lc i) = 1)
    (hf : ∀ i, C (la i : K)*X^2+C (lb i : K)*X+C (lc i : K) =
      C (la i : K)*((X-C (x i))*(X-C (τ (x i)))))
    (ha : ∀ i, la i ≠ 0) (φ : K →+* ℂ)
    (hφ : φ.comp (algebraMap GaussianInt K) = GaussianInt.toComplex)
    (hne : MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a) ≠ 0) :
    -2*Real.log (minorDenominator T a b : ℝ)-Real.log (minorCoefficientEnvelope k s h a b)-
      (∑ i, (minorDegrees a b i : ℝ)*Real.log
        (‖φ (la i : K)‖*max 1 ‖φ (x i)‖*max 1 ‖φ (τ (x i))‖))+
      (∑ i, (minorDegrees a b i : ℝ)*Real.log (max 1 ‖φ (x i)‖)) ≤
      Real.log ‖MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a)‖ := by
  apply logarithmic_norm_product_lower
    (minorDenominator T a b : ℝ) (minorCoefficientEnvelope k s h a b)
    (fun i => max 1 ‖φ (x i)‖)
    (fun i => ‖φ (la i : K)‖*max 1 ‖φ (x i)‖*max 1 ‖φ (τ (x i))‖)
    (minorDegrees a b) (MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a))
  · exact_mod_cast minorDenominator_pos T a b
  · exact minorCoefficientEnvelope_pos _ _ _ _ _
  · intro i
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro i
    have hc : 0 < ‖φ (la i : K)‖ := norm_pos_iff.mpr ((_root_.map_ne_zero φ).mpr
      (by exact_mod_cast ha i))
    have hR : 0 < max 1 ‖φ (x i)‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hS : 0 < max 1 ‖φ (τ (x i))‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact mul_pos (mul_pos hc hR) hS
  · exact hne
  · exact formal_minor_fixed_field_arithmetic hdegree τ hτ T k j s h b a hj la lb lc x
      hprim hf ha φ hφ hne

/-- Exact logarithm of the coefficient envelope. In particular there is no
log-log height residue hidden in this cost. -/
theorem log_minorCoefficientEnvelope {ι : Type*} [Fintype ι] {m : ℕ}
    (k : ℕ) (s h : ι → ℕ) (a b : ι → Fin m → ℕ) :
    Real.log (minorCoefficientEnvelope k s h a b) =
      Real.log ((Fintype.card ι).factorial : ℝ)+
      (∑ r, s r : ℕ)*Real.log 2+(∑ c, h c : ℕ)*Real.log (3/2)+
      (∑ c, ∑ i, a c i : ℕ)*Real.log 2+
      (∑ i, minorDegrees a b i : ℕ)*Real.log (2*k+2) := by
  unfold minorCoefficientEnvelope
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]

/-- A stronger denominator bound than the coordinatewise paper estimate:
the same joint budget can also be used before summing the truncation costs. -/
theorem log_minorDenominator_le_joint {ι : Type*} [Fintype ι] {m : ℕ}
    (T : Fin m → ℕ) (a b : ι → Fin m → ℕ) (w : Fin m → ℝ)
    (F v wmin D : ℝ) (hF : 0 ≤ F) (hv : 0 < v) (hwmin : 0 < wmin)
    (hw : ∀ i, wmin ≤ w i) (hT : ∀ i, (T i : ℝ) ≤ F*w i/v+1)
    (hbudget : ∑ i, w i*(minorDegrees a b i : ℝ) ≤ D) :
    Real.log (minorDenominator T a b : ℝ) ≤
      formalLcmConstant*(F/v*D+D/wmin) := by
  have he := sum_degrees_le_of_joint_budget (minorDegrees a b) w wmin D hwmin hw hbudget
  have hh : (∑ i, (minorDegrees a b i : ℝ)*T i) ≤ F/v*D+D/wmin := by
    calc
      _ ≤ ∑ i, (minorDegrees a b i : ℝ)*(F*w i/v+1) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hT i) (by positivity))
      _ = F/v*(∑ i, w i*(minorDegrees a b i : ℝ))+
          ∑ i, (minorDegrees a b i : ℝ) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hbudget (div_nonneg hF hv.le)) he
  exact (log_minorDenominator_le T a b).trans
    (mul_le_mul_of_nonneg_left hh formalLcmConstant_pos.le)

noncomputable def arithmeticError (F v w0 wmin : ℝ) (k : ℕ) : ℝ :=
  2*formalLcmConstant*F/v+Real.log 2/v+Real.log (3/2)/w0+
    (2*formalLcmConstant+Real.log (2*(2*k+2))+Real.log (Real.sqrt 3))/wmin

/-- Converts the already proved actual-minor log inequality and explicit
row/column and Mahler budgets to its normalized form. All geometric budgets
remain visible; this lemma asserts no pi finiteness theorem. -/
theorem normalize_minor_log_lower {ι : Type*} [Fintype ι] {m : ℕ}
    (T : Fin m → ℕ) (a b : ι → Fin m → ℕ) (s h : ι → ℕ)
    (k : ℕ) (w R M : Fin m → ℝ) (F v w0 wmin D rebate : ℝ) (z : ℂ)
    (hF : 0 ≤ F) (hv : 0 < v) (hw0 : 0 < w0) (hwmin : 0 < wmin) (hD : 0 < D)
    (hw : ∀ i, wmin ≤ w i) (hT : ∀ i, (T i : ℝ) ≤ F*w i/v+1)
    (hjoint : ∑ i, w i*(minorDegrees a b i : ℝ) ≤ D*(1-rebate))
    (hrebate : 0 ≤ rebate)
    (hs : (∑ r, s r : ℕ) ≤ D/v) (hh : (∑ c, h c : ℕ) ≤ D/w0)
    (hα : (∑ c, ∑ i, a c i : ℕ) ≤ D/wmin)
    (hM : ∀ i, Real.log (M i) ≤ w i+Real.log (Real.sqrt 3))
    (hR : ∀ i, 1 ≤ R i)
    (hlower : -2*Real.log (minorDenominator T a b : ℝ)-
      Real.log (minorCoefficientEnvelope k s h a b)-
      (∑ i, (minorDegrees a b i : ℝ)*Real.log (M i))+
      (∑ i, (minorDegrees a b i : ℝ)*Real.log (R i)) ≤ Real.log ‖z‖) :
    -(1-rebate)-arithmeticError F v w0 wmin k-
      Real.log ((Fintype.card ι).factorial : ℝ)/D ≤ Real.log ‖z‖/D := by
  have hb : ∑ i, w i*(minorDegrees a b i : ℝ) ≤ D :=
    hjoint.trans (by nlinarith)
  have he := sum_degrees_le_of_joint_budget (minorDegrees a b) w wmin D hwmin hw hb
  have hq := log_minorDenominator_le_joint T a b w F v wmin D hF hv hwmin hw hT hb
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog15 : 0 ≤ Real.log (3/2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogk : 0 ≤ Real.log (2*k+2 : ℝ) := Real.log_nonneg (by
    have : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith)
  have hlog3 : 0 ≤ Real.log (Real.sqrt 3) := Real.log_nonneg (by
    have := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    have := Real.sqrt_nonneg (3 : ℝ)
    nlinarith)
  have hC : Real.log (minorCoefficientEnvelope k s h a b) ≤
      Real.log ((Fintype.card ι).factorial : ℝ)+D/v*Real.log 2+
      D/w0*Real.log (3/2)+D/wmin*Real.log 2+D/wmin*Real.log (2*k+2) := by
    rw [log_minorCoefficientEnvelope]
    have he' : (∑ i, minorDegrees a b i : ℕ) ≤ D/wmin := by
      simpa only [Nat.cast_sum] using he
    gcongr
  have hheight := joint_height_log_cost (minorDegrees a b) w M (Real.log (Real.sqrt 3))
    (D*(1-rebate)) hM hjoint
  have hheight' : (∑ i, (minorDegrees a b i : ℝ)*Real.log (M i)) ≤
      D*(1-rebate)+Real.log (Real.sqrt 3)*(D/wmin) :=
    hheight.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left he hlog3))
  have hRsum : 0 ≤ ∑ i, (minorDegrees a b i : ℝ)*Real.log (R i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (Real.log_nonneg (hR i)))
  have hraw : -D*(1-rebate)-
      2*formalLcmConstant*(F/v*D+D/wmin)-
      (Real.log ((Fintype.card ι).factorial : ℝ)+D/v*Real.log 2+
        D/w0*Real.log (3/2)+D/wmin*Real.log 2+D/wmin*Real.log (2*k+2))-
      Real.log (Real.sqrt 3)*(D/wmin) ≤ Real.log ‖z‖ := by linarith
  apply (le_div_iff₀ hD).mpr
  have hlog : Real.log (2*(2*k+2 : ℝ)) = Real.log 2+Real.log (2*k+2) :=
    Real.log_mul (by norm_num) (by positivity)
  unfold arithmeticError
  rw [hlog]
  convert hraw using 1 <;> field_simp <;> ring

/-- The normalized statement for the actual nonzero truncated-log minor.
Only the displayed geometric budgets and Mahler-to-weight bound are inputs. -/
theorem formal_minor_fixed_field_normalized_lower {G K ι : Type*} [Field G] [Field K]
    [NumberField K] [Algebra GaussianInt G] [IsFractionRing GaussianInt G]
    [Algebra G K] [Algebra GaussianInt K] [IsScalarTower GaussianInt G K]
    [FiniteDimensional G K] [IsGalois G K] [Fintype ι] [DecidableEq ι] {m : ℕ}
    (hdegree : Module.finrank G K = 2) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1)
    (T : Fin m → ℕ) (k : ℕ) (j s h : ι → ℕ) (b a : ι → Fin m → ℕ)
    (hj : ∀ r, j r ≤ k) (la lb lc : Fin m → ℤ) (x : Fin m → K)
    (hprim : ∀ i, Int.gcd (Int.gcd (la i) (lb i) : ℤ) (lc i) = 1)
    (hf : ∀ i, C (la i : K)*X^2+C (lb i : K)*X+C (lc i : K) =
      C (la i : K)*((X-C (x i))*(X-C (τ (x i)))))
    (ha : ∀ i, la i ≠ 0) (φ : K →+* ℂ)
    (hφ : φ.comp (algebraMap GaussianInt K) = GaussianInt.toComplex)
    (hne : MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a) ≠ 0)
    (w : Fin m → ℝ) (F v w0 wmin D rebate : ℝ)
    (hF : 0 ≤ F) (hv : 0 < v) (hw0 : 0 < w0) (hwmin : 0 < wmin) (hD : 0 < D)
    (hw : ∀ i, wmin ≤ w i) (hT : ∀ i, (T i : ℝ) ≤ F*w i/v+1)
    (hjoint : ∑ i, w i*(minorDegrees a b i : ℝ) ≤ D*(1-rebate))
    (hrebate : 0 ≤ rebate)
    (hs : (∑ r, s r : ℕ) ≤ D/v) (hh : (∑ c, h c : ℕ) ≤ D/w0)
    (hα : (∑ c, ∑ i, a c i : ℕ) ≤ D/wmin)
    (hM : ∀ i, Real.log (‖φ (la i : K)‖*max 1 ‖φ (x i)‖*
      max 1 ‖φ (τ (x i))‖) ≤ w i+Real.log (Real.sqrt 3)) :
    -(1-rebate)-arithmeticError F v w0 wmin k-
      Real.log ((Fintype.card ι).factorial : ℝ)/D ≤
      Real.log ‖MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a)‖/D := by
  exact normalize_minor_log_lower T a b s h k w
    (fun i => max 1 ‖φ (x i)‖)
    (fun i => ‖φ (la i : K)‖*max 1 ‖φ (x i)‖*max 1 ‖φ (τ (x i))‖)
    F v w0 wmin D rebate
    (MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a))
    hF hv hw0 hwmin hD hw hT hjoint hrebate hs hh hα hM (fun i => le_max_left _ _)
    (formal_minor_fixed_field_log_lower hdegree τ hτ T k j s h b a hj la lb lc x
      hprim hf ha φ hφ hne)

end FixedQuadratic
