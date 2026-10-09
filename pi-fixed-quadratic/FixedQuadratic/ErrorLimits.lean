import FixedQuadratic.ArithmeticErrors
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Normed

/- The elementary dimension definitions and estimates below are adapted from
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
PiExponent/Analysis/DimensionLimits and LocalAlgebra/Dimension. The coefficient
100 is generalized to an arbitrary nonnegative d and every proof is rechecked
in this independent pinned project. -/
namespace FixedQuadratic
noncomputable section
open Filter
open scoped Topology
 theorem tendsto_nat_add_one_div_pow {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
  simpa only [pow_one, pow_zero, ← add_div, zero_add] using h₁.add h₀

 theorem tendsto_pow_div_nat_add_one {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n / ((n : ℝ) + 1)) atTop atTop := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) + 1) / r ^ n :=
    Filter.Eventually.of_forall fun n =>
      div_pos (by positivity) (pow_pos (zero_lt_one.trans hr) n)
  have hwithin : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nat_add_one_div_pow hr, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun n : ℕ => (((n : ℝ) + 1) / r ^ n)⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

def dimensionK (C : ℝ) (m : ℕ) : ℕ := ⌊C ^ m⌋₊

def dimensionW (B : ℝ) (m : ℕ) : ℝ := (B ^ m)⁻¹

def dimensionV (theta B C : ℝ) (m : ℕ) : ℝ :=
  2 * (dimensionK C m : ℝ) * theta ^ m * dimensionW B m

theorem dimensionK_le (C : ℝ) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) ≤ C ^ m :=
  Nat.floor_le (pow_nonneg hC m)

theorem dimensionK_one_le (C : ℝ) (hC : 1 ≤ C) (m : ℕ) :
    1 ≤ dimensionK C m := by
  exact (Nat.one_le_floor_iff _).2 (one_le_pow₀ hC)

theorem dimensionW_pos (B : ℝ) (hB : 0 < B) (m : ℕ) :
    0 < dimensionW B m := by
  exact inv_pos.mpr (pow_pos hB m)

theorem dimensionV_pos (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    0 < dimensionV theta B C m := by
  have hK : 0 < (dimensionK C m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m))
  exact mul_pos (mul_pos (mul_pos (by norm_num) hK) (pow_pos htheta m))
    (dimensionW_pos B hB m)

theorem dimension_volume (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) * (dimensionW B m / dimensionV theta B C m) *
      theta ^ m = 1 / 2 := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hw : dimensionW B m ≠ 0 := ne_of_gt (dimensionW_pos B hB m)
  unfold dimensionV
  field_simp

theorem dimensionK_div_W_le (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) / dimensionW B m ≤ (C * B) ^ m := by
  rw [dimensionW, div_inv_eq_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos hB m).le

theorem dimensionV_geometric_lower (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (C * theta / B) ^ m ≤ dimensionV theta B C m := by
  have hfloor : C ^ m < (dimensionK C m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK : C ^ m ≤ 2 * (dimensionK C m : ℝ) := by linarith
  rw [div_pow, mul_pow, div_eq_mul_inv]
  unfold dimensionV dimensionW
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (pow_pos htheta m).le)
    (inv_pos.mpr (pow_pos hB m)).le

theorem dimension_volume_lt_one (theta C : ℝ) (htheta : 0 < theta)
    (hC : 0 ≤ C) (hsmall : C * theta < 1) (m : ℕ) (hm : 1 ≤ m) :
    (dimensionK C m : ℝ) * theta ^ m < 1 := by
  calc
    (dimensionK C m : ℝ) * theta ^ m ≤ C ^ m * theta ^ m :=
      mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos htheta m).le
    _ = (C * theta) ^ m := (mul_pow _ _ _).symm
    _ < 1 := pow_lt_one₀ (mul_nonneg hC htheta.le) hsmall (by omega)

theorem dimension_error_le (theta B C a b d : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (a * (m : ℝ) + b) / dimensionV theta B C m +
        d * (dimensionK C m : ℝ) / dimensionW B m ≤
      (a * (m : ℝ) + b) / (C * theta / B) ^ m + d * (C * B) ^ m := by
  have hr : 0 < (C * theta / B) ^ m := by
    have hCp : 0 < C := by
      by_contra hn
      have hz : C = 0 := le_antisymm (le_of_not_gt hn) hC
      subst C
      rcases m with _ | m <;> norm_num at hlarge
    positivity
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hr
      (dimensionV_geometric_lower theta B C htheta hB m hlarge)
  · rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (dimensionK_div_W_le B C hB hC m) hd

theorem dimension_collision_identity (theta A B C eta : ℝ)
    (htheta : 0 < theta) (hA : 0 < A) (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    eta ^ 2 * (dimensionK C m : ℝ) * theta ^ m /
        (((m : ℝ) + 1) * dimensionV theta B C m * A ^ m) =
      eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hA' : A ^ m ≠ 0 := ne_of_gt (pow_pos hA m)
  have hB' : B ^ m ≠ 0 := ne_of_gt (pow_pos hB m)
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold dimensionV dimensionW
  rw [div_pow]
  field_simp

theorem tendsto_dimension_error_majorant (theta B C a b d : ℝ)
    (hB : 0 < B) (hC : 0 < C) (hsmall : C * B < 1)
    (hlarge : 1 < C * theta / B) :
    Tendsto (fun m : ℕ => (a * (m : ℝ) + b) / (C * theta / B) ^ m +
      d * (C * B) ^ m) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hlarge
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hlarge
  have hlin : Tendsto (fun m : ℕ => (a * (m : ℝ) + b) /
      (C * theta / B) ^ m) atTop (𝓝 0) := by
    convert (h₁.const_mul a).add (h₀.const_mul b) using 1
    · ext m
      simp only [pow_one, pow_zero]
      ring
    · simp
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hC hB).le hsmall
  simpa only [mul_zero, add_zero] using hlin.add (hgeom.const_mul d)

theorem tendsto_dimension_collision (A B eta : ℝ)
    (hratio : 1 < B / A) (heta : 0 < eta) :
    Tendsto (fun m : ℕ => eta ^ 2 * (B / A) ^ m /
      (2 * ((m : ℝ) + 1))) atTop atTop := by
  have h := (tendsto_pow_div_nat_add_one hratio).const_mul_atTop
    (show 0 < eta ^ 2 / 2 by positivity)
  convert h using 1
  ext m
  rw [mul_div_mul_comm]

theorem exists_dimension_margin (theta A B C eta a b d epsilon target : ℝ)
    (htheta : 0 < theta) (hB : 0 < B) (hC : 1 < C)
    (hsmall : C * B < 1) (hlarge : 1 < C * theta / B)
    (hratio : 1 < B / A) (heta : 0 < eta)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV theta B C m +
        d * (dimensionK C m : ℝ) / dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have herrors := (tendsto_dimension_error_majorant theta B C a b d hB
    (zero_lt_one.trans hC) hsmall hlarge).eventually (gt_mem_nhds hepsilon)
  have hcollision := (tendsto_dimension_collision A B eta hratio heta).eventually
    (eventually_gt_atTop target)
  have hfloor := (tendsto_pow_atTop_atTop_of_one_lt hC).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hgood : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV theta B C m +
        d * (dimensionK C m : ℝ) / dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
    filter_upwards [herrors, hcollision, hfloor, eventually_ge_atTop 1]
      with m herror hcollision hfloor hm
    exact ⟨hm, (dimension_error_le theta B C a b d htheta hB
      (zero_lt_one.trans hC).le ha hb hd m hfloor).trans_lt herror, hcollision⟩
  exact hgood.exists


noncomputable def analyticError (nu F v w0 wmin : ℝ) (k : ℕ) : ℝ :=
  nu/F+2*Real.log 2/v+100*k/w0+
    (Real.log 4+Real.log (2*k)+nu+Real.log (200*k))/wmin

noncomputable def heightErrorCoefficient (nu : ℝ) (k : ℕ) : ℝ :=
  2*formalLcmConstant+Real.log (2*(2*k+2))+Real.log (Real.sqrt 3)+
    Real.log 4+Real.log (2*k)+nu+Real.log (200*k)

/-- The changed total, explicitly including the conjugate coefficient cost.
The analytic term is an error expression, not an assertion that the rational
upstream analytic theorem has already been ported. -/
theorem changed_error_sum (nu F v w0 wmin : ℝ) (k : ℕ) :
    arithmeticError F v w0 wmin k+analyticError nu F v w0 wmin k =
      nu/F+(2*formalLcmConstant*F+3*Real.log 2)/v+
      (100*k+Real.log (3/2))/w0+heightErrorCoefficient nu k/wmin := by
  unfold arithmeticError analyticError heightErrorCoefficient
  ring

theorem changed_error_lt (nu F v w0 wmin epsilon : ℝ) (k : ℕ)
    (hinitial : nu/F < epsilon/3)
    (hdimension : (2*formalLcmConstant*F+3*Real.log 2)/v+
      (100*k+Real.log (3/2))/w0 < epsilon/3)
    (hheight : heightErrorCoefficient nu k/wmin < epsilon/3) :
    arithmeticError F v w0 wmin k+analyticError nu F v w0 wmin k < epsilon := by
  rw [changed_error_sum]
  linarith

theorem changed_collision_margin (nu F v w0 wmin epsilon saving : ℝ) (k : ℕ)
    (hinitial : nu/F < epsilon/3)
    (hdimension : (2*formalLcmConstant*F+3*Real.log 2)/v+
      (100*k+Real.log (3/2))/w0 < epsilon/3)
    (hheight : heightErrorCoefficient nu k/wmin < epsilon/3)
    (hepsilon : epsilon ≤ 1/2) (hsaving : 2 < saving) :
    1+arithmeticError F v w0 wmin k+analyticError nu F v w0 wmin k < saving := by
  have := changed_error_lt nu F v w0 wmin epsilon k hinitial hdimension hheight
  linarith

theorem exists_changed_dimension_margin (theta A B C eta F epsilon target : ℝ)
    (htheta : 0 < theta) (hB : 0 < B) (hC : 1 < C)
    (hsmall : C*B < 1) (hlarge : 1 < C*theta/B)
    (hratio : 1 < B/A) (heta : 0 < eta) (hF : 0 ≤ F) (heps : 0 < epsilon) :
    ∃ m : ℕ, 1 ≤ m ∧
      (2*formalLcmConstant*F+3*Real.log 2)/dimensionV theta B C m+
      (100*(dimensionK C m : ℝ)+Real.log (3/2))/dimensionW B m < epsilon ∧
      target < eta^2*(B/A)^m/(2*((m : ℝ)+1)) := by
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have h15 : 0 ≤ Real.log (3/2 : ℝ) := Real.log_nonneg (by norm_num)
  have hcoef : 0 ≤ 2*formalLcmConstant*F :=
    mul_nonneg (mul_nonneg (by norm_num) formalLcmConstant_pos.le) hF
  obtain ⟨m, hm, herror, hcollision⟩ := exists_dimension_margin theta A B C eta
    (2*formalLcmConstant*F) (3*Real.log 2) (100+Real.log (3/2)) epsilon target
    htheta hB hC hsmall hlarge hratio heta hcoef (by positivity)
    (by positivity) heps
  refine ⟨m, hm, lt_of_le_of_lt ?_ herror, hcollision⟩
  have hK : (1 : ℝ) ≤ dimensionK C m := by
    exact_mod_cast dimensionK_one_le C hC.le m
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hv := dimensionV_pos theta B C htheta hB hC.le m
  have hw := dimensionW_pos B hB m
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ hv.le
    have hmul := mul_le_mul_of_nonneg_left hmR hcoef
    nlinarith only [hmul]
  · apply div_le_div_of_nonneg_right _ hw.le
    nlinarith

/-- Once the dimension and hence k have been fixed, a single lower bound for
all approximation weights absorbs the complete changed height coefficient. -/
theorem exists_changed_height_margin (nu : ℝ) (k : ℕ) (epsilon : ℝ)
    (heps : 0 < epsilon) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ wmin : ℝ, X ≤ wmin →
      heightErrorCoefficient nu k/wmin < epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (heightErrorCoefficient nu k/epsilon))
  have hn1 : (1 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnC : heightErrorCoefficient nu k/epsilon < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hn
  refine ⟨n, hn1.le, fun w hw => ?_⟩
  have hwpos : 0 < w := lt_of_lt_of_le (by linarith) hw
  apply (div_lt_iff₀ hwpos).mpr
  have hc := (div_lt_iff₀ heps).mp hnC
  nlinarith

theorem log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ)*Real.log n := by
  have hh : (n.factorial : ℝ) ≤ (n : ℝ)^n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hl := Real.log_le_log (show 0 < (n.factorial : ℝ) by positivity) hh
  simpa only [Real.log_pow] using hl

/-- Polynomial row growth gives a genuinely vanishing factorial cost with
all packet data held fixed before N tends to infinity. -/
theorem factorial_remainder_tendsto (M : ℕ → ℕ) (C : ℝ) (d : ℕ)
    (hC : 0 < C) (hM : ∀ᶠ N in atTop, 0 < M N ∧ (M N : ℝ) ≤ C*(N : ℝ)^d) :
    Tendsto (fun N : ℕ => Real.log ((M N).factorial : ℝ)/((M N : ℝ)*N)) atTop (𝓝 0) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (Real.log C)
  have hup : Tendsto (fun N : ℕ => (Real.log C+(d : ℝ)*Real.log N)/(N : ℝ))
      atTop (𝓝 0) := by
    convert hconst.add (hlogN.const_mul (d : ℝ)) using 1
    · ext N
      ring
    · simp
  apply squeeze_zero' ?_ ?_ hup
  · filter_upwards [eventually_ge_atTop 1] with N hN
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    · positivity
  · filter_upwards [hM, eventually_ge_atTop 1] with N hMN hN
    have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hMr : 0 < (M N : ℝ) := by exact_mod_cast hMN.1
    have hlM := Real.log_le_log hMr hMN.2
    rw [Real.log_mul hC.ne' (pow_pos hNr _).ne', Real.log_pow] at hlM
    apply (div_le_div_iff₀ (mul_pos hMr hNr) hNr).mpr
    have hf := log_factorial_le (M N)
    nlinarith [mul_le_mul_of_nonneg_left hlM hMr.le]

end
end FixedQuadratic
