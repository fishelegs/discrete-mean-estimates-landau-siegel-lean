import ZhangLS.Spec.Proposition71LocalizedSigmaSquare
import ZhangLS.Spec.Proposition71QuarterConductorSaving

/-! # A genuine weighted localized (7.15)-type saving for the repaired split

The range R≥D^(1/4) is wider than the printed R≥D range. All actual σ*,
primitive-character, r/φ(r), and original coefficient objects are retained.
The discarded localization tails are not asserted to be negligible here.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 4000000

/-- The actual localized dyadic mean has an explicit D^(-1/16) saving.
No desired averaged estimate, Euler identity, or cancellation is a premise. -/
theorem proposition71_actual_localized_dyadic_power_saving :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ c b B : ℝ, 0≤B → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
        ∀ R : ℝ, (D : ℝ)^(1/4 : ℝ)≤R → ∀ d h : ℕ,
          0<d → 0<h → ((d*h : ℕ) : ℝ)*R≤lemma81Cutoff D →
            proposition71LocalizedDyadicMean D c b a R h d/R^(3/2 : ℝ)≤
              C*B*(lemma34Tau 5 d : ℝ)*(h : ℝ)*lemma23PaperP D^2*(D : ℝ)^(-1/16 : ℝ) := by
  obtain ⟨Ds,hDs,hsquare⟩ := proposition71_actual_localized_sigma_square
  obtain ⟨Da,habsorb⟩ := proposition71_log_power_eighth_threshold 6625
  let K := proposition71LargeMeanSquareConstant
  have hK : 0<K := proposition71_large_mean_square_constant_pos
  refine ⟨Real.sqrt (2*K),by positivity,max Ds (max Da ⌈Real.exp 3⌉₊),hDs.trans (le_max_left _ _),?_⟩
  intro D hD c b B hB a ha R hRlower d h hd hh hcut
  have hDsD := (le_max_left _ _).trans hD
  have hDaD := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hD3 := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hD2 : 2≤D := hDs.trans hDsD
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hD1 : 1≤(D : ℝ) := by exact_mod_cast (show 1≤D by omega)
  have hL : 3≤lemma23PaperL D := lemma33_parameters_at_threshold hD3
  have hLp : 0≤lemma23PaperL D := by linarith
  have hR : 1≤R := (Real.one_le_rpow hD1 (by norm_num : (0:ℝ)≤1/4)).trans hRlower
  have hRp : 0<R := by linarith
  have hPp : 0<lemma23PaperP D := Real.exp_pos _
  have hSq := hsquare D hDsD c b B hB a ha R hR d h hd hh hcut
  have hdh : 1≤((d*h : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd hh
  have hRcut : R≤lemma81Cutoff D := by
    have hh' := mul_le_mul_of_nonneg_right hdh hRp.le
    simpa only [one_mul] using hh'.trans hcut
  have hTD : lemma56PaperT D^(-2 : ℤ)≤(D : ℝ)⁻¹ := by
    have he := lemma81_T_inverse_square_le_exp_neg_log hL
    simpa [Real.exp_neg,lemma23PaperL,Real.exp_log hDp] using he
  have hRP : R/lemma23PaperP D≤(D : ℝ)⁻¹ := by
    have hh' := div_le_div_of_nonneg_right hRcut hPp.le
    have he : lemma81Cutoff D/lemma23PaperP D=lemma56PaperT D^(-2 : ℤ) := by
      unfold lemma81Cutoff
      field_simp
    exact (hh'.trans_eq he).trans hTD
  have hDinverse : (D : ℝ)⁻¹≤(D : ℝ)^(-1/4 : ℝ) := by
    have he := Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num : (-1 : ℝ)≤-1/4)
    simpa only [Real.rpow_neg_one] using he
  have hRinverse : R⁻¹≤(D : ℝ)^(-1/4 : ℝ) := by
    have he := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hDp (1/4 : ℝ)) hRlower (by norm_num : (-1 : ℝ)≤0)
    rw [Real.rpow_neg_one,←Real.rpow_mul hDp.le] at he
    convert he using 1 <;> norm_num
  have hratio : R/lemma23PaperP D+R⁻¹≤2*(D : ℝ)^(-1/4 : ℝ) := by
    linarith [hRP.trans hDinverse,hRinverse]
  have hRpow : (R^(3/2 : ℝ))^2=R^3 := by
    rw [proposition71_three_halves_eq_mul_sqrt hRp.le,mul_pow,Real.sq_sqrt hRp.le]
    ring
  have hnorm : (proposition71LocalizedDyadicMean D c b a R h d/R^(3/2 : ℝ))^2≤
      K*B^2*(lemma34Tau 5 d : ℝ)^2*(h : ℝ)^2*lemma23PaperP D^4*lemma23PaperL D^6625*
        (R/lemma23PaperP D+R⁻¹) := by
    rw [div_pow,hRpow]
    apply (div_le_iff₀ (pow_pos hRp 3)).mpr
    apply hSq.trans_eq
    dsimp [K]
    field_simp
  have hLog := habsorb D hDaD
  have hfinal : (proposition71LocalizedDyadicMean D c b a R h d/R^(3/2 : ℝ))^2≤
      2*K*B^2*(lemma34Tau 5 d : ℝ)^2*(h : ℝ)^2*lemma23PaperP D^4*(D : ℝ)^(-1/8 : ℝ) := by
    calc
      _≤K*B^2*(lemma34Tau 5 d : ℝ)^2*(h : ℝ)^2*lemma23PaperP D^4*lemma23PaperL D^6625*
          (R/lemma23PaperP D+R⁻¹) := hnorm
      _≤K*B^2*(lemma34Tau 5 d : ℝ)^2*(h : ℝ)^2*lemma23PaperP D^4*lemma23PaperL D^6625*
          (2*(D : ℝ)^(-1/4 : ℝ)) := by gcongr
      _≤K*B^2*(lemma34Tau 5 d : ℝ)^2*(h : ℝ)^2*lemma23PaperP D^4*(D : ℝ)^(1/8 : ℝ)*
          (2*(D : ℝ)^(-1/4 : ℝ)) := by gcongr
      _=(2*K*B^2*(lemma34Tau 5 d : ℝ)^2*(h : ℝ)^2*lemma23PaperP D^4)*
          ((D : ℝ)^(1/8 : ℝ)*(D : ℝ)^(-1/4 : ℝ)) := by ring
      _=_ := by rw [←Real.rpow_add hDp]; norm_num
  have hDpow : ((D : ℝ)^(-1/16 : ℝ))^2=(D : ℝ)^(-1/8 : ℝ) := by
    calc
      _=((D : ℝ)^(-1/16 : ℝ))^(2 : ℝ) := by rw [Real.rpow_two]
      _=(D : ℝ)^((-1/16 : ℝ)*2) := (Real.rpow_mul hDp.le _ _).symm
      _=_ := by norm_num
  apply (sq_le_sq₀ (div_nonneg (proposition71_localized_dyadic_mean_nonneg D c b a R h d)
    (Real.rpow_nonneg hRp.le _)) (by positivity)).mp
  convert hfinal using 1
  simp only [mul_pow,Real.sq_sqrt (by positivity : 0≤2*K),hDpow,←pow_mul]

end ZhangLS.Spec
