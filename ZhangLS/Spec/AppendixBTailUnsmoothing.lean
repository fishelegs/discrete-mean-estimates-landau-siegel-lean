import ZhangLS.Spec.Lemma57GaussianMellinTransform
import ZhangLS.Spec.Lemma23GoodSet

/-! Genuine Gaussian-to-strict-step estimates, including the exact half-weight
at equality. The finite weighted error separates its actual boundary mass. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical

noncomputable def appendixBStrictLogStep (u : ℝ) : ℝ := if 0<u then 1 else 0

noncomputable def appendixBGaussianStepError (D : ℕ) (u : ℝ) : ℝ :=
  |zhangGaussianWeight D (Real.exp u)-appendixBStrictLogStep u|

lemma appendixB_gaussian_step_endpoint (D : ℕ) :
    zhangGaussianWeight D 1=1/2 ∧ appendixBStrictLogStep 0=0 ∧
      appendixBGaussianStepError D 0=1/2 := by
  norm_num [zhangGaussianWeight,zhangGaussianEndpoint,appendixBStrictLogStep,
    appendixBGaussianStepError]

lemma appendixB_gaussian_weight_unit_interval {D : ℕ} (hD : 1<D) (u : ℝ) :
    0≤zhangGaussianWeight D (Real.exp u) ∧ zhangGaussianWeight D (Real.exp u)≤1 := by
  have hp := zhangGaussianWeight_nonneg hD (Real.exp_pos u)
  have hn := zhangGaussianWeight_nonneg hD (Real.exp_pos (-u))
  exact ⟨hp,by linarith [zhangGaussianWeight_exp_add_neg (D := D) u]⟩

lemma appendixB_gaussian_step_error_le_one {D : ℕ} (hD : 1<D) (u : ℝ) :
    appendixBGaussianStepError D u≤1 := by
  obtain ⟨h0,h1⟩ := appendixB_gaussian_weight_unit_interval hD u
  unfold appendixBGaussianStepError appendixBStrictLogStep
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

/-- The exact Gaussian tail estimate off a logarithmic boundary band. -/
theorem appendixB_gaussian_step_error_off_boundary {D : ℕ} (hD : 1<D)
    {K u : ℝ} (hK : 0<K) (hu : K≤lemma23PaperL D^15*|u|) :
    appendixBGaussianStepError D u≤
      (Real.sqrt Real.pi)⁻¹*Real.exp (-(K^2))/K := by
  have hL : 0<lemma23PaperL D := Real.log_pos (by exact_mod_cast hD)
  have hA : 0<lemma23PaperL D^15 := pow_pos hL 15
  have hu0 : u≠0 := by intro he; simp [he] at hu; linarith
  have hnegative (v : ℝ) (hv : v<0) (hvK : K≤ -(lemma23PaperL D^15*v)) :
      zhangGaussianWeight D (Real.exp v)≤
        (Real.sqrt Real.pi)⁻¹*Real.exp (-(K^2))/K := by
    have hend : zhangGaussianEndpoint D (Real.exp v)=lemma23PaperL D^15*v := by
      simp [zhangGaussianEndpoint,lemma23PaperL]
    have he0 : zhangGaussianEndpoint D (Real.exp v)≤0 := by rw [hend]; nlinarith
    rw [zhangGaussianWeight_eq_tail_of_endpoint_nonpos he0]
    have ht := zhangGaussianTail_le_exp_linear (y := -zhangGaussianEndpoint D (Real.exp v)) hK (by rw [hend]; exact hvK)
    calc
      _ ≤ (Real.sqrt Real.pi)⁻¹*(Real.exp (-K*(-zhangGaussianEndpoint D (Real.exp v)))/K) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (Real.sqrt Real.pi)⁻¹*(Real.exp (-(K^2))/K) := by
        gcongr
        rw [hend]
        nlinarith
      _ = _ := by ring
  by_cases hpos : 0<u
  · have hvK : K≤ -(lemma23PaperL D^15*(-u)) := by
      rw [abs_of_pos hpos] at hu
      nlinarith
    have ht := hnegative (-u) (neg_neg_of_pos hpos) hvK
    have he := zhangGaussianWeight_exp_add_neg (D := D) u
    have hgn := (appendixB_gaussian_weight_unit_interval hD (-u)).1
    unfold appendixBGaussianStepError appendixBStrictLogStep
    rw [if_pos hpos,show zhangGaussianWeight D (Real.exp u)-1=
      -zhangGaussianWeight D (Real.exp (-u)) by linarith,abs_neg,abs_of_nonneg hgn]
    exact ht
  · have hneg : u<0 := lt_of_le_of_ne (le_of_not_gt hpos) hu0
    have hvK : K≤ -(lemma23PaperL D^15*u) := by
      rw [abs_of_neg hneg] at hu
      nlinarith
    unfold appendixBGaussianStepError appendixBStrictLogStep
    rw [if_neg hpos,sub_zero,abs_of_nonneg (appendixB_gaussian_weight_unit_interval hD u).1]
    exact hnegative u hneg hvK

noncomputable def appendixBGaussianBoundaryBand (D : ℕ) (K : ℝ)
    (u : ℕ→ℝ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun n => lemma23PaperL D^15*|u n|<K)

/-- Quantitative finite unsmoothing with an explicit boundary mass. The rho
pointwise estimate supplies M=exp(3*pi) in the original n<=P range, removing
any divisor-function or log(P) loss from the boundary contribution. -/
theorem appendixB_gaussian_finite_unsmoothing {D : ℕ} (hD : 1<D)
    (S : Finset ℕ) (u : ℕ→ℝ) (a : ℕ→ℂ) {K M : ℝ}
    (hK : 0<K) (hM : 0≤M) (ha : ∀ n∈S, ‖a n‖≤M/(n : ℝ)) :
    ‖∑ n∈S, a n*((zhangGaussianWeight D (Real.exp (u n))-
      appendixBStrictLogStep (u n) : ℝ) : ℂ)‖≤
      M*(∑ n∈appendixBGaussianBoundaryBand D K u S, (1 : ℝ)/n)+
        ((Real.sqrt Real.pi)⁻¹*Real.exp (-(K^2))/K)*
          M*(∑ n∈S\appendixBGaussianBoundaryBand D K u S, (1 : ℝ)/n) := by
  let B := appendixBGaussianBoundaryBand D K u S
  let E := (Real.sqrt Real.pi)⁻¹*Real.exp (-(K^2))/K
  have hBS : B⊆S := Finset.filter_subset _ _
  have hE : 0≤E := by dsimp [E]; positivity
  have hbound (n : ℕ) (hn : n∈S) :
      ‖a n*((zhangGaussianWeight D (Real.exp (u n))-
        appendixBStrictLogStep (u n) : ℝ) : ℂ)‖≤
          if n∈B then M/n else E*(M/n) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    change ‖a n‖*appendixBGaussianStepError D (u n)≤_
    by_cases hb : n∈B
    · rw [if_pos hb]
      exact (mul_le_mul (ha n hn) (appendixB_gaussian_step_error_le_one hD (u n))
        (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    · rw [if_neg hb]
      have hfar : K≤lemma23PaperL D^15*|u n| := by
        simp only [B,appendixBGaussianBoundaryBand,Finset.mem_filter,hn,true_and] at hb
        exact le_of_not_gt hb
      exact (mul_le_mul (ha n hn) (appendixB_gaussian_step_error_off_boundary hD hK hfar)
        (abs_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
  calc
    _ ≤ ∑ n∈S, ‖a n*((zhangGaussianWeight D (Real.exp (u n))-
        appendixBStrictLogStep (u n) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n∈S, if n∈B then M/n else E*(M/n) := Finset.sum_le_sum hbound
    _ = (∑ n∈B, M/n)+(∑ n∈S\B, E*(M/n)) := by
      rw [←Finset.sum_sdiff hBS (f := fun n => if n∈B then M/(n : ℝ) else E*(M/n))]
      rw [add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro n hn
        simp only [if_pos hn]
      · apply Finset.sum_congr rfl
        intro n hn
        simp only [if_neg (Finset.mem_sdiff.mp hn).2]
    _ = _ := by
      simp only [div_eq_mul_inv,←Finset.mul_sum,one_mul]
      dsimp [B,E]
      ring

end ZhangLS.Spec
