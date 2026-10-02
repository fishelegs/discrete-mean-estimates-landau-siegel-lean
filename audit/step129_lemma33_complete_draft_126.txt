import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000

lemma lemma33_local_scalar_sampling {q q' B : ℝ → ℝ} {a δ : ℝ}
    (hδ : 0 < δ) (hq : Continuous q) (hq' : Continuous q') (hB : Continuous B)
    (hd : ∀ x, HasDerivAt q (q' x) x)
    (hBn : ∀ x, 0 ≤ B x) (hdB : ∀ x, ‖q' x‖ ≤ B x) :
    δ * q a ≤ (∫ x in a..a+δ, q x) + δ * (∫ x in a..a+δ, B x) := by
  have hab : a ≤ a+δ := by linarith
  have hiB := hB.intervalIntegrable (μ := volume) a (a+δ)
  have hiq := hq.intervalIntegrable (μ := volume) a (a+δ)
  have hp (x : ℝ) (hx : x ∈ Icc a (a+δ)) :
      q a ≤ q x + (∫ t in a..a+δ, B t) := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hd t) (hq'.intervalIntegrable (μ := volume) a x)
    have hn : ‖q x - q a‖ ≤ ∫ t in a..x, B t := by
      rw [← he]
      exact intervalIntegral.norm_integral_le_of_norm_le hx.1
        (ae_of_all _ (fun t _ => hdB t))
        (hB.intervalIntegrable (μ := volume) a x)
    have hm := intervalIntegral.integral_mono_interval (le_refl a) hx.1 hx.2
      (ae_of_all _ (fun t => hBn t)) hiB
    rw [Real.norm_eq_abs] at hn
    have ha := (abs_le.mp hn).1
    linarith
  have hh := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => q a) volume a (a+δ))
    (hiq.add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add hiq intervalIntegrable_const,
    intervalIntegral.integral_const] at hh
  simpa only [add_sub_cancel_left,smul_eq_mul] using hh

lemma lemma33_norm_square_derivative {F : ℝ → ℂ} {z : ℂ} {x : ℝ}
    (h : HasDerivAt F z x) :
    HasDerivAt (fun t => ‖F t‖ ^ 2)
      (2 * ((F x).re * z.re + (F x).im * z.im)) x := by
  have hr : HasDerivAt (fun t => (F t).re) z.re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  have hi : HasDerivAt (fun t => (F t).im) z.im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h
  convert (hr.pow 2).add (hi.pow 2) using 1
  · ext t
    change ‖F t‖ ^ 2 = (F t).re ^ 2 + (F t).im ^ 2
    simpa only [pow_two,Complex.normSq_apply] using (Complex.normSq_eq_norm_sq (F t)).symm
  · dsimp
    ring

lemma lemma33_norm_square_derivative_bound (z w : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    δ * |2 * (z.re * w.re + z.im * w.im)| ≤ ‖z‖ ^ 2 + δ ^ 2 * ‖w‖ ^ 2 := by
  have he : δ * |2 * (z.re * w.re + z.im * w.im)| =
      |δ * (2 * (z.re * w.re + z.im * w.im))| := by
    rw [abs_mul δ (2 * (z.re * w.re + z.im * w.im)),abs_of_pos hδ]
  rw [he]
  simp only [Complex.sq_norm,Complex.normSq_apply]
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (z.re + δ*w.re),sq_nonneg (z.im + δ*w.im)]
  · nlinarith [sq_nonneg (z.re - δ*w.re),sq_nonneg (z.im - δ*w.im)]

lemma lemma33_local_norm_square_sampling {F F' : ℝ → ℂ} {a δ : ℝ}
    (hδ : 0 < δ) (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ x, HasDerivAt F (F' x) x) :
    δ * ‖F a‖ ^ 2 ≤ 2 * (∫ x in a..a+δ, ‖F x‖ ^ 2) +
      δ ^ 2 * (∫ x in a..a+δ, ‖F' x‖ ^ 2) := by
  let q := fun x => ‖F x‖ ^ 2
  let q' := fun x => 2 * ((F x).re * (F' x).re + (F x).im * (F' x).im)
  let B := fun x => δ⁻¹ * q x + δ * ‖F' x‖ ^ 2
  have hq : Continuous q := hF.norm.pow 2
  have hq' : Continuous q' := continuous_const.mul
    (((Complex.continuous_re.comp hF).mul (Complex.continuous_re.comp hF')).add
      ((Complex.continuous_im.comp hF).mul (Complex.continuous_im.comp hF')))
  have hB : Continuous B := (continuous_const.mul hq).add
    (continuous_const.mul (hF'.norm.pow 2))
  have hBn (x : ℝ) : 0 ≤ B x := by dsimp [B,q]; positivity
  have hdB (x : ℝ) : ‖q' x‖ ≤ B x := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    have he : δ * B x = ‖F x‖ ^ 2 + δ ^ 2 * ‖F' x‖ ^ 2 := by
      dsimp [B,q]
      field_simp
    rw [he]
    exact lemma33_norm_square_derivative_bound (F x) (F' x) hδ
  have h := lemma33_local_scalar_sampling (a := a) hδ hq hq' hB
    (fun x => lemma33_norm_square_derivative (hd x)) hBn hdB
  have hiq := hq.intervalIntegrable (μ := volume) a (a+δ)
  have hiF' := (hF'.norm.pow 2).intervalIntegrable (μ := volume) a (a+δ)
  dsimp only [B] at h
  rw [intervalIntegral.integral_add (hiq.const_mul _) (hiF'.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  convert h using 1
  dsimp only [q]
  field_simp
  ring

lemma lemma33_sampling_interval_sum_le {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) {A B δ : ℝ} (hδ : 0 ≤ δ) (hab : A ≤ B)
    (hx : ∀ i ∈ S, A ≤ x i ∧ x i + δ ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|)
    {q : ℝ → ℝ} (hq : Continuous q) (hn : ∀ t, 0 ≤ q t) :
    (∑ i ∈ S, ∫ t in x i..x i + δ, q t) ≤ ∫ t in A..B, q t := by
  classical
  have hp : Set.Pairwise (↑S) (fun i j => Disjoint (Ioc (x i) (x i + δ)) (Ioc (x j) (x j + δ))) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    have hh : |x i - x j| < δ := abs_lt.mpr ⟨by linarith [hti.1,hti.2,htj.1,htj.2],
      by linarith [hti.1,hti.2,htj.1,htj.2]⟩
    exact (not_lt_of_ge (hsep i hi j hj hij)) hh
  have hsub : (⋃ i ∈ S, Ioc (x i) (x i + δ)) ⊆ Ioc A B := by
    intro t ht
    simp only [mem_iUnion] at ht
    obtain ⟨i,hi,hti⟩ := ht
    exact ⟨(hx i hi).1.trans_lt hti.1,hti.2.trans (hx i hi).2⟩
  calc
    _ = ∑ i ∈ S, ∫ t in Ioc (x i) (x i + δ), q t := by
      apply Finset.sum_congr rfl
      intro i hi
      exact intervalIntegral.integral_of_le (by linarith)
    _ = ∫ t in ⋃ i ∈ S, Ioc (x i) (x i + δ), q t :=
      (integral_biUnion_finset S (fun _ _ => measurableSet_Ioc) hp
        (fun i _ => (hq.intervalIntegrable (μ := volume) (x i) (x i + δ)).1)).symm
    _ ≤ ∫ t in Ioc A B, q t := setIntegral_mono_set
      (hq.intervalIntegrable (μ := volume) A B).1 (ae_of_all _ hn) hsub.eventuallyLE
    _ = _ := (intervalIntegral.integral_of_le hab).symm

lemma lemma33_separated_norm_square_sampling {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) {A B δ : ℝ} (hδ : 0 < δ) (hab : A ≤ B)
    (hx : ∀ i ∈ S, A ≤ x i ∧ x i + δ ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|)
    {F F' : ℝ → ℂ} (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ t, HasDerivAt F (F' t) t) :
    δ * (∑ i ∈ S, ‖F (x i)‖ ^ 2) ≤ 2 * (∫ t in A..B, ‖F t‖ ^ 2) +
      δ ^ 2 * (∫ t in A..B, ‖F' t‖ ^ 2) := by
  have hq := lemma33_sampling_interval_sum_le S x hδ.le hab hx hsep
    (hF.norm.pow 2) (fun t => sq_nonneg _)
  have hq' := lemma33_sampling_interval_sum_le S x hδ.le hab hx hsep
    (hF'.norm.pow 2) (fun t => sq_nonneg _)
  calc
    _ ≤ ∑ i ∈ S, (2 * (∫ t in x i..x i+δ, ‖F t‖ ^ 2) +
        δ ^ 2 * (∫ t in x i..x i+δ, ‖F' t‖ ^ 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      exact lemma33_local_norm_square_sampling hδ hF hF' hd
    _ = 2 * (∑ i ∈ S, ∫ t in x i..x i+δ, ‖F t‖ ^ 2) +
        δ ^ 2 * (∑ i ∈ S, ∫ t in x i..x i+δ, ‖F' t‖ ^ 2) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hq (by norm_num))
      (mul_le_mul_of_nonneg_left hq' (sq_nonneg δ))

end ZhangLS.Spec
