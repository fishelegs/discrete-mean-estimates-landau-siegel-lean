import ZhangLS.Spec.Lemma84LogPerronShift
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
set_option maxHeartbeats 2000000

lemma lemma84_original_kernel_eq_log {x : ℝ} (hx : 0 < x) (c : ℝ)
    (m : ℂ) (hm : m.re = 0) (t : ℝ) :
    (x:ℂ)^((c:ℂ)+I*(t:ℂ))/((c:ℂ)+I*(t:ℂ)+m)^2 =
      lemma84LogKernel c (Real.log x) m.im t := by
  rw [lemma84_positive_cpow_eq_exp hx]
  unfold lemma84LogKernel
  have hm' := lemma84_pure_imaginary_eq hm
  conv_lhs => rw [hm']
  push_cast
  congr 2
  ring

lemma lemma84_positive_div_cpow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x/y : ℝ):ℂ)^s = (x:ℂ)^s/(y:ℂ)^s := by
  simp_rw [lemma84_positive_cpow_eq_exp (div_pos hx hy),lemma84_positive_cpow_eq_exp hx,
    lemma84_positive_cpow_eq_exp hy]
  rw [←Complex.exp_sub,Real.log_div hx.ne' hy.ne',Complex.ofReal_sub]
  congr 1
  ring

noncomputable def lemma84MellinTerm (a : ℕ → ℂ) (c : ℝ) (m : ℂ) (x : ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term a (1+((c:ℂ)+I*(t:ℂ))) n *
    ((x:ℂ)^((c:ℂ)+I*(t:ℂ))/((c:ℂ)+I*(t:ℂ)+m)^2)

noncomputable def lemma84PerronTerm (a : ℕ → ℂ) (m : ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  if n=0 then 0 else if (n:ℝ)<x then
    a n/(n:ℂ)*((x/(n:ℝ):ℝ):ℂ)^(-m)*(Real.log (x/(n:ℝ)):ℂ) else 0

lemma lemma84_mellin_term_eq_log_kernel (a : ℕ → ℂ) (c : ℝ) (m : ℂ)
    (hm : m.re = 0) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    lemma84MellinTerm a c m x n t =
      (a n/(n:ℂ))*lemma84LogKernel c (Real.log (x/(n:ℝ))) m.im t := by
  have hnp : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  rw [← lemma84_original_kernel_eq_log (div_pos hx hnp) c m hm t,
    lemma84MellinTerm,LSeries.term_of_ne_zero hn,
    lemma84_positive_div_cpow hx hnp]
  rw [Complex.ofReal_natCast,Complex.cpow_add _ _ hnC,Complex.cpow_one]
  ring

lemma lemma84_mellin_term_integrable (a : ℕ → ℂ) {c : ℝ} (hc : 0 < c) (m : ℂ)
    (hm : m.re = 0) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Integrable (lemma84MellinTerm a c m x n) := by
  by_cases hn : n=0
  · subst n
    have he : lemma84MellinTerm a c m x 0 = 0 := by funext t; simp [lemma84MellinTerm]
    rw [he]
    exact integrable_zero ℝ ℂ volume
  · have he : lemma84MellinTerm a c m x n =
        fun t => (a n/(n:ℂ))*lemma84LogKernel c (Real.log (x/(n:ℝ))) m.im t := by
      funext t
      exact lemma84_mellin_term_eq_log_kernel a c m hm hx hn t
    rw [he]
    exact (lemma84_log_kernel_integrable hc _ _).const_mul _

lemma lemma84_mellin_term_integral (a : ℕ → ℂ) {c : ℝ} (hc : 0 < c) (m : ℂ)
    (hm : m.re = 0) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (2*Real.pi:ℂ)⁻¹*(∫ t : ℝ, lemma84MellinTerm a c m x n t) =
      lemma84PerronTerm a m x n := by
  by_cases hn : n=0
  · subst n
    simp [lemma84MellinTerm,lemma84PerronTerm]
  have hnp : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp_rw [lemma84_mellin_term_eq_log_kernel a c m hm hx hn]
  rw [integral_const_mul]
  have hi := lemma84_original_log_perron_kernel hc (div_pos hx hnp) m hm
  simp_rw [lemma84_original_kernel_eq_log (div_pos hx hnp) c m hm] at hi
  rw [show (2*Real.pi:ℂ)⁻¹*((a n/(n:ℂ))*(∫ t : ℝ, lemma84LogKernel c (Real.log (x/(n:ℝ))) m.im t)) =
      (a n/(n:ℂ))*((2*Real.pi:ℂ)⁻¹*(∫ t : ℝ, lemma84LogKernel c (Real.log (x/(n:ℝ))) m.im t)) by ring,hi]
  simp only [lemma84PerronTerm,if_neg hn,one_lt_div hnp]
  split_ifs <;> ring

lemma lemma84_original_kernel_norm {x : ℝ} (hx : 0 < x) (c : ℝ)
    (m : ℂ) (hm : m.re = 0) (t : ℝ) :
    ‖(x:ℂ)^((c:ℂ)+I*(t:ℂ))/((c:ℂ)+I*(t:ℂ)+m)^2‖ =
      x^c*‖lemma84LogKernel c 0 m.im t‖ := by
  rw [lemma84_original_kernel_eq_log hx c m hm,lemma84_log_kernel_norm,lemma84_log_kernel_norm]
  simp only [mul_zero,Real.exp_zero,one_mul]
  rw [Real.rpow_def_of_pos hx]
  congr 2
  ring

lemma lemma84_mellin_term_norm (a : ℕ → ℂ) (c : ℝ) (m : ℂ)
    (hm : m.re = 0) {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖lemma84MellinTerm a c m x n t‖ =
      (x^c*‖LSeries.term a ((1+c:ℝ):ℂ) n‖)*‖lemma84LogKernel c 0 m.im t‖ := by
  have ht : ‖LSeries.term a (1+((c:ℂ)+I*(t:ℂ))) n‖ =
      ‖LSeries.term a ((1+c:ℝ):ℂ) n‖ := by simp [LSeries.norm_term_eq]
  rw [lemma84MellinTerm,norm_mul,ht,lemma84_original_kernel_norm hx c m hm]
  ring

lemma lemma84_mellin_integral_norm_summable (a : ℕ → ℂ) (c : ℝ) (m : ℂ)
    (hm : m.re = 0) {x : ℝ} (hx : 0 < x)
    (ha : LSeriesSummable a ((1+c:ℝ):ℂ)) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖lemma84MellinTerm a c m x n t‖) := by
  have hs : Summable (fun n : ℕ => ‖LSeries.term a ((1+c:ℝ):ℂ) n‖) := summable_norm_iff.mpr ha
  let C := x^c*(∫ t : ℝ, ‖lemma84LogKernel c 0 m.im t‖)
  apply (hs.mul_left C).congr
  intro n
  simp_rw [lemma84_mellin_term_norm a c m hm hx n]
  rw [integral_const_mul]
  dsimp [C]
  ring

end ZhangLS.Spec
