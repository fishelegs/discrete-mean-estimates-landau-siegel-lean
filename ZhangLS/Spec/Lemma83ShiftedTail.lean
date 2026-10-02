import ZhangLS.Spec.Lemma83KappaLocal
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 800000

/-- A power series absolutely convergent on a larger disc gives an absolutely
convergent shifted double series on any smaller bidisc. -/
lemma lemma83_shifted_double_summable (f : ℕ → ℂ) (x t : ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hx : ‖x‖ < ρ) (ht : ‖t‖ < ρ)
    (hf : Summable (fun n => ‖f n‖*ρ^n)) :
    Summable (fun ij : ℕ × ℕ => f (ij.1+ij.2)*x^ij.1*t^ij.2) := by
  let C := ∑' n : ℕ, ‖f n‖*ρ^n
  have hb (n : ℕ) : ‖f n‖*ρ^n ≤ C :=
    hf.le_tsum n (fun m _ => mul_nonneg (norm_nonneg _) (pow_nonneg hρ.le _))
  have hxn : ‖‖x‖/ρ‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) hρ.le)]
    exact (div_lt_one hρ).mpr hx
  have htn : ‖‖t‖/ρ‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) hρ.le)]
    exact (div_lt_one hρ).mpr ht
  have hs := ((summable_geometric_of_norm_lt_one hxn).mul_of_nonneg
    (summable_geometric_of_norm_lt_one htn)
    (fun n => pow_nonneg (div_nonneg (norm_nonneg _) hρ.le) n)
    (fun n => pow_nonneg (div_nonneg (norm_nonneg _) hρ.le) n)).mul_left C
  apply hs.of_norm_bounded
  intro ij
  calc
    ‖f (ij.1+ij.2)*x^ij.1*t^ij.2‖ =
      (‖f (ij.1+ij.2)‖*ρ^(ij.1+ij.2))*((‖x‖/ρ)^ij.1*(‖t‖/ρ)^ij.2) := by
        simp only [norm_mul,norm_pow,div_pow,pow_add]
        field_simp
    _ ≤ C*((‖x‖/ρ)^ij.1*(‖t‖/ρ)^ij.2) :=
      mul_le_mul_of_nonneg_right (hb _) (by positivity)

lemma lemma83_antidiagonal_geometric (x t : ℂ) (hxt : x ≠ t) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, x^ij.1*t^ij.2) =
      (x^(n+1)-t^(n+1))/(x-t) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => x^i*t^j)]
  apply (eq_div_iff (sub_ne_zero.mpr hxt)).mpr
  simpa using geom_sum₂_mul x t (n+1)

/-- Reindex an absolutely convergent double power series by total degree. -/
lemma lemma83_shifted_double_tsum_eq (f : ℕ → ℂ) (x t : ℂ)
    (hf : Summable (fun ij : ℕ × ℕ => f (ij.1+ij.2)*x^ij.1*t^ij.2)) :
    (∑' i : ℕ, ∑' j : ℕ, f (i+j)*x^i*t^j) =
      ∑' n : ℕ, f n*(∑ ij ∈ antidiagonal n, x^ij.1*t^ij.2) := by
  let F : ℕ × ℕ → ℂ := fun ij => f (ij.1+ij.2)*x^ij.1*t^ij.2
  have he : Summable (F ∘ sigmaAntidiagonalEquivProd) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hf
  rw [← hf.tsum_prod,← sigmaAntidiagonalEquivProd.tsum_eq F]
  change (∑' c, (F ∘ sigmaAntidiagonalEquivProd) c) = _
  rw [he.tsum_sigma]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  simp only [Function.comp_apply,sigmaAntidiagonalEquivProd_apply]
  have hh : (∑ ij : antidiagonal n, F ij) = ∑ ij ∈ antidiagonal n, F ij :=
    Finset.sum_finset_coe F (antidiagonal n)
  change (∑ ij : antidiagonal n, F ij) = _
  rw [hh,mul_sum]
  apply sum_congr rfl
  intro ij hij
  have hij' := mem_antidiagonal.mp hij
  simp only [F]
  rw [hij']
  ring

lemma lemma83_shifted_tail_hasSum (f : ℕ → ℂ) (x t u v : ℂ)
    (hxt : x ≠ t) (hx : HasSum (fun n => f n*x^n) u)
    (ht : HasSum (fun n => f n*t^n) v)
    (hf : Summable (fun ij : ℕ × ℕ => f (ij.1+ij.2)*x^ij.1*t^ij.2)) :
    HasSum (fun r : ℕ => (∑' η : ℕ, f (r+η)*t^η)*x^r)
      ((x*u-t*v)/(x-t)) := by
  have hg : HasSum (fun n => f n*(∑ ij ∈ antidiagonal n, x^ij.1*t^ij.2))
      ((x*u-t*v)/(x-t)) := by
    convert ((hx.mul_left x).sub (ht.mul_left t)).div_const (x-t) using 1
    funext n
    rw [lemma83_antidiagonal_geometric x t hxt n,pow_succ,pow_succ]
    ring
  have ho : Summable (fun r : ℕ => (∑' η : ℕ, f (r+η)*t^η)*x^r) := by
    convert hf.prod using 1
    funext r
    rw [← tsum_mul_right]
    apply tsum_congr
    intro η
    ring
  convert ho.hasSum using 1
  rw [← hg.tsum_eq,← lemma83_shifted_double_tsum_eq f x t hf]
  apply tsum_congr
  intro r
  rw [← tsum_mul_right]
  apply tsum_congr
  intro η
  ring


/-- Shifting coefficients preserves convergence at every fixed point. -/
lemma lemma83_power_series_shifted_summable (f : ℕ → ℂ) (t : ℂ) (r : ℕ)
    (hf : Summable (fun n => f n*t^n)) :
    Summable (fun η : ℕ => f (r+η)*t^η) := by
  by_cases ht : t = 0
  · subst t
    convert (hasSum_ite_eq 0 (f r)).summable using 1
    funext n
    by_cases hn : n = 0 <;> simp [hn]
  · have hs := (summable_nat_add_iff r).mpr hf
    have hs' : Summable (fun n => (f (r+n)*t^n)*t^r) := by
      convert hs using 1
      funext n
      rw [Nat.add_comm r n,pow_add]
      ring
    exact (summable_mul_right_iff (pow_ne_zero r ht)).mp hs'

lemma lemma83_local_kappa_shifted_summable (a b c t : ℂ) (r : ℕ)
    (ha : ‖a*t‖ < 1) (hb : ‖b*t‖ < 1) (hc : ‖c*t‖ < 1) :
    Summable (fun η : ℕ => lemma83LocalKappa a b c (r+η)*t^η) :=
  lemma83_power_series_shifted_summable _ t r
    (lemma83_local_kappa_summable a b c t ha hb hc)

/-- The local κ double series converges absolutely throughout the open bidisc. -/
lemma lemma83_local_kappa_shifted_double_summable (a b c x t : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) :
    Summable (fun ij : ℕ × ℕ => lemma83LocalKappa a b c (ij.1+ij.2)*x^ij.1*t^ij.2) := by
  obtain ⟨ρ,hρmax,hρ1⟩ := exists_between (max_lt hx ht)
  have hρ : 0 < ρ := lt_of_le_of_lt (le_trans (norm_nonneg x) (le_max_left _ _)) hρmax
  have hn : ‖(ρ : ℂ)‖ = ρ := by simp [Real.norm_eq_abs,hρ.le]
  apply lemma83_shifted_double_summable _ x t ρ hρ
    (lt_of_le_of_lt (le_max_left _ _) hρmax) (lt_of_le_of_lt (le_max_right _ _) hρmax)
  have hh := lemma83_local_kappa_norm_summable a b c (ρ : ℂ)
    (by simpa only [norm_mul,ha,hn,one_mul] using hρ1)
    (by simpa only [norm_mul,hb,hn,one_mul] using hρ1)
    (by simpa only [norm_mul,hc,hn,one_mul] using hρ1)
  simpa only [norm_mul,norm_pow,hn] using hh

/-- The exact shifted-tail generating function required for the local ξ factor. -/
lemma lemma83_local_kappa_shifted_tail_hasSum (a b c x t : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) (hxt : x ≠ t) :
    HasSum (fun r : ℕ => (∑' η : ℕ, lemma83LocalKappa a b c (r+η)*t^η)*x^r)
      ((x*((1-x)/((1-a*x)*(1-b*x)*(1-c*x))) -
        t*((1-t)/((1-a*t)*(1-b*t)*(1-c*t))))/(x-t)) := by
  apply lemma83_shifted_tail_hasSum _ x t _ _ hxt
  · exact lemma83_local_kappa_hasSum a b c x
      (by simpa [norm_mul,ha] using hx)
      (by simpa [norm_mul,hb] using hx)
      (by simpa [norm_mul,hc] using hx)
  · exact lemma83_local_kappa_hasSum a b c t
      (by simpa [norm_mul,ha] using ht)
      (by simpa [norm_mul,hb] using ht)
      (by simpa [norm_mul,hc] using ht)
  · exact lemma83_local_kappa_shifted_double_summable a b c x t ha hb hc hx ht

end ZhangLS.Spec
