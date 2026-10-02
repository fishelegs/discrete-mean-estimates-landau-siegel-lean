import ZhangLS.Spec.Lemma153WeightedKernel
/-! Remove the artificial divided-difference singularity x=χ(q)/q in the
actual supported κ₁-tail series. This includes χ(q)=1 at zero shifts. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma153TailClosed (a b x t : ℂ) : ℂ :=
  (1-x-t+(a+b-a*b)*x*t)/((1-a*x)*(1-b*x)*(1-a*t)*(1-b*t))

lemma lemma153_weighted_kappa_hasSum (a b x : ℂ)
    (ha : ‖a*x‖ < 1) (hb : ‖b*x‖ < 1) :
    HasSum (fun n : ℕ => ((n:ℂ)+1)*lemma152LocalKappa a b n*x^n)
      ((1-x)*(1-a*b*x^2)/((1-a*x)^2*(1-b*x)^2) -
        x/((1-a*x)*(1-b*x))) := by
  let W := (1-a*b*x^2)/((1-a*x)^2*(1-b*x)^2)
  let H := (1-a*x)⁻¹*(1-b*x)⁻¹
  have hw : HasSum (fun n : ℕ => ((n:ℂ)+1)*lemma83LocalH2 a b n*x^n) W :=
    lemma153_weighted_h2_hasSum a b x ha hb
  have hh : HasSum (fun n : ℕ => lemma83LocalH2 a b n*x^n) H :=
    lemma83_local_h2_hasSum a b x ha hb
  have hwt : HasSum (fun n : ℕ => (((n+1:ℕ):ℂ)+1)*lemma83LocalH2 a b (n+1)*x^(n+1))
      (W-1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hw
  have hkt : HasSum (fun n : ℕ => (((n+1:ℕ):ℂ)+1)*lemma152LocalKappa a b (n+1)*x^(n+1))
      (W-1-x*(W+H)) := by
    convert hwt.sub ((hw.add hh).mul_left x) using 1
    funext n
    rw [lemma152_local_kappa_succ,pow_succ]
    push_cast
    ring
  convert (hasSum_nat_add_iff (f := fun n : ℕ => ((n:ℂ)+1)*lemma152LocalKappa a b n*x^n) 1).mp hkt using 1
  simp only [sum_range_succ,sum_range_zero,pow_zero,lemma152_local_kappa_zero,
    Nat.cast_zero,zero_add,one_mul,mul_one]
  dsimp [W,H]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma lemma153_diagonal_antidiagonal (t : ℂ) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, t^ij.1*t^ij.2) = ((n:ℂ)+1)*t^n := by
  calc
    _ = ∑ ij ∈ antidiagonal n, t^n := by
      apply sum_congr rfl
      intro ij hij
      rw [← pow_add,mem_antidiagonal.mp hij]
    _ = _ := by simp

lemma lemma153_tail_diagonal_hasSum (a b t : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (ht : ‖t‖ < 1) :
    HasSum (fun r : ℕ => (∑' k : ℕ, lemma152LocalKappa a b (r+k)*t^k)*t^r)
      (lemma153TailClosed a b t t) := by
  have hd := lemma152_local_kappa_double_summable a b t t ha hb ht ht
  have hsum := lemma83_shifted_double_tsum_eq (lemma152LocalKappa a b) t t hd
  have ho : Summable (fun r : ℕ => (∑' k : ℕ, lemma152LocalKappa a b (r+k)*t^k)*t^r) := by
    convert hd.prod using 1
    funext r
    rw [← tsum_mul_right]
    apply tsum_congr
    intro k
    ring
  have hat : ‖a*t‖ < 1 := by simpa [norm_mul,ha] using ht
  have hbt : ‖b*t‖ < 1 := by simpa [norm_mul,hb] using ht
  have hw := lemma153_weighted_kappa_hasSum a b t hat hbt
  convert ho.hasSum using 1
  calc
    lemma153TailClosed a b t t =
        (1-t)*(1-a*b*t^2)/((1-a*t)^2*(1-b*t)^2)-t/((1-a*t)*(1-b*t)) := by
      have ha' := lemma83_one_sub_ne_zero hat
      have hb' := lemma83_one_sub_ne_zero hbt
      unfold lemma153TailClosed
      field_simp
      ring
    _ = ∑' n : ℕ, ((n:ℂ)+1)*lemma152LocalKappa a b n*t^n := hw.tsum_eq.symm
    _ = ∑' n : ℕ, lemma152LocalKappa a b n*(∑ ij ∈ antidiagonal n, t^ij.1*t^ij.2) := by
      apply tsum_congr
      intro n
      rw [lemma153_diagonal_antidiagonal]
      ring
    _ = ∑' r : ℕ, ∑' k : ℕ, lemma152LocalKappa a b (r+k)*t^r*t^k := hsum.symm
    _ = ∑' r : ℕ, (∑' k : ℕ, lemma152LocalKappa a b (r+k)*t^k)*t^r := by
      apply tsum_congr
      intro r
      rw [← tsum_mul_right]
      apply tsum_congr
      intro k
      ring

/-- The exact actual tail series has a regular rational value on the whole
unit bidisc. There is no off-diagonal hypothesis. -/
lemma lemma153_tail_closed_hasSum (a b x t : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) :
    HasSum (fun r : ℕ => (∑' k : ℕ, lemma152LocalKappa a b (r+k)*t^k)*x^r)
      (lemma153TailClosed a b x t) := by
  by_cases hxt : x = t
  · subst x
    exact lemma153_tail_diagonal_hasSum a b t ha hb ht
  · convert lemma152_local_kappa_tail_hasSum a b x t ha hb hx ht hxt using 1
    have hax : 1-a*x ≠ 0 := lemma83_one_sub_ne_zero (by simpa [norm_mul,ha] using hx)
    have hbx : 1-b*x ≠ 0 := lemma83_one_sub_ne_zero (by simpa [norm_mul,hb] using hx)
    have hat : 1-a*t ≠ 0 := lemma83_one_sub_ne_zero (by simpa [norm_mul,ha] using ht)
    have hbt : 1-b*t ≠ 0 := lemma83_one_sub_ne_zero (by simpa [norm_mul,hb] using ht)
    have hxt' := sub_ne_zero.mpr hxt
    unfold lemma153TailClosed lemma152KappaRational
    repeat' field_simp [hax,hbx,hat,hbt,hxt',mul_comm]
    all_goals ring

end ZhangLS.Spec
