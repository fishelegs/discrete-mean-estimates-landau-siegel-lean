import ZhangLS.Spec.Lemma83ZeroShift
import ZhangLS.Spec.Lemma83FinitePrimeBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

/-- Absolute product perturbation; it remains valid when some factors vanish. -/
lemma lemma83_product_perturbation {ι : Type*} (S : Finset ι)
    (f g : ι → ℂ) (w e : ι → ℝ)
    (hw : ∀ i ∈ S, 1 ≤ w i) (hf : ∀ i ∈ S, ‖f i‖ ≤ w i)
    (hg : ∀ i ∈ S, ‖g i‖ ≤ w i) (he : ∀ i ∈ S, ‖f i-g i‖ ≤ e i) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ (∏ i ∈ S, w i) * ∑ i ∈ S, e i := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hwS : ∀ i ∈ S, 1 ≤ w i := fun i hi => hw i (mem_insert_of_mem hi)
    have hfS : ∀ i ∈ S, ‖f i‖ ≤ w i := fun i hi => hf i (mem_insert_of_mem hi)
    have hgS : ∀ i ∈ S, ‖g i‖ ≤ w i := fun i hi => hg i (mem_insert_of_mem hi)
    have heS : ∀ i ∈ S, ‖f i-g i‖ ≤ e i := fun i hi => he i (mem_insert_of_mem hi)
    have haS := mem_insert_self a S
    have hw0 : 0 ≤ ∏ i ∈ S, w i := prod_nonneg (fun i hi => (zero_le_one.trans (hwS i hi)))
    have he0 : 0 ≤ e a := (norm_nonneg _).trans (he a haS)
    have hes0 : 0 ≤ ∑ i ∈ S, e i := sum_nonneg (fun i hi => (norm_nonneg _).trans (heS i hi))
    have hpf : ‖∏ i ∈ S, f i‖ ≤ ∏ i ∈ S, w i := by
      rw [norm_prod]
      exact prod_le_prod (fun _ _ => norm_nonneg _) hfS
    rw [prod_insert ha,prod_insert ha,prod_insert ha,sum_insert ha]
    calc
      _ = ‖(f a-g a)*(∏ i ∈ S, f i) + g a*((∏ i ∈ S, f i)-(∏ i ∈ S, g i))‖ := by
        congr 1
        ring
      _ ≤ ‖f a-g a‖*‖∏ i ∈ S, f i‖ + ‖g a‖*‖(∏ i ∈ S, f i)-(∏ i ∈ S, g i)‖ := by
        simpa only [norm_mul] using norm_add_le
          ((f a-g a)*(∏ i ∈ S, f i)) (g a*((∏ i ∈ S, f i)-(∏ i ∈ S, g i)))
      _ ≤ e a*(∏ i ∈ S, w i) + w a*((∏ i ∈ S, w i)*∑ i ∈ S, e i) := by
        exact add_le_add (mul_le_mul (he a haS) hpf (norm_nonneg _) he0)
          (mul_le_mul (hg a haS) (ih hwS hfS hgS heS) (norm_nonneg _)
            (zero_le_one.trans (hw a haS)))
      _ ≤ _ := by nlinarith [mul_nonneg he0 hw0,hw a haS]

/-- A global exponential perturbation inequality, with no small-argument restriction. -/
lemma lemma83_exp_sub_one_bound (z : ℂ) :
    ‖Complex.exp z-1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp z 1

/-- The prime monomial has the exact normalization q⁻¹ at s=1. -/
lemma lemma83_monomial_near_one {q : ℕ} (hq : 0 < q) (w : ℂ) :
    ‖lemma32PrimeMonomial q (1+w) - (q:ℂ)⁻¹‖ ≤
      (q:ℝ)⁻¹ * (‖w‖*Real.log q) * Real.exp (‖w‖*Real.log q) := by
  have hl : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hn : ‖-(w*(Real.log q:ℂ))‖ = ‖w‖*Real.log q := by
    rw [norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl]
  have he : lemma32PrimeMonomial q (1+w) - (q:ℂ)⁻¹ =
      (q:ℂ)⁻¹ * (Complex.exp (-(w*(Real.log q:ℂ)))-1) := by
    rw [← lemma83_prime_monomial_one hq]
    unfold lemma32PrimeMonomial
    rw [mul_sub, mul_one,← Complex.exp_add]
    congr 2
    ring
  rw [he,norm_mul,norm_inv,Complex.norm_natCast]
  have hb := lemma83_exp_sub_one_bound (-(w*(Real.log q:ℂ)))
  rw [hn] at hb
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (q:ℝ)⁻¹)

end ZhangLS.Spec
