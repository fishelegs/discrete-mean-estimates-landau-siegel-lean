import ZhangLS.Spec.Lemma32IntervalFourierCompletion
import Mathlib.Algebra.Field.GeomSum
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma32_std_add_character_norm {D : ℕ} [NeZero D] (k : ZMod D) :
    ‖ZMod.stdAddChar k‖=1 := by
  rw [ZMod.stdAddChar_apply]
  simp

lemma lemma32_fourier_interval_geometric_sum {D : ℕ} [NeZero D]
    (M : ℤ) (N : ℕ) (k : ZMod D) :
    lemma32FourierIntervalKernel D M N k =
      ZMod.stdAddChar (k*(M : ZMod D))*
        (∑ n ∈ Finset.range N, (ZMod.stdAddChar k)^n) := by
  unfold lemma32FourierIntervalKernel
  rw [Fin.sum_univ_eq_sum_range
    (fun n => ZMod.stdAddChar (k*(((M+(n : ℤ)) : ℤ) : ZMod D))) N]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he : k*(((M+(n : ℤ)) : ℤ) : ZMod D) = k*(M : ZMod D)+n•k := by
    push_cast
    rw [nsmul_eq_mul]
    ring
  rw [he, AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]

lemma lemma32_fourier_geometric_kernel_norm_product {D : ℕ} [NeZero D]
    (M : ℤ) (N : ℕ) (k : ZMod D) :
    ‖lemma32FourierIntervalKernel D M N k‖*‖ZMod.stdAddChar k-1‖ ≤ 2 := by
  rw [lemma32_fourier_interval_geometric_sum, norm_mul,
    lemma32_std_add_character_norm, one_mul, ← norm_mul, geom_sum_mul]
  calc
    _ ≤ ‖(ZMod.stdAddChar k)^N‖+‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, lemma32_std_add_character_norm, one_pow, norm_one];norm_num

lemma lemma32_fourier_geometric_kernel_norm_bound {D : ℕ} [NeZero D]
    (M : ℤ) (N : ℕ) {k : ZMod D} (hk : k≠0) :
    ‖lemma32FourierIntervalKernel D M N k‖ ≤ 2/‖ZMod.stdAddChar k-1‖ := by
  have hne : ZMod.stdAddChar k≠1 := by
    intro he
    apply hk
    apply ZMod.injective_stdAddChar
    simpa using he
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).mpr
  exact lemma32_fourier_geometric_kernel_norm_product M N k

end ZhangLS.Spec
