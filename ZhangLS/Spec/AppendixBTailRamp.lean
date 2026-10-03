import ZhangLS.Spec.AppendixBTailSupport
import ZhangLS.Spec.Lemma84LogPerronKernel

/-! Exact algebra behind the strict lower truncation. The monomial cutoff
has strict support; its endpoint therefore belongs to the complementary tail. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex
open scoped Classical

noncomputable def appendixBStrictMonomial (X Y : ℝ) (γ : ℂ) (n : ℕ) : ℂ :=
  if 0<n ∧ (n : ℝ)<Y then ((X/n : ℝ) : ℂ)^γ else 0

lemma appendixB_positive_cpow_split {X Y : ℝ} (hX : 0<X) (hY : 0<Y)
    {n : ℕ} (hn : 0<n) (γ : ℂ) :
    ((X/Y : ℝ) : ℂ)^γ*((Y/n : ℝ) : ℂ)^γ=((X/n : ℝ) : ℂ)^γ := by
  have hnr : 0<(n : ℝ) := Nat.cast_pos.mpr hn
  rw [lemma84_positive_cpow_eq_exp (div_pos hX hY),
    lemma84_positive_cpow_eq_exp (div_pos hY hnr),
    lemma84_positive_cpow_eq_exp (div_pos hX hnr),←exp_add]
  simp only [Real.log_div hX.ne' hY.ne',Real.log_div hY.ne' hnr.ne',
    Real.log_div hX.ne' hnr.ne']
  congr 1
  push_cast
  ring

/-- Truncated X-ramp equals a scaled Y-ramp plus the strict monomial cutoff.
This retains both logarithmic normalizers exactly. -/
theorem appendixB_truncated_ramp_identity {X Y : ℝ} (hY : 1<Y) (hYX : Y≤X)
    (γ : ℂ) (n : ℕ) :
    appendixBTruncatedKernel X Y γ n =
      ((Real.log Y/Real.log X : ℝ) : ℂ)*((X/Y : ℝ) : ℂ)^γ*
        lemma151Kernel Y γ n+
      (((Real.log X-Real.log Y)/Real.log X : ℝ) : ℂ)*
        appendixBStrictMonomial X Y γ n := by
  have hXp : 0<X := (zero_lt_one.trans hY).trans_le hYX
  have hYp : 0<Y := zero_lt_one.trans hY
  have hX1 : 1<X := hY.trans_le hYX
  have hlX : (Real.log X : ℂ)≠0 := ofReal_ne_zero.mpr (Real.log_pos hX1).ne'
  have hlY : (Real.log Y : ℂ)≠0 := ofReal_ne_zero.mpr (Real.log_pos hY).ne'
  by_cases hn : 0<n
  · by_cases hcut : (n : ℝ)<Y
    · have hcutX : (n : ℝ)<X := hcut.trans_le hYX
      have hpow := appendixB_positive_cpow_split hXp hYp hn γ
      have hcondX : 0<n ∧ (n : ℝ)<X := ⟨hn,hcutX⟩
      have hcondY : 0<n ∧ (n : ℝ)<Y := ⟨hn,hcut⟩
      simp only [appendixBTruncatedKernel,if_pos hcut,lemma151Kernel,
        if_pos hcondX,if_pos hcondY,appendixBStrictMonomial]
      have he : ((Real.log Y/Real.log X : ℝ) : ℂ)*((X/Y : ℝ) : ℂ)^γ*
          ((1-(Real.log (n : ℝ)/Real.log Y : ℂ))*((Y/n : ℝ) : ℂ)^γ) =
          ((Real.log Y/Real.log X : ℝ) : ℂ)*
            (1-(Real.log (n : ℝ)/Real.log Y : ℂ))*((X/n : ℝ) : ℂ)^γ := by
        rw [←hpow]
        ring
      rw [he]
      push_cast
      field_simp [hlX,hlY]
      <;> ring
    · simp [appendixBTruncatedKernel,appendixBStrictMonomial,lemma151Kernel,hcut]
  · have hn0 : n=0 := by omega
    simp [hn0,appendixBTruncatedKernel,appendixBStrictMonomial,lemma151Kernel]

/-- Exact complementary ramp expression. At n=Y both subtracted terms vanish. -/
theorem appendixB_complement_ramp_identity {X Y : ℝ} (hY : 1<Y) (hYX : Y≤X)
    (γ : ℂ) (n : ℕ) :
    appendixBComplementKernel X Y γ n = lemma151Kernel X γ n-
      ((Real.log Y/Real.log X : ℝ) : ℂ)*((X/Y : ℝ) : ℂ)^γ*
        lemma151Kernel Y γ n-
      (((Real.log X-Real.log Y)/Real.log X : ℝ) : ℂ)*
        appendixBStrictMonomial X Y γ n := by
  have hp := appendixB_kernel_exact_partition X Y γ n
  rw [appendixB_truncated_ramp_identity hY hYX γ n] at hp
  linear_combination -hp

lemma appendixB_monomial_excludes_equality (X Y : ℝ) (γ : ℂ) {n : ℕ}
    (hn : (n : ℝ)=Y) : appendixBStrictMonomial X Y γ n=0 := by
  simp [appendixBStrictMonomial,hn]

end ZhangLS.Spec
