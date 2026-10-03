import ZhangLS.Spec.AppendixBKernelPerronBridge
import ZhangLS.Spec.BSourceKernels
import ZhangLS.Spec.Lemma151TailIntegral

/-! The exact complementary tail of the source H14, including equality. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical

noncomputable def appendixBTruncatedKernel (X Y : ℝ) (γ : ℂ) (n : ℕ) : ℂ :=
  if (n : ℝ)<Y then lemma151Kernel X γ n else 0

noncomputable def appendixBComplementKernel (X Y : ℝ) (γ : ℂ) (n : ℕ) : ℂ :=
  if Y≤(n : ℝ) then lemma151Kernel X γ n else 0

lemma appendixB_kernel_exact_partition (X Y : ℝ) (γ : ℂ) (n : ℕ) :
    lemma151Kernel X γ n = appendixBTruncatedKernel X Y γ n +
      appendixBComplementKernel X Y γ n := by
  by_cases h : (n : ℝ)<Y
  · simp [appendixBTruncatedKernel,appendixBComplementKernel,h,not_le.mpr h]
  · simp [appendixBTruncatedKernel,appendixBComplementKernel,h,le_of_not_gt h]

lemma appendixB_h14_is_actual_truncation (D n : ℕ) :
    bH14Coefficient D n = appendixBTruncatedKernel (lemma151P1 D)
      ((lemma23PaperP D)^(1/2 : ℝ)) (lemma151Beta6 D) n := rfl

lemma appendixB_tail_includes_equality {X Y : ℝ} (γ : ℂ) {n : ℕ}
    (hn : (n : ℝ)=Y) :
    appendixBComplementKernel X Y γ n=lemma151Kernel X γ n ∧
      appendixBTruncatedKernel X Y γ n=0 := by
  simp [appendixBComplementKernel,appendixBTruncatedKernel,hn]

lemma appendixB_complement_zero_below {X Y : ℝ} (γ : ℂ) {n : ℕ}
    (hn : (n : ℝ)<Y) : appendixBComplementKernel X Y γ n=0 := by
  simp [appendixBComplementKernel,not_le.mpr hn]

lemma appendixB_complement_zero_at_or_above {X Y : ℝ} (γ : ℂ) {n : ℕ}
    (hn : X≤(n : ℝ)) : appendixBComplementKernel X Y γ n=0 := by
  simp [appendixBComplementKernel,lemma151Kernel,not_lt.mpr hn]

lemma appendixB_shifted_kernel_support {X : ℝ} (γ : ℂ) {l₁ : ℕ} (hl : 0<l₁)
    (w : ℕ→ℂ) : BStrictSupport X
      (fun n => lemma151Kernel X γ (l₁*n)*w n) := by
  intro n hn
  obtain ⟨hprod,hcut⟩ := b_kernel_strict_support X γ (l₁*n) (left_ne_zero_of_mul hn)
  have hn0 : 0<n := Nat.pos_of_mul_pos_left hprod
  have hle : n≤l₁*n := Nat.le_mul_of_pos_left n hl
  exact ⟨hn0,(show (n : ℝ)≤((l₁*n : ℕ) : ℝ) by exact_mod_cast hle).trans_lt hcut⟩

lemma appendixB_shifted_kernel_summable {X : ℝ} (γ : ℂ) {l₁ : ℕ} (hl : 0<l₁)
    (w : ℕ→ℂ) : Summable (fun n => lemma151Kernel X γ (l₁*n)*w n) :=
  summable_of_ne_finset_zero (s := Finset.Icc 1 ⌈X⌉₊) (fun n hn => by
    by_contra hne
    exact hn (b_strict_support_mem (appendixB_shifted_kernel_support γ hl w) hne))

noncomputable def appendixBTruncatedKernelSum (X Y : ℝ) (β γ : ℂ) (l₁ : ℕ) : ℂ :=
  ∑' n : ℕ, appendixBTruncatedKernel X Y γ (l₁*n)*lemma151Rho β n/n

noncomputable def appendixBComplementKernelSum (X Y : ℝ) (β γ : ℂ) (l₁ : ℕ) : ℂ :=
  ∑' n : ℕ, appendixBComplementKernel X Y γ (l₁*n)*lemma151Rho β n/n

lemma appendixB_truncated_terms_summable (X Y : ℝ) (β γ : ℂ) {l₁ : ℕ}
    (hl : 0<l₁) : Summable (fun n : ℕ =>
      appendixBTruncatedKernel X Y γ (l₁*n)*lemma151Rho β n/n) := by
  have hs := appendixB_shifted_kernel_summable (X := X) γ hl
    (fun n => if ((l₁*n : ℕ) : ℝ)<Y then lemma151Rho β n/n else 0)
  apply hs.congr
  intro n
  unfold appendixBTruncatedKernel
  split_ifs <;> ring

lemma appendixB_complement_terms_summable (X Y : ℝ) (β γ : ℂ) {l₁ : ℕ}
    (hl : 0<l₁) : Summable (fun n : ℕ =>
      appendixBComplementKernel X Y γ (l₁*n)*lemma151Rho β n/n) := by
  have hs := appendixB_shifted_kernel_summable (X := X) γ hl
    (fun n => if Y≤((l₁*n : ℕ) : ℝ) then lemma151Rho β n/n else 0)
  apply hs.congr
  intro n
  unfold appendixBComplementKernel
  split_ifs <;> ring

/-- Exact splitting, with both summability proofs and no endpoint convention hidden. -/
theorem appendixB_full_eq_h14_add_complement (X Y : ℝ) (β γ : ℂ)
    {l₁ : ℕ} (hl : 0<l₁) :
    appendixBFullKernelSum X β γ l₁ = appendixBTruncatedKernelSum X Y β γ l₁+
      appendixBComplementKernelSum X Y β γ l₁ := by
  unfold appendixBFullKernelSum appendixBTruncatedKernelSum appendixBComplementKernelSum
  rw [←(appendixB_truncated_terms_summable X Y β γ hl).tsum_add
    (appendixB_complement_terms_summable X Y β γ hl)]
  apply tsum_congr
  intro n
  rw [appendixB_kernel_exact_partition X Y γ (l₁*n)]
  ring

/-- True H14 is full P1 minus the complementary tail, never full P1 alone. -/
theorem appendixB_actual_h14_sum (D : ℕ) (β : ℂ) {l₁ : ℕ} (hl : 0<l₁) :
    (∑' n : ℕ, bH14Coefficient D (l₁*n)*lemma151Rho β n/n) =
      appendixBFullKernelSum (lemma151P1 D) β (lemma151Beta6 D) l₁-
      appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ))
        β (lemma151Beta6 D) l₁ := by
  have hh := appendixB_full_eq_h14_add_complement (lemma151P1 D)
    ((lemma23PaperP D)^(1/2 : ℝ)) β (lemma151Beta6 D) hl
  rw [hh,add_sub_cancel_right]
  rfl

end ZhangLS.Spec
