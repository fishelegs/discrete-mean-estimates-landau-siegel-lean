import ZhangLS.Spec.Proposition71NatMultiples
import ZhangLS.Spec.Proposition71DeltaOneAbsolute

/-! # Exact reindexing and bound for the p-divisible long Δ₁ branch

The missing branch is reindexed as m=p*l, including m=0 and l=0 explicitly.
The resulting scale is n, not pn, and the genuine divisor factor τ₅(p) is kept.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71DivisibleDeltaTerm (D p n : ℕ) (κ : ℕ → ℂ) (m : ℕ) : ℂ :=
  if p∣m then if 0<m then κ m*lemma53PaperDeltaOne D ((m : ℝ)/((p : ℝ)*(n : ℝ))) else 0 else 0

lemma proposition71_divisible_delta_reindexed {p n : ℕ} (hp : 0<p) (hn : 0<n)
    (D : ℕ) (κ : ℕ → ℂ) (l : ℕ) :
    (if 0<p*l then κ (p*l)*lemma53PaperDeltaOne D (((p*l : ℕ) : ℝ)/((p : ℝ)*(n : ℝ))) else 0)=
      proposition71DeltaOneDilatedTerm D κ (fun _ => 1) p (n : ℝ) l := by
  have hpr : (p : ℝ)≠0 := by exact_mod_cast hp.ne'
  have hnr : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  by_cases hl : 0<l
  · rw [if_pos (Nat.mul_pos hp hl),proposition71DeltaOneDilatedTerm,if_pos hl,mul_one]
    congr 2
    push_cast
    field_simp
  · have hl0 : l=0 := by omega
    subst l
    simp [proposition71DeltaOneDilatedTerm]

/-- The full restoration branch is genuinely absolutely convergent and costs
τ₅(p)·n·L^575, rather than the incorrect pn-scale bound without sparsity. -/
theorem proposition71_divisible_delta_branch_bound {D p n : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hp : 0<p) (hn : 0<n)
    (hnP : (n : ℝ)≤lemma23PaperP D^10) (κ : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀m : ℕ, 0<m → ‖κ m‖≤B*(lemma34Tau 5 m : ℝ)) :
    Summable (proposition71DivisibleDeltaTerm D p n κ) ∧
      ‖∑'m, proposition71DivisibleDeltaTerm D p n κ m‖≤
        tauDeltaAbsoluteConstant*B*(lemma34Tau 5 p : ℝ)*(n : ℝ)*lemma23PaperL D^575 := by
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
  have hb := proposition71_delta_one_dilated_absolute_bound hD hL κ (fun _ => 1) hB (by norm_num : (0 : ℝ)≤1)
    hκ (by intro m hm; simp) hp hn1 hnP
  have he : (fun l : ℕ => if 0<p*l then κ (p*l)*lemma53PaperDeltaOne D (((p*l : ℕ) : ℝ)/((p : ℝ)*(n : ℝ))) else 0)=
      proposition71DeltaOneDilatedTerm D κ (fun _ => 1) p (n : ℝ) :=
    funext (proposition71_divisible_delta_reindexed hp hn D κ)
  have hs : Summable (proposition71DivisibleDeltaTerm D p n κ) := by
    unfold proposition71DivisibleDeltaTerm
    rw [proposition71_nat_multiples_summable_iff hp,he]
    exact hb.1
  refine ⟨hs,?_⟩
  unfold proposition71DivisibleDeltaTerm
  rw [proposition71_nat_multiples_tsum hp,he]
  exact (norm_tsum_le_tsum_norm hb.1.norm).trans (by simpa only [one_mul] using hb.2)

end ZhangLS.Spec
