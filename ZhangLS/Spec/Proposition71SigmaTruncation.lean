import ZhangLS.Spec.Proposition71SigmaSeries
import ZhangLS.Spec.Proposition71SmallSigma

/-! # Exact P² truncation of the genuine infinite σ series -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_mem_sigma_truncation {D l h : ℕ} :
    l∈(Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun l => l.Coprime h) ↔
      0<l ∧ (l : ℝ)≤lemma23PaperP D^2 ∧ l.Coprime h := by
  simp only [mem_filter,mem_Icc,Nat.le_floor_iff (sq_nonneg (lemma23PaperP D))]
  tauto

lemma proposition71_sigma_truncated_finite_sum {D r : ℕ} (c b : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) :
    (∑ l∈(Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun l => l.Coprime h),
      proposition71SigmaTerm D c b a h d θ l)=proposition71SigmaTruncated D c b a h d θ := by
  unfold proposition71SigmaTruncated
  apply sum_congr rfl
  intro l hl
  have hm := proposition71_mem_sigma_truncation.mp hl
  simp only [proposition71SigmaTerm,if_pos (show 0<l ∧ l.Coprime h from ⟨hm.1,hm.2.2⟩)]

lemma proposition71_sigma_truncation_complement {D r : ℕ} (c b : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) (l : ℕ) :
    (if l∈(Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun l => l.Coprime h)
      then 0 else proposition71SigmaTerm D c b a h d θ l)=
        proposition71SigmaLargeLTerm D c b a h d θ l := by
  simp only [proposition71_mem_sigma_truncation]
  by_cases he : 0<l ∧ l.Coprime h
  · by_cases hl : lemma23PaperP D^2<(l : ℝ)
    · simp [he.1,he.2,not_le.mpr hl,proposition71SigmaLargeLTerm,hl]
    · have hl' : (l : ℝ)≤lemma23PaperP D^2 := le_of_not_gt hl
      simp [he.1,he.2,hl',proposition71SigmaLargeLTerm,hl]
  · have hz : proposition71SigmaTerm D c b a h d θ l=0 := by simp only [proposition71SigmaTerm,if_neg he]
    simp [hz,proposition71SigmaLargeLTerm]

/-- The tail is the actual omitted infinite subseries, not a residual. -/
theorem proposition71_sigma_exact_truncation {D r : ℕ} (c b : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r)
    (hs : Summable (proposition71SigmaTerm D c b a h d θ)) :
    proposition71SigmaSeries D c b a h d θ=
      proposition71SigmaTruncated D c b a h d θ+proposition71SigmaLargeLTail D c b a h d θ := by
  have hh := proposition71_tsum_finite_split hs ((Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun l => l.Coprime h))
  simp only [proposition71_sigma_truncated_finite_sum,proposition71_sigma_truncation_complement] at hh
  exact hh

end ZhangLS.Spec
