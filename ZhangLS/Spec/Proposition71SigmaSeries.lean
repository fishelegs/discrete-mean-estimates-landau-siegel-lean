import ZhangLS.Spec.Proposition71SigmaLargeLTail
import ZhangLS.Spec.Proposition71LocalizedSigmaSquare

/-! # The actual infinite σ series and exact finite localization bridge

The complementary term is a literal subseries. No residual is defined by
subtraction, and no estimate of that complement is assumed here.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

noncomputable def proposition71SigmaSeries {r : ℕ} (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) : ℂ :=
  ∑' l, proposition71SigmaTerm D c b a h d θ l

noncomputable def proposition71SigmaOffLocalTerm {r : ℕ} (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) (θ : DirichletCharacter ℂ r) (l : ℕ) : ℂ :=
  if l∈proposition71LocalizedIndices D R h then 0 else proposition71SigmaTerm D c b a h d θ l

noncomputable def proposition71SigmaOffLocalTail {r : ℕ} (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) (θ : DirichletCharacter ℂ r) : ℂ :=
  ∑' l, proposition71SigmaOffLocalTerm D c b a R h d θ l

lemma proposition71_tsum_finite_split {f : ℕ → ℂ} (hf : Summable f) (S : Finset ℕ) :
    (∑' n, f n)=(∑ n∈S, f n)+(∑' n, if n∈S then 0 else f n) := by
  have hh := hf.sum_add_tsum_compl (s := S)
  rw [_root_.tsum_subtype] at hh
  simpa only [Set.indicator,Set.mem_compl_iff,Finset.mem_coe,ite_not] using hh.symm

/-- The full actual series converges absolutely, by the proved infinite tail
and a genuinely finite head. -/
theorem proposition71_sigma_series_summable :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ {D r : ℕ} (θ : DirichletCharacter ℂ r),
      D₀≤D → 1<D → 2000≤lemma23PaperL D → ∀ c b B : ℝ, 0≤B →
        ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) → ∀ h d : ℕ, 0<h → 0<r →
          ((h*r : ℕ) : ℝ)≤lemma81Cutoff D →
            Summable (proposition71SigmaTerm D c b a h d θ) := by
  obtain ⟨D₀,hD₀,htail⟩ := proposition71_large_l_tail_bound
  refine ⟨D₀,hD₀,?_⟩
  intro D r θ hDN hD hL c b B hB a ha h d hh hr hcut
  have hs := (htail θ hDN hD hL c b B hB a ha h d hh hr hcut).1
  apply hs.congr_atTop
  apply eventually_atTop.mpr
  refine ⟨⌊lemma23PaperP D^2⌋₊+1,?_⟩
  intro l hl
  have hl' : lemma23PaperP D^2<(l : ℝ) := Nat.lt_of_floor_lt (by omega)
  simp only [proposition71SigmaLargeLTerm,if_pos hl']

lemma proposition71_sigma_local_finite_sum {D r : ℕ} (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) (θ : DirichletCharacter ℂ r) :
    (∑ l∈proposition71LocalizedIndices D R h, proposition71SigmaTerm D c b a h d θ l)=
      proposition71SigmaStar D c b a R h d θ := by
  unfold proposition71SigmaStar proposition71SigmaOnSet
  apply sum_congr rfl
  intro l hl
  have hm := proposition71_mem_localized_indices.mp hl
  simp only [proposition71SigmaTerm,if_pos (show 0<l ∧ l.Coprime h from ⟨hm.1,hm.2.2.2⟩)]

/-- Exact localization of the genuine infinite σ. The actual error subseries
retains every omitted l and every original coefficient/character/prime factor. -/
theorem proposition71_sigma_exact_localization {D r : ℕ} (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) (θ : DirichletCharacter ℂ r)
    (hs : Summable (proposition71SigmaTerm D c b a h d θ)) :
    proposition71SigmaSeries D c b a h d θ=
      proposition71SigmaStar D c b a R h d θ+
        proposition71SigmaOffLocalTail D c b a R h d θ := by
  have hh := proposition71_tsum_finite_split hs (proposition71LocalizedIndices D R h)
  rw [proposition71_sigma_local_finite_sum] at hh
  exact hh

end ZhangLS.Spec
