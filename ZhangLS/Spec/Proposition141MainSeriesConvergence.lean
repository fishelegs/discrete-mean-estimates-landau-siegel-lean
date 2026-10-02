import ZhangLS.Spec.Proposition141PrimeInfiniteTail

/-! # Absolute convergence of the original Section14 arithmetic main series

The whole Δ series converges because its literal large-index restriction is
summable and the complement is finite. Coprimality filtering and passage to
positive natural indices preserve that convergence. This validates the exact
infinite l-series in the original main term without changing its coefficients.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Filter Finset
open scoped Classical ComplexConjugate

/-- Every actual dilated character-Δ series is absolutely convergent. -/
theorem proposition141_dilated_delta_series_summable {D N : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (θ : DirichletCharacter ℂ N)
    {B : ℝ} (hB : 0≤B) {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ)
    {D₁ d : ℕ} (hD₁ : 0<D₁) (hd : 0<d) {q : ℝ} (hq : 0<q) :
    Summable (fun l:ℕ => κ (D₁*d*l)*θ (l:ZMod N)*lemma53PaperDelta D ((l:ℝ)/q)) := by
  let U := q*lemma51PaperT0 D^(51/50:ℝ)
  have hs := proposition141_dilated_delta_tail_summable hD hL θ hB hκ hD₁ hd hq (le_refl U)
  apply hs.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  refine eventually_atTop.mpr ⟨⌈U⌉₊+1,?_⟩
  intro l hl
  have hc := Nat.le_ceil U
  have hl' : (⌈U⌉₊:ℝ)+1≤(l:ℝ) := by exact_mod_cast hl
  have hlt : U<(l:ℝ) := by linarith
  simp only [proposition141DilatedDeltaTailTerm,if_pos hlt]

/-- Arbitrary coprimality restrictions are genuine indicators of the
absolutely convergent series, not new convergence assumptions. -/
theorem proposition141_coprime_delta_series_summable {D N : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (θ : DirichletCharacter ℂ N)
    {B : ℝ} (hB : 0≤B) {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ)
    {D₁ d : ℕ} (hD₁ : 0<D₁) (hd : 0<d) {q : ℝ} (hq : 0<q) (k : ℕ) :
    Summable (fun l:ℕ => if l.Coprime k then
      κ (D₁*d*l)*θ (l:ZMod N)*lemma53PaperDelta D ((l:ℝ)/q) else 0) := by
  have hs := proposition141_dilated_delta_series_summable hD hL θ hB hκ hD₁ hd hq
  apply (hs.indicator {l:ℕ | l.Coprime k}).congr
  intro l
  by_cases hc : l.Coprime k
  · rw [Set.indicator_of_mem (show l∈{l:ℕ | l.Coprime k} from hc),if_pos hc]
  · rw [Set.indicator_of_notMem (show l∉{l:ℕ | l.Coprime k} from hc),if_neg hc]

/-- Exactly the positive-index, coprimality-filtered infinite l-series
appearing in Proposition14.1's original main term is absolutely convergent. -/
theorem proposition141_original_main_series_summable {D p d k : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {B : ℝ} (hB : 0≤B) {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ)
    (hp : 0<p) (hd : 0<d) (hk : 0<k) :
    Summable (fun l:ℕ+ => if (l:ℕ).Coprime k then
      χ.chi ((l:ℕ):ZMod D)*κ (d*l)*
        lemma53PaperDelta D ((l:ℝ)/((D:ℝ)*p*k)) else 0) := by
  have hDp : 0<(D:ℝ) := by exact_mod_cast (by omega : 0<D)
  have hpp : 0<(p:ℝ) := by exact_mod_cast hp
  have hkp : 0<(k:ℝ) := by exact_mod_cast hk
  have hs := proposition141_coprime_delta_series_summable hD hL χ.chi hB hκ
    (D₁:=1) (by norm_num) hd (mul_pos (mul_pos hDp hpp) hkp) k
  have hsub := hs.subtype (fun l:ℕ => 0<l)
  simpa only [Function.comp_apply,one_mul,mul_comm (κ _) (χ.chi _)] using hsub

end ZhangLS.Spec
