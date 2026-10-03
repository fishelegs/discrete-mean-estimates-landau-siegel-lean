import ZhangLS.Spec.Proposition71CharacterSplit
import ZhangLS.Spec.Proposition71PositiveNatSeries

/-! Absolute convergence and exact summation of the literal character split.
The long series has the actual dilated coefficient kappa(d*l); no tau5(d)
factor is dropped, and all Delta scales stay in the proved range. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate
set_option maxHeartbeats 3000000

/-- Arbitrary bounded weights on the true positive-index dilated Delta fiber. -/
lemma proposition71_positive_delta_fiber_summable {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (κ w : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀n : ℕ, 0<n → ‖κ n‖≤B*(lemma34Tau 5 n : ℝ))
    (hw : ∀n : ℕ, 0<n → ‖w n‖≤1) {d : ℕ} (hd : 0<d) {q : ℝ}
    (hq : 1≤q) (hqP : q≤lemma23PaperP D^10) :
    Summable (fun l : ℕ+ => κ (d*(l : ℕ))*w (l : ℕ)*lemma53PaperDelta D ((l : ℝ)/q)) := by
  have hs := (tauDelta_actual_dilated_character_sum hD hL κ w hB hκ hw hd hq hqP).1
  have hh := proposition71_positive_nat_summable _ hs
  exact hh.congr (fun l => by simp [tauDeltaDilatedTerm])

noncomputable def proposition71PrincipalDeltaFiber (D d k : ℕ) (q : ℝ) (κ : ℕ → ℂ) : ℂ :=
  ∑'l : ℕ+, if Nat.Coprime (l : ℕ) k then
    κ (d*(l : ℕ))*lemma53PaperDelta D ((l : ℝ)/q) else 0

noncomputable def proposition71CharacterDeltaFiber {k : ℕ}
    (D d : ℕ) (q : ℝ) (κ : ℕ → ℂ) (θ : DirichletCharacter ℂ k) : ℂ :=
  ∑'l : ℕ+, κ (d*(l : ℕ))*θ (-(l : ZMod k))*lemma53PaperDelta D ((l : ℝ)/q)

lemma proposition71_principal_delta_fiber_summable {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (κ : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀n : ℕ, 0<n → ‖κ n‖≤B*(lemma34Tau 5 n : ℝ))
    {d : ℕ} (hd : 0<d) (k : ℕ) {q : ℝ} (hq : 1≤q) (hqP : q≤lemma23PaperP D^10) :
    Summable (fun l : ℕ+ => if Nat.Coprime (l : ℕ) k then
      κ (d*(l : ℕ))*lemma53PaperDelta D ((l : ℝ)/q) else 0) := by
  have hs := proposition71_positive_delta_fiber_summable hD hL κ
    (fun l => if l.Coprime k then 1 else 0) hB hκ
    (fun l hl => by dsimp only; split_ifs <;> norm_num) hd hq hqP
  exact hs.congr (fun l => by split_ifs <;> simp_all)

lemma proposition71_character_delta_fiber_summable {D k : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (κ : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀n : ℕ, 0<n → ‖κ n‖≤B*(lemma34Tau 5 n : ℝ))
    {d : ℕ} (hd : 0<d) (θ : DirichletCharacter ℂ k)
    {q : ℝ} (hq : 1≤q) (hqP : q≤lemma23PaperP D^10) :
    Summable (fun l : ℕ+ => κ (d*(l : ℕ))*θ (-(l : ZMod k))*lemma53PaperDelta D ((l : ℝ)/q)) :=
  proposition71_positive_delta_fiber_summable hD hL κ (fun l => θ (-(l : ZMod k)))
    hB hκ (fun l hl => θ.norm_le_one _) hd hq hqP

/-- Exact infinite-series (7.9) split; all characters are genuine and every
infinite/finite interchange follows from the proved absolute fibers. -/
theorem proposition71_reciprocal_fiber_split {D k : ℕ} [NeZero k]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {p : ℕ} (hp : p.Coprime k)
    (κ : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀n : ℕ, 0<n → ‖κ n‖≤B*(lemma34Tau 5 n : ℝ))
    {d : ℕ} (hd : 0<d) {q : ℝ} (hq : 1≤q) (hqP : q≤lemma23PaperP D^10) :
    (∑'l : ℕ+, if Nat.Coprime (l : ℕ) k then
      κ (d*(l : ℕ))*deltaReciprocalWeight p (l : ℕ) k*lemma53PaperDelta D ((l : ℝ)/q) else 0)=
      ((ArithmeticFunction.moebius k : ℂ)/(k.totient : ℂ))*proposition71PrincipalDeltaFiber D d k q κ+
      (k.totient : ℂ)⁻¹*∑θ∈(univ : Finset (DirichletCharacter ℂ k)).erase 1,
        gaussSum θ⁻¹ ZMod.stdAddChar*conj (θ (p : ZMod k))*proposition71CharacterDeltaFiber D d q κ θ := by
  let f := fun l : ℕ+ => if Nat.Coprime (l : ℕ) k then
    κ (d*(l : ℕ))*lemma53PaperDelta D ((l : ℝ)/q) else 0
  let g := fun (θ : DirichletCharacter ℂ k) (l : ℕ+) =>
    κ (d*(l : ℕ))*θ (-(l : ZMod k))*lemma53PaperDelta D ((l : ℝ)/q)
  let C := fun θ : DirichletCharacter ℂ k => gaussSum θ⁻¹ ZMod.stdAddChar*conj (θ (p : ZMod k))
  have hf : Summable f := proposition71_principal_delta_fiber_summable hD hL κ hB hκ hd k hq hqP
  have hg (θ : DirichletCharacter ℂ k) : Summable (g θ) :=
    proposition71_character_delta_fiber_summable hD hL κ hB hκ hd θ hq hqP
  have hgSum := hasSum_sum (s := (univ : Finset (DirichletCharacter ℂ k)).erase 1)
    (fun θ hθ => (hg θ).hasSum.mul_left (C θ))
  have htotal := (hf.hasSum.mul_left ((ArithmeticFunction.moebius k : ℂ)/(k.totient : ℂ))).add
    (hgSum.mul_left (k.totient : ℂ)⁻¹)
  have hpoint (l : ℕ+) :
      (ArithmeticFunction.moebius k : ℂ)/(k.totient : ℂ)*f l+
        (k.totient : ℂ)⁻¹*∑θ∈(univ : Finset (DirichletCharacter ℂ k)).erase 1,C θ*g θ l=
      if Nat.Coprime (l : ℕ) k then
        κ (d*(l : ℕ))*deltaReciprocalWeight p (l : ℕ) k*lemma53PaperDelta D ((l : ℝ)/q) else 0 := by
    have hs := proposition71_reciprocal_filtered_split (l := (l : ℕ)) hp (κ (d*(l : ℕ))*lemma53PaperDelta D ((l : ℝ)/q))
    dsimp [f,g,C]
    calc
      _=(if Nat.Coprime (l : ℕ) k then
          (κ (d*(l : ℕ))*lemma53PaperDelta D ((l : ℝ)/q))*deltaReciprocalWeight p (l : ℕ) k else 0) := by
        rw [hs]
        congr 1
        congr 1
        apply sum_congr rfl
        intro θ hθ
        ring
      _=_ := by split_ifs <;> ring
  apply HasSum.tsum_eq
  apply htotal.congr
  intro S
  exact sum_congr rfl (fun l hl => hpoint l)

/-- The full-modulus principal character is exactly the coprime principal
fiber, including k=1 and the nonunit long branch. -/
lemma proposition71_principal_character_delta_fiber {k : ℕ} [NeZero k]
    (D d : ℕ) (q : ℝ) (κ : ℕ → ℂ) :
    proposition71CharacterDeltaFiber D d q κ (1 : DirichletCharacter ℂ k)=
      proposition71PrincipalDeltaFiber D d k q κ := by
  unfold proposition71CharacterDeltaFiber proposition71PrincipalDeltaFiber
  apply tsum_congr
  intro l
  by_cases hl : (l : ℕ).Coprime k
  · have hu : IsUnit ((l : ℕ) : ZMod k) := (ZMod.isUnit_iff_coprime _ _).mpr hl
    simp only [if_pos hl,MulChar.one_apply hu.neg,mul_one]
  · simp only [if_neg hl,proposition71_nonunit_character_term_zero _ hl,mul_zero,zero_mul]

/-- Full character expansion before selecting either principal or additional
arithmetic main characters. The analytic hypotheses are exactly those of the
proved reciprocal fiber split. -/
theorem proposition71_reciprocal_fiber_character_expansion {D k : ℕ} [NeZero k]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {p : ℕ} (hp : p.Coprime k)
    (κ : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀n : ℕ, 0<n → ‖κ n‖≤B*(lemma34Tau 5 n : ℝ))
    {d : ℕ} (hd : 0<d) {q : ℝ} (hq : 1≤q) (hqP : q≤lemma23PaperP D^10) :
    (∑'l : ℕ+, if Nat.Coprime (l : ℕ) k then
      κ (d*(l : ℕ))*deltaReciprocalWeight p (l : ℕ) k*lemma53PaperDelta D ((l : ℝ)/q) else 0)=
      (k.totient : ℂ)⁻¹*∑θ : DirichletCharacter ℂ k,
        gaussSum θ⁻¹ ZMod.stdAddChar*conj (θ (p : ZMod k))*proposition71CharacterDeltaFiber D d q κ θ := by
  rw [proposition71_reciprocal_fiber_split hD hL hp κ hB hκ hd hq hqP]
  have hu : IsUnit (p : ZMod k) := (ZMod.isUnit_iff_coprime p k).mpr hp
  have hs := sum_erase_add (univ : Finset (DirichletCharacter ℂ k))
    (fun θ => gaussSum θ⁻¹ ZMod.stdAddChar*conj (θ (p : ZMod k))*
      proposition71CharacterDeltaFiber D d q κ θ) (mem_univ 1)
  simp only [inv_one,inducedGauss_principal_value,MulChar.one_apply hu,map_one,mul_one,
    proposition71_principal_character_delta_fiber] at hs
  rw [←hs]
  ring

end ZhangLS.Spec
