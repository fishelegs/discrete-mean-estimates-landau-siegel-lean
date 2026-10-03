import ZhangLS.Spec.Proposition141OffLocalSigma
import ZhangLS.Spec.Proposition141MainSeriesConvergence
import ZhangLS.Spec.InducedGaussMainCharacters
import ZhangLS.Spec.Proposition141GlobalShift

/-! Exact full-series attachment of genuine induced characters to σ. The
prime/long-series exchange is justified directly from absolute Δ convergence. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

noncomputable def proposition141PrimitivePrimeTerm {D r:ℕ}
    (θ:DirichletCharacter ℂ r) (κ:ℕ→ℂ) (D₁ d h p l:ℕ) : ℂ :=
  if 0<l ∧ l.Coprime h then κ (D₁*d*l)*θ (l:ZMod r)*
    lemma53PaperDelta D ((l:ℝ)/((p:ℝ)*(h:ℝ)*(r:ℝ))) else 0

lemma proposition141_primitive_prime_series_summable {D r D₁ d h p:ℕ}
    (θ:DirichletCharacter ℂ r) (hD:1<D) (hL:2000≤lemma23PaperL D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hh:0<h) (hr:0<r) (hp:0<p) :
    Summable (proposition141PrimitivePrimeTerm (D:=D) θ κ D₁ d h p) := by
  have hq:0<(p:ℝ)*(h:ℝ)*(r:ℝ) := by positivity
  have hs := proposition141_coprime_delta_series_summable hD hL θ hB hκ hD₁ hd hq h
  have hs' := hs.indicator {l:ℕ | 0<l}
  apply hs'.congr
  intro l
  simp only [Set.indicator_apply,Set.mem_setOf_eq,proposition141PrimitivePrimeTerm]
  by_cases hl:0<l <;> by_cases hc:l.Coprime h <;> simp [hl,hc]

/-- The actual full σ equals the genuine finite prime sum of complete
infinite l rows, without a localization or analytic error premise. -/
theorem proposition141_sigma_prime_exchange {D r D₁ d h:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {B:ℝ} (hB:0≤B)
    {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hh:0<h) (hr:0<r) :
    Summable (proposition141SigmaTerm χ θ β κ D₁ d h) ∧
      proposition141Sigma χ θ β κ D₁ d h=
        ∑p∈lemma56PaperPrimes D,χ.chi (p:ZMod D)*conj (θ (p:ZMod r))*(p:ℂ)^β*
          ∑'l:ℕ,proposition141PrimitivePrimeTerm (D:=D) θ κ D₁ d h p l := by
  let C := fun (p:ℕ)=>χ.chi (p:ZMod D)*conj (θ (p:ZMod r))*(p:ℂ)^β
  let F := fun (p l:ℕ)=>C p*proposition141PrimitivePrimeTerm (D:=D) θ κ D₁ d h p l
  have hs (p:ℕ) (hp:p∈lemma56PaperPrimes D) : Summable (F p) :=
    (proposition141_primitive_prime_series_summable θ hD hL hB hκ hD₁ hd hh hr
      (lemma56_mem_paper_primes D p |>.mp hp).1.pos).mul_left _
  have he : proposition141SigmaTerm χ θ β κ D₁ d h=
      fun l=>∑p∈lemma56PaperPrimes D,F p l := by
    funext l
    unfold proposition141SigmaTerm proposition141ActualShiftedPrimeKernel
    dsimp [F,C,proposition141PrimitivePrimeTerm]
    by_cases hl:0<l ∧ l.Coprime h
    · simp only [if_pos hl,mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    · simp only [if_neg hl,mul_zero,sum_const_zero]
  have hfin := hasSum_sum (s:=lemma56PaperPrimes D) (fun p hp=>(hs p hp).hasSum)
  refine ⟨he ▸ hfin.summable,?_⟩
  unfold proposition141Sigma
  rw [he,Summable.tsum_finsetSum hs]
  simp only [F,tsum_mul_left,C]

lemma proposition141_induced_negative_nat {r h:ℕ} [NeZero r] [NeZero h]
    (θ:DirichletCharacter ℂ r) (l:ℕ) :
    θ.changeLevel (r.dvd_mul_right h) (-(l:ZMod (r*h)))=
      if l.Coprime h then θ (-1:ZMod r)*θ (l:ZMod r) else 0 := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  have hn : θ.changeLevel (r.dvd_mul_right h) (-1:ZMod (r*h))=θ (-1:ZMod r) := by
    simpa only [Nat.cast_one] using inducedGauss_changeLevel_neg_nat θ 1 (Nat.coprime_one_left h)
  rw [show -(l:ZMod (r*h))=(-1)*(l:ZMod (r*h)) by ring,map_mul,hn,
    inducedGauss_changeLevel_nat]
  split_ifs <;> simp

noncomputable def proposition141InducedPrimeRow {D r h:ℕ} [NeZero r] [NeZero h]
    (θ:DirichletCharacter ℂ r) (κ:ℕ→ℂ) (D₁ d p:ℕ) : ℂ :=
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  let η := θ.changeLevel (r.dvd_mul_right h)
  ∑'l:ℕ,if 0<l then κ (D₁*d*l)*η (-(l:ZMod (r*h)))*conj (η (p:ZMod (r*h)))*
    lemma53PaperDelta D ((l:ℝ)/((p:ℝ)*(h:ℝ)*(r:ℝ))) else 0

/-- Literal induced row, with its extra-factor coprimality restored exactly. -/
theorem proposition141_induced_prime_row {D r h:ℕ} [NeZero r] [NeZero h]
    (θ:DirichletCharacter ℂ r) (κ:ℕ→ℂ) (D₁ d p:ℕ) (hp:p.Coprime h) :
    proposition141InducedPrimeRow (D:=D) (h:=h) θ κ D₁ d p=
      θ (-1:ZMod r)*conj (θ (p:ZMod r))*
        ∑'l:ℕ,proposition141PrimitivePrimeTerm (D:=D) θ κ D₁ d h p l := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  unfold proposition141InducedPrimeRow
  simp only
  rw [←tsum_mul_left]
  apply tsum_congr
  intro l
  unfold proposition141PrimitivePrimeTerm
  rw [inducedGauss_changeLevel_nat θ p,if_pos hp,proposition141_induced_negative_nat]
  by_cases hl:0<l <;> by_cases hc:l.Coprime h <;> simp [hl,hc] <;> ring

/-- Full actual source prime average equals the full σ, including negative
character phase and all positive long indices. No β bound is needed here. -/
theorem proposition141_induced_source_sigma {D r h D₁ d:ℕ} [NeZero r] [NeZero h]
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {B:ℝ} (hB:0≤B)
    {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) (hD₁:0<D₁) (hd:0<d)
    (hp:∀p∈lemma56PaperPrimes D,p.Coprime h) :
    (∑p∈lemma56PaperPrimes D,χ.chi (p:ZMod D)*(p:ℂ)^β*
      proposition141InducedPrimeRow (D:=D) (h:=h) θ κ D₁ d p)=
        θ (-1:ZMod r)*proposition141Sigma χ θ β κ D₁ d h := by
  rw [(proposition141_sigma_prime_exchange χ θ β hD hL hB hκ hD₁ hd
    (Nat.pos_of_ne_zero (NeZero.ne h)) (Nat.pos_of_ne_zero (NeZero.ne r))).2,mul_sum]
  apply sum_congr rfl
  intro p hpp
  rw [proposition141_induced_prime_row θ κ D₁ d p (hp p hpp)]
  ring

/-- The original full complex shift is factored exactly before induction. -/
theorem proposition141_induced_shifted_source_sigma {D r h D₁ d:ℕ} [NeZero r] [NeZero h]
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {B:ℝ} (hB:0≤B)
    {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) (hD₁:0<D₁) (hd:0<d)
    (hp:∀p∈lemma56PaperPrimes D,p.Coprime h) :
    (∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
      proposition141InducedPrimeRow (D:=D) (h:=h) θ κ D₁ d p)=
        (lemma51PaperT0 D:ℂ)^β*θ (-1:ZMod r)*proposition141Sigma χ θ β κ D₁ d h := by
  rw [proposition141_prime_windows_equal]
  have hw (p:ℕ) : proposition141ShiftWeight D p β=(lemma51PaperT0 D:ℂ)^β*(p:ℂ)^β := by
    simpa only [proposition141ShiftWeight,Complex.ofReal_mul,Complex.ofReal_natCast] using
      proposition141_prime_t0_shift_factor (p:=p) hL β
  calc
    _=(lemma51PaperT0 D:ℂ)^β*
        (∑p∈lemma56PaperPrimes D,χ.chi (p:ZMod D)*(p:ℂ)^β*
          proposition141InducedPrimeRow (D:=D) (h:=h) θ κ D₁ d p) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hpp
      rw [hw]
      ring
    _=_ := by rw [proposition141_induced_source_sigma χ θ β hD hL hB hκ hD₁ hd hp]; ring

/-- Genuine induced Gauss amplitude times the complete shifted source,
bounded by sqrt(r) times the literal full σ, with no divisor factors lost. -/
theorem proposition141_induced_gauss_source_bound {D r h D₁ d:ℕ} [NeZero r] [NeZero h]
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (hθ:θ.IsPrimitive) (β:ℂ)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {B:ℝ} (hB:0≤B)
    {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) (hD₁:0<D₁) (hd:0<d)
    (hp:∀p∈lemma56PaperPrimes D,p.Coprime h) :
    letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
    ‖gaussSum (θ.changeLevel (r.dvd_mul_right h))⁻¹ ZMod.stdAddChar*
      (∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
        proposition141InducedPrimeRow (D:=D) (h:=h) θ κ D₁ d p)‖≤
      ‖(lemma51PaperT0 D:ℂ)^β‖*Real.sqrt (r:ℝ)*‖proposition141Sigma χ θ β κ D₁ d h‖ := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  rw [proposition141_induced_shifted_source_sigma χ θ β hD hL hB hκ hD₁ hd hp]
  simp only [norm_mul]
  have hg := inducedGauss_inverse_norm_le_sqrt_conductor (θ.changeLevel (r.dvd_mul_right h))
  rw [lemma44_conductor_changeLevel,hθ] at hg
  have hc := θ.norm_le_one (-1:ZMod r)
  have hinner : ‖(lemma51PaperT0 D:ℂ)^β‖*‖θ (-1:ZMod r)‖*‖proposition141Sigma χ θ β κ D₁ d h‖≤
      ‖(lemma51PaperT0 D:ℂ)^β‖*‖proposition141Sigma χ θ β κ D₁ d h‖ := by
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (norm_nonneg ((lemma51PaperT0 D:ℂ)^β)))
      (norm_nonneg (proposition141Sigma χ θ β κ D₁ d h))
    simpa only [mul_one] using hb
  exact (mul_le_mul hg hinner (by positivity) (Real.sqrt_nonneg _)).trans_eq (by ring)

end ZhangLS.Spec
