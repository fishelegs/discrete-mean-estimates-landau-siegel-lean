import ZhangLS.Spec.Proposition141OffLocalPrimeBound

/-! # Literal full σ and the actual omitted-interval subseries

The tail is defined by its omitted indices, not by subtraction. Its genuine
τ₅/l² envelope proves absolute convergence before any infinite sum is split.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141SigmaTerm {D r:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ)
    (κ:ℕ→ℂ) (D₁ d h:ℕ) (l:ℕ) : ℂ :=
  if 0<l ∧ l.Coprime h then κ (D₁*d*l)*θ (l:ZMod r)*
    proposition141ActualShiftedPrimeKernel χ θ β h r l else 0

noncomputable def proposition141Sigma {D r:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ)
    (κ:ℕ→ℂ) (D₁ d h:ℕ) : ℂ := ∑'l:ℕ,proposition141SigmaTerm χ θ β κ D₁ d h l

noncomputable def proposition141SigmaOffLocalTerm {D r:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ)
    (κ:ℕ→ℂ) (D₁ d h:ℕ) (R:ℝ) (l:ℕ) : ℂ :=
  if l∉proposition141LocalizedIndices D R h then proposition141SigmaTerm χ θ β κ D₁ d h l else 0

noncomputable def proposition141SigmaOffLocalTail {D r:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ)
    (κ:ℕ→ℂ) (D₁ d h:ℕ) (R:ℝ) : ℂ :=
  ∑'l:ℕ,proposition141SigmaOffLocalTerm χ θ β κ D₁ d h R l

lemma proposition141_offlocal_sigma_term_majorant {D r h D₁ d:ℕ} {R:ℝ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hR:1≤R) (hh:0<h) (hr:r∈primitiveDyadicModuli R)
    (hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D) (l:ℕ) :
    ‖proposition141SigmaOffLocalTerm χ θ β κ D₁ d h R l‖≤
      ((Real.exp 40*proposition141OffLocalDeltaConstant)*Real.exp (-lemma23PaperL D^10/2)*
        lemma23PaperP D^6*lemma56PrimeMass D*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))*
          ((lemma34Tau 5 l:ℝ)/(l:ℝ)^2) := by
  have hC := proposition141_offlocal_delta_constant_pos.le
  have hM := lemma56_prime_mass_nonneg D
  unfold proposition141SigmaOffLocalTerm
  by_cases hnot:l∉proposition141LocalizedIndices D R h
  · rw [if_pos hnot]
    unfold proposition141SigmaTerm
    split_ifs with hl
    · rw [norm_mul,norm_mul]
      have hcoef := proposition141_kappa_three_factor_bound hB hκ hD₁ hd hl.1
      have hchar := θ.norm_le_one (l:ZMod r)
      have hker := proposition141_offlocal_prime_kernel_bound χ θ hD hL hβ hR hh hr hhr hl.1 hl.2 hnot
      have hh' := mul_le_mul (mul_le_mul hcoef hchar (norm_nonneg _) (by positivity)) hker
        (norm_nonneg _) (by positivity)
      convert hh' using 1; ring
    · rw [norm_zero]
      positivity
  · rw [if_neg hnot,norm_zero]
    positivity

noncomputable def proposition141OffLocalTailConstant : ℝ :=
  243*Real.exp 40*proposition141OffLocalDeltaConstant

lemma proposition141_offlocal_tail_constant_pos : 0<proposition141OffLocalTailConstant := by
  unfold proposition141OffLocalTailConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) proposition141_offlocal_delta_constant_pos

theorem proposition141_actual_offlocal_sigma_bound {D r h D₁ d:ℕ} {R:ℝ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hR:1≤R) (hh:0<h) (hr:r∈primitiveDyadicModuli R)
    (hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D) :
    Summable (proposition141SigmaOffLocalTerm χ θ β κ D₁ d h R) ∧
      ‖proposition141SigmaOffLocalTail χ θ β κ D₁ d h R‖≤
        proposition141OffLocalTailConstant*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*
          lemma56PrimeMass D*lemma23PaperP D^6*Real.exp (-lemma23PaperL D^10/2) := by
  let K := (Real.exp 40*proposition141OffLocalDeltaConstant)*Real.exp (-lemma23PaperL D^10/2)*
    lemma23PaperP D^6*lemma56PrimeMass D*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)
  have hC := proposition141_offlocal_delta_constant_pos.le
  have hM := lemma56_prime_mass_nonneg D
  have hK : 0≤K := by dsimp [K]; positivity
  have ht := proposition141_offlocal_sigma_term_majorant χ θ hD hL hβ hB hκ hD₁ hd hR hh hr hhr
  have hsR := proposition141_tau_five_square_summable.mul_left K
  have hs : Summable (proposition141SigmaOffLocalTerm χ θ β κ D₁ d h R) :=
    Summable.of_norm_bounded hsR ht
  refine ⟨hs,?_⟩
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  have hb := hs.norm.tsum_le_tsum ht hsR
  rw [tsum_mul_left] at hb
  apply hb.trans
  have hh' := mul_le_mul_of_nonneg_left proposition141_tau_five_square_mass_le hK
  change K*(∑'n:ℕ,(lemma34Tau 5 n:ℝ)/(n:ℝ)^2)≤K*243 at hh'
  convert hh' using 1; dsimp [K,proposition141OffLocalTailConstant]; ring

/-- Full σ equals the actual localized finite sum plus the literal omitted
subseries, with both absolute convergence claims proved first. -/
theorem proposition141_actual_sigma_localization {D r h D₁ d:ℕ} {R:ℝ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hR:1≤R) (hh:0<h) (hr:r∈primitiveDyadicModuli R)
    (hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D) :
    Summable (proposition141SigmaTerm χ θ β κ D₁ d h) ∧
      proposition141Sigma χ θ β κ D₁ d h=
        proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r (proposition141LocalizedIndices D R h)+
          proposition141SigmaOffLocalTail χ θ β κ D₁ d h R := by
  have ht := (proposition141_actual_offlocal_sigma_bound χ θ hD hL hβ hB hκ hD₁ hd hR hh hr hhr).1
  let S := proposition141LocalizedIndices D R h
  let F := proposition141SigmaTerm χ θ β κ D₁ d h
  let H : ℕ→ℂ := fun l=>if l∈S then F l else 0
  have hhead : HasSum H (∑l∈S,F l) := by
    have hs : HasSum H (∑l∈S,H l) := hasSum_sum_of_ne_finset_zero (s:=S)
      (fun l hl=>by simp only [H,if_neg hl])
    simpa only [H,sum_ite_mem,inter_self] using hs
  have heq : F=fun l=>H l+proposition141SigmaOffLocalTerm χ θ β κ D₁ d h R l := by
    funext l
    by_cases hl:l∈S <;> simp [H,proposition141SigmaOffLocalTerm,hl,S,F]
  have hs : Summable F := by rw [heq]; exact hhead.summable.add ht
  refine ⟨hs,?_⟩
  change (∑'l:ℕ,F l)=_
  rw [heq,hhead.summable.tsum_add ht,hhead.tsum_eq]
  congr 1
  unfold proposition141FiniteSmallCharacterSum
  apply sum_congr rfl
  intro l hl
  have hp := proposition141_mem_localized_indices.mp hl
  simp only [F,proposition141SigmaTerm,if_pos (And.intro hp.1 hp.2.2.2)]

end ZhangLS.Spec
