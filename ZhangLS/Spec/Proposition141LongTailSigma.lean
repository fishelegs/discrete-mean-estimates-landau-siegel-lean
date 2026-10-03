import ZhangLS.Spec.Proposition141OffLocalSigma
import ZhangLS.Spec.Proposition141PrimitiveSmallSum

/-! # The literal l>P³ subseries and exact closed-prefix decomposition

This is a true subseries of σ. The proved geometry places the whole local
interval at scale R=r below P³, so the existing actual off-center envelope
controls it without asserting any new cancellation beyond the valid height.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition141_four_t0_le_P {D:ℕ} (hL:2000≤lemma23PaperL D) :
    4*lemma51PaperT0 D≤lemma23PaperP D := by
  have hL1:1≤lemma23PaperL D := by linarith
  have hL11:2≤lemma23PaperL D^11 := by
    have hh := le_self_pow₀ hL1 (by norm_num : 11≠0)
    linarith
  have hh := mul_le_mul_of_nonneg_right hL11 (show 0≤2*lemma23PaperL D^519 by positivity)
  apply le_trans _ (proposition141_log_scale_le_P hL)
  unfold lemma51PaperT0
  convert hh using 1 <;> ring

lemma proposition141_individual_local_upper {D h r:ℕ} (hL:2000≤lemma23PaperL D)
    (hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D) :
    4*proposition141LocalScale D (r:ℝ) h≤lemma23PaperP D^3 := by
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have ht:0≤lemma51PaperT0 D := pow_nonneg (by linarith : 0≤lemma23PaperL D) _
  have hh : (h:ℝ)*(r:ℝ)≤lemma23PaperP D := by simpa only [Nat.cast_mul] using hhr
  calc
    _=lemma23PaperP D*(4*lemma51PaperT0 D)*((h:ℝ)*(r:ℝ)) := by unfold proposition141LocalScale; ring
    _≤lemma23PaperP D*lemma23PaperP D*lemma23PaperP D := by
      gcongr
      exact proposition141_four_t0_le_P hL
    _=_ := by ring

noncomputable def proposition141SigmaLongTailTerm {D r:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ)
    (κ:ℕ→ℂ) (D₁ d h:ℕ) (l:ℕ) : ℂ :=
  if lemma23PaperP D^3<(l:ℝ) then proposition141SigmaTerm χ θ β κ D₁ d h l else 0

noncomputable def proposition141SigmaLongTail {D r:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ)
    (κ:ℕ→ℂ) (D₁ d h:ℕ) : ℂ := ∑'l:ℕ,proposition141SigmaLongTailTerm χ θ β κ D₁ d h l

lemma proposition141_long_tail_term_majorant {D r h D₁ d:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hh:0<h) (hr:1<r)
    (hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D) (l:ℕ) :
    ‖proposition141SigmaLongTailTerm χ θ β κ D₁ d h l‖≤
      ((Real.exp 40*proposition141OffLocalDeltaConstant)*Real.exp (-lemma23PaperL D^10/2)*
        lemma23PaperP D^6*lemma56PrimeMass D*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))*
          ((lemma34Tau 5 l:ℝ)/(l:ℝ)^2) := by
  have hC := proposition141_offlocal_delta_constant_pos.le
  have hM := lemma56_prime_mass_nonneg D
  unfold proposition141SigmaLongTailTerm
  split_ifs with hl
  · have hnot : l∉proposition141LocalizedIndices D (r:ℝ) h := by
      intro hin
      have hi := (proposition141_mem_localized_indices.mp hin).2.2.1
      exact (not_le_of_gt hl) (hi.trans (proposition141_individual_local_upper hL hhr))
    have hR:1≤(r:ℝ) := by exact_mod_cast (show 1≤r by omega)
    have hrdy : r∈primitiveDyadicModuli (r:ℝ) := mem_primitiveDyadicModuli.mpr
      ⟨hr,le_rfl,by
        have hp:0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
        linarith⟩
    have hb := proposition141_offlocal_sigma_term_majorant χ θ hD hL hβ hB hκ hD₁ hd hR hh hrdy hhr l
    simpa only [proposition141SigmaOffLocalTerm,if_pos hnot] using hb
  · rw [norm_zero]
    positivity

theorem proposition141_actual_long_tail_bound {D r h D₁ d:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hh:0<h) (hr:1<r)
    (hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D) :
    Summable (proposition141SigmaLongTailTerm χ θ β κ D₁ d h) ∧
      ‖proposition141SigmaLongTail χ θ β κ D₁ d h‖≤
        proposition141OffLocalTailConstant*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*
          lemma56PrimeMass D*lemma23PaperP D^6*Real.exp (-lemma23PaperL D^10/2) := by
  let K := (Real.exp 40*proposition141OffLocalDeltaConstant)*Real.exp (-lemma23PaperL D^10/2)*
    lemma23PaperP D^6*lemma56PrimeMass D*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)
  have hC := proposition141_offlocal_delta_constant_pos.le
  have hM := lemma56_prime_mass_nonneg D
  have hK:0≤K := by dsimp [K]; positivity
  have ht := proposition141_long_tail_term_majorant χ θ hD hL hβ hB hκ hD₁ hd hh hr hhr
  have hsR := proposition141_tau_five_square_summable.mul_left K
  have hs : Summable (proposition141SigmaLongTailTerm χ θ β κ D₁ d h) := Summable.of_norm_bounded hsR ht
  refine ⟨hs,?_⟩
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  have hb := hs.norm.tsum_le_tsum ht hsR
  rw [tsum_mul_left] at hb
  apply hb.trans
  have hh' := mul_le_mul_of_nonneg_left proposition141_tau_five_square_mass_le hK
  change K*(∑'n:ℕ,(lemma34Tau 5 n:ℝ)/(n:ℝ)^2)≤K*243 at hh'
  convert hh' using 1; dsimp [K,proposition141OffLocalTailConstant]; ring

/-- The original full series split at the closed P³ prefix. -/
theorem proposition141_actual_sigma_prefix {D r h D₁ d:ℕ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hh:0<h) (hr:1<r)
    (hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D) :
    Summable (proposition141SigmaTerm χ θ β κ D₁ d h) ∧
      proposition141Sigma χ θ β κ D₁ d h=
        proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (Icc 1 ⌊lemma23PaperP D^3⌋₊)+
          proposition141SigmaLongTail χ θ β κ D₁ d h := by
  have ht := (proposition141_actual_long_tail_bound χ θ hD hL hβ hB hκ hD₁ hd hh hr hhr).1
  let S := Icc 1 ⌊lemma23PaperP D^3⌋₊
  let F := proposition141SigmaTerm χ θ β κ D₁ d h
  let H:ℕ→ℂ := fun l=>if l∈S then F l else 0
  have hhead : HasSum H (∑l∈S,F l) := by
    have hs : HasSum H (∑l∈S,H l) := hasSum_sum_of_ne_finset_zero (s:=S)
      (fun l hl=>by simp only [H,if_neg hl])
    simpa only [H,sum_ite_mem,inter_self] using hs
  have heq : F=fun l=>H l+proposition141SigmaLongTailTerm χ θ β κ D₁ d h l := by
    funext l
    by_cases hl:l=0
    · subst l
      have hP:¬lemma23PaperP D^3<(0:ℝ) := not_lt.mpr (pow_nonneg (Real.exp_pos _).le _)
      simp [F,H,S,proposition141SigmaLongTailTerm,proposition141SigmaTerm,hP]
    have hlpos:1≤l := by omega
    by_cases hm:l∈S
    · have hle:(l:ℝ)≤lemma23PaperP D^3 :=
        (by exact_mod_cast (mem_Icc.mp hm).2 : (l:ℝ)≤⌊lemma23PaperP D^3⌋₊).trans (Nat.floor_le (pow_nonneg (Real.exp_pos _).le _))
      simp only [H,if_pos hm,proposition141SigmaLongTailTerm,if_neg (not_lt.mpr hle),add_zero]
    · have hgt:lemma23PaperP D^3<(l:ℝ) := Nat.lt_of_floor_lt (by
        have hh:¬l≤⌊lemma23PaperP D^3⌋₊ := fun he=>hm (mem_Icc.mpr ⟨hlpos,he⟩)
        omega)
      simp only [H,if_neg hm,proposition141SigmaLongTailTerm,if_pos hgt,zero_add,F]
  have hs : Summable F := by rw [heq]; exact hhead.summable.add ht
  refine ⟨hs,?_⟩
  change (∑'l:ℕ,F l)=_
  rw [heq,hhead.summable.tsum_add ht,hhead.tsum_eq]
  congr 1
  unfold proposition141PrimitiveFiniteCharacterSum
  rw [sum_filter]
  apply sum_congr rfl
  intro l hl
  have hlpos:0<l := (mem_Icc.mp hl).1
  simp only [F,proposition141SigmaTerm,hlpos,true_and]

end ZhangLS.Spec
