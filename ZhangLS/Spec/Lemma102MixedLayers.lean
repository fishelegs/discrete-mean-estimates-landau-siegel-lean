import ZhangLS.Spec.Lemma102MixedObjects
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2500000

/-- Closed original knot layers retain their upper endpoint. Enlarging to
[Q/T,QT) gives a true harmonic mass bound without discarding that endpoint. -/
lemma lemma102_closed_weight_layer {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1< lemma23PaperL D) (c : ℝ) (j : Fin 3)
    (S : Finset (ℕ×ℕ)) (hS : S⊆(Icc 1 ⌊lemma84Section8P1 D⌋₊)×ˢ(Icc 1 ⌊lemma84Section8P1 D⌋₊))
    {Q : ℝ} (hQ : 0<Q) (hcut : Q<lemma23PaperP D*lemma56PaperT D^(-2:ℤ))
    (hband : ∀ a∈S, Q/lemma56PaperT D≤(a.1*a.2:ℕ) ∧ ((a.1*a.2:ℕ):ℝ)≤Q) :
    (∑ a∈S, ‖lemma84Section8Weight χ c j a.1 a.2‖)≤
      2*lemma84WeightScale (lemma23PaperL D^9)*(2+2*Real.log (lemma56PaperT D)) := by
  have hT := lemma101_T_gt_one hD
  have hT0 : 0<lemma56PaperT D := by linarith
  have hQT : Q*lemma56PaperT D<lemma23PaperP D := by
    have hh := mul_lt_mul_of_pos_right hcut hT0
    have he : (lemma23PaperP D*lemma56PaperT D^(-2:ℤ))*lemma56PaperT D=
        lemma23PaperP D/lemma56PaperT D := by
      simp only [zpow_neg,zpow_ofNat]
      field_simp <;> ring
    rw [he] at hh
    exact hh.trans_le (div_le_self (Real.exp_pos _).le hT.le)
  have hb := lemma84_actual_weight_layer χ c j S ⌊lemma84Section8P1 D⌋₊ hS
    (Q:=Q*lemma56PaperT D) (T:=lemma56PaperT D^2)
    (mul_pos hQ hT0) (one_le_pow₀ hT.le) (one_lt_pow₀ hL (by norm_num : 9≠0)) (by
      have hh := (Real.log_lt_log (mul_pos hQ hT0) hQT).le
      simpa only [lemma23PaperP,Real.log_exp] using hh) (by
      intro a ha
      have hh := hband a ha
      constructor
      · convert hh.1 using 1
        field_simp
      · exact hh.2.trans_lt (by nlinarith only [mul_pos hQ (sub_pos.mpr hT)]))
  simpa only [Real.log_pow,Nat.cast_ofNat] using hb

noncomputable def lemma102TransitionPairs (D : ℕ) : Finset (ℕ×ℕ) :=
  (lemma84Section8Pairs D).filter (fun a => Lemma101Transition D (a.1*a.2:ℝ))

/-- All three original transition bands have only O(log T) actual weighted
mass, with their strict lower and mixed upper endpoints preserved. -/
lemma lemma102_transition_weight_mass {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1< lemma23PaperL D) (c : ℝ) (j : Fin 3)
    (hcut : lemma23PaperP D^(63/125:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ)) :
    (∑ a∈lemma102TransitionPairs D, ‖lemma84Section8Weight χ c j a.1 a.2‖)≤
      24*lemma84WeightScale (lemma23PaperL D^9)*Real.log (lemma56PaperT D) := by
  let W := lemma84WeightScale (lemma23PaperL D^9)
  let H := Real.log (lemma56PaperT D)
  let band := fun t : ℝ => (lemma84Section8Pairs D).filter (fun a =>
    lemma23PaperP D^t/lemma56PaperT D≤(a.1*a.2:ℕ) ∧ ((a.1*a.2:ℕ):ℝ)≤lemma23PaperP D^t)
  have hb (t : ℝ) (ht : t≤63/125) :
      (∑ a∈band t, ‖lemma84Section8Weight χ c j a.1 a.2‖)≤2*W*(2+2*H) := by
    apply lemma102_closed_weight_layer χ hD hL c j (band t)
      (fun a ha => (mem_filter.mp (mem_filter.mp ha).1).1) (Real.rpow_pos_of_pos (Real.exp_pos _) _)
      ((Real.rpow_le_rpow_of_exponent_le (lemma101_P_gt_one hD).le ht).trans_lt hcut)
      (fun a ha => (mem_filter.mp ha).2)
  have hm : (∑ a∈lemma102TransitionPairs D, ‖lemma84Section8Weight χ c j a.1 a.2‖)≤
      (∑ a∈band (1/2), ‖lemma84Section8Weight χ c j a.1 a.2‖)+
      (∑ a∈band (251/500), ‖lemma84Section8Weight χ c j a.1 a.2‖)+
      (∑ a∈band (63/125), ‖lemma84Section8Weight χ c j a.1 a.2‖) := by
    dsimp [lemma102TransitionPairs,band]
    simp_rw [sum_filter]
    rw [←sum_add_distrib,←sum_add_distrib]
    apply sum_le_sum
    intro a ha
    by_cases hband : Lemma101Transition D (a.1*a.2:ℝ)
    · rw [if_pos hband]
      rcases hband with ((h|h)|h)
      · have hb : lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D≤(a.1*a.2:ℕ) ∧
            ((a.1*a.2:ℕ):ℝ)≤lemma23PaperP D^(1/2:ℝ) := by simpa only [Nat.cast_mul] using And.intro h.1.le h.2
        rw [if_pos hb]
        split_ifs <;> linarith [norm_nonneg (lemma84Section8Weight χ c j a.1 a.2)]
      · have hb : lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D≤(a.1*a.2:ℕ) ∧
            ((a.1*a.2:ℕ):ℝ)≤lemma23PaperP D^(251/500:ℝ) := by simpa only [Nat.cast_mul] using And.intro h.1.le h.2
        rw [if_pos hb]
        split_ifs <;> linarith [norm_nonneg (lemma84Section8Weight χ c j a.1 a.2)]
      · have hb : lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D≤(a.1*a.2:ℕ) ∧
            ((a.1*a.2:ℕ):ℝ)≤lemma23PaperP D^(63/125:ℝ) := by simpa only [Nat.cast_mul] using And.intro h.1.le h.2.le
        rw [if_pos hb]
        split_ifs <;> linarith [norm_nonneg (lemma84Section8Weight χ c j a.1 a.2)]
    · rw [if_neg hband]
      split_ifs <;> positivity
  have hH : 1≤H := by dsimp [H]; rw [lemma56PaperT,Real.log_exp]; exact Real.one_le_rpow hL.le (by norm_num)
  have hW : 0≤W := lemma84_weight_scale_nonneg _
  have h0 := hb (1/2) (by norm_num)
  have h1 := hb (251/500) (by norm_num)
  have h2 := hb (63/125) le_rfl
  have hh := mul_le_mul_of_nonneg_left hH hW
  change _≤24*W*H
  nlinarith only [hm,h0,h1,h2,hh]

end ZhangLS.Spec
