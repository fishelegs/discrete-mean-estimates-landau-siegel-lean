import ZhangLS.Spec.Lemma102MixedObjects
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def lemma102MixedInteriorConstant : ℝ :=
  32000*lemma84CompanionConstant*(1+‖lemma84Section8Iota‖)*
    (2+lemma84TaylorCircleConstant*lemma83PrimeProductScale)

lemma lemma102_mixed_interior_constant_pos : 0<lemma102MixedInteriorConstant := by
  unfold lemma102MixedInteriorConstant lemma83PrimeProductScale
  positivity [lemma84_companion_constant_pos,lemma84_circle_constants_pos.1]

/-- Genuine weighted interior replacement of the actual Section 10 tent-ξ
factor. All original μ/χ/λ/φ weights and the κ companion are retained. -/
theorem lemma102_mixed_interior_quantitative :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ j : Fin 3,
        ‖lemma102MixedRaw χ c j-lemma102MixedHybrid χ c j‖≤
          lemma102MixedInteriorConstant*lemma84WeightScale (lemma23PaperL D^9)*
            (1+9*Real.log (lemma23PaperL D))^lemma84PiExponent*lemma23PaperL D^(-12:ℤ) := by
  intro c hc
  obtain ⟨Ni,hNi,hint⟩ := lemma102_genuine_interior_error_with_pi c hc
  obtain ⟨Nf,hNf,hfirst⟩ := lemma84_section8_inner_bounds c hc
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      Ni≤D ∧ Nf≤D ∧ 2≤D ∧ 2000≤lemma23PaperL D ∧
        lemma23PaperP D^(63/125:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) from by
    filter_upwards [eventually_ge_atTop Ni,eventually_ge_atTop Nf,
      lemma84_section8_cutoffs_eventually,ht.eventually_ge_atTop 2000] with D hi hf hq hL
    exact ⟨hi,hf,hq.1,hL,by simpa [lemma84Section8Cutoff,lemma84Section8P1] using (hq.2.2 6).2.1⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).2.2.1,?_⟩
  intro D hDD χ hA j
  obtain ⟨hNi,hNf,hD2,hL,hPcut⟩ := hD₀ D hDD
  have hD : 1<D := by omega
  have hLp : 0< lemma23PaperL D := by linarith
  have hB1 : 1≤1+9*Real.log (lemma23PaperL D) := by
    linarith [Real.log_nonneg (by linarith : 1≤lemma23PaperL D)]
  let F := 4*lemma84CompanionConstant*(1+‖lemma84Section8Iota‖)*lemma23PaperL D^(-6:ℤ)
  let E := 2000*(2+lemma84TaylorCircleConstant*lemma83PrimeProductScale)*
    (1+9*Real.log (lemma23PaperL D))^lemma84PiExponent*lemma23PaperL D^(-15:ℤ)
  have hF0 : 0≤F := by dsimp [F]; positivity [lemma84_companion_constant_pos]
  have hE0 : 0≤E := by dsimp [E,lemma83PrimeProductScale]; positivity [lemma84_circle_constants_pos.1]
  have hF (n : ℕ) (hn : 0<n) : ‖lemma84Section8FirstCombined χ c j n‖≤F := by
    have h6 := ((hfirst D hNf).2 χ hA j 6).1 n hn
    have h7 := ((hfirst D hNf).2 χ hA j 7).1 n hn
    unfold lemma84Section8FirstCombined
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    have hh := mul_le_mul_of_nonneg_left h7 (norm_nonneg lemma84Section8Iota)
    dsimp [F]
    nlinarith only [h6,hh]
  have hE (d r : ℕ) (hd : 0<d) (hr : 0<r) (hupper : (d*r:ℝ)<lemma23PaperP D^(63/125:ℝ)) :
      ‖lemma102Sum χ c j d r-
        (if Lemma101Transition D (d*r:ℝ) then lemma102Sum χ c j d r else lemma102FullMain χ c j d r)‖≤E := by
    split_ifs with hband
    · simpa using hE0
    have hcut := hupper.trans hPcut
    have hPi := lemma84_pi_polylog_bound χ (by linarith : 100≤lemma23PaperL D)
      d r lemma84PiExponent hd hr hcut (Nat.le_ceil _)
    have hbudget : 2000*(2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖)*lemma23PaperL D^(-15:ℤ)≤E := by
      have hp := one_le_pow₀ hB1 (n:=lemma84PiExponent)
      have hh := mul_le_mul_of_nonneg_left hPi lemma84_circle_constants_pos.1.le
      have hs : 2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖≤
        (2+lemma84TaylorCircleConstant*lemma83PrimeProductScale)*
          (1+9*Real.log (lemma23PaperL D))^lemma84PiExponent := by nlinarith only [hp,hh]
      have hh' := mul_le_mul_of_nonneg_right hs (show 0≤2000*lemma23PaperL D^(-15:ℤ) by positivity)
      dsimp [E]
      nlinarith only [hh']
    have hi := hint D hNi χ hA j d r hd hr
    dsimp only at hi
    unfold lemma102FullMain
    split_ifs with h1 h2
    · apply (hi.1 ?_).trans hbudget
      by_contra hn
      exact hband (Or.inl (Or.inl ⟨lt_of_not_ge hn,h1⟩))
    · apply (hi.2.1 (lt_of_not_ge h1) ?_).trans hbudget
      by_contra hn
      exact hband (Or.inl (Or.inr ⟨lt_of_not_ge hn,h2⟩))
    · apply (hi.2.2 (lt_of_not_ge h2) ?_).trans hbudget
      by_contra hn
      exact hband (Or.inr ⟨lt_of_not_ge hn,hupper⟩)
  have hid : lemma102MixedRaw χ c j-lemma102MixedHybrid χ c j=
      ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
        lemma84Section8FirstCombined χ c j (a.1*a.2)*
        (lemma102Sum χ c j a.1 a.2-
          (if Lemma101Transition D (a.1*a.2:ℝ) then lemma102Sum χ c j a.1 a.2
            else lemma102FullMain χ c j a.1 a.2)) := by
    rw [lemma102MixedRaw,lemma102MixedHybrid,←sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    ring
  rw [hid]
  calc
    _ ≤ ∑ a∈lemma84Section8Pairs D, ‖lemma84Section8Weight χ c j a.1 a.2‖*F*E := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro a ha
      obtain ⟨hd,hr,hupper⟩ := (lemma84_section8_pairs_exact D a.1 a.2).mp ha
      rw [norm_mul,norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF _ (Nat.mul_pos hd hr)) (norm_nonneg _))
        (hE a.1 a.2 hd hr (by simpa [lemma84Section8P1] using hupper)) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) hF0)
    _ = (∑ a∈lemma84Section8Pairs D, ‖lemma84Section8Weight χ c j a.1 a.2‖)*F*E := by rw [sum_mul,sum_mul]
    _ ≤ (4*lemma84WeightScale (lemma23PaperL D^9)*lemma23PaperL D^9)*F*E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (lemma84_section8_weight_mass χ c j (by linarith)) hF0) hE0
    _ = _ := by
      dsimp [F,E,lemma102MixedInteriorConstant]
      simp only [zpow_neg,zpow_ofNat]
      field_simp <;> ring

end ZhangLS.Spec
