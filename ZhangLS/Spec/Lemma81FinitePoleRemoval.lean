import ZhangLS.Spec.Lemma81ActualResidues

/-! # Removing finitely many genuine simple poles

The correction at each pole is fixed by its actual divided-difference
regular part. Away from the finite zero set the remainder is exactly the
original quotient minus the finite sum of its computed principal parts.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Filter
open scoped Topology Classical
set_option maxHeartbeats 2000000

noncomputable def lemma81FinitePoleRemainder (N M : ℂ → ℂ) (S : Finset ℂ) (s : ℂ) : ℂ :=
  N s / M s - (∑ ρ ∈ S, (N ρ / deriv M ρ) / (s-ρ)) +
    if s ∈ S then deriv (fun z => N z / dslope M s z) s else 0

lemma lemma81_finite_pole_remainder_off_set (N M : ℂ → ℂ) (S : Finset ℂ)
    {s : ℂ} (hs : s ∉ S) :
    lemma81FinitePoleRemainder N M S s = N s/M s - ∑ ρ ∈ S, (N ρ/deriv M ρ)/(s-ρ) := by
  simp only [lemma81FinitePoleRemainder,if_neg hs,add_zero]

lemma lemma81_finite_pole_remainder_at_pole (N M : ℂ → ℂ) (S : Finset ℂ)
    {ρ s : ℂ} (hρ : ρ ∈ S) (hzero : M ρ = 0) (hs : s ∉ S.erase ρ) :
    lemma81FinitePoleRemainder N M S s = lemma81SimplePoleRegularPart N M ρ s -
      ∑ ζ ∈ S.erase ρ, (N ζ/deriv M ζ)/(s-ζ) := by
  have hsum := Finset.sum_erase_add S (fun ζ => (N ζ/deriv M ζ)/(s-ζ)) hρ
  by_cases he : s = ρ
  · subst s
    unfold lemma81FinitePoleRemainder lemma81SimplePoleRegularPart
    rw [if_pos hρ,hzero,div_zero,← hsum]
    dsimp only
    rw [sub_self,div_zero,add_zero,dslope_same]
    ring
  · have hsS : s ∉ S := by
      intro hh
      exact hs (Finset.mem_erase.mpr ⟨he,hh⟩)
    rw [lemma81_finite_pole_remainder_off_set N M S hsS,← hsum,
      lemma81_simple_zero_principal_part hzero he]
    ring

lemma lemma81_principal_sum_analyticAt (N M : ℂ → ℂ) (S : Finset ℂ)
    {s : ℂ} (hs : s ∉ S) :
    AnalyticAt ℂ (fun z => ∑ ρ ∈ S, (N ρ/deriv M ρ)/(z-ρ)) s := by
  apply Finset.analyticAt_fun_sum
  intro ρ hρ
  have hne : s-ρ ≠ 0 := sub_ne_zero.mpr (fun he => hs (he ▸ hρ))
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) hne

/-- Every actual simple pole is removed analytically. No residue value or
pole-removal equality is an additional hypothesis. -/
theorem lemma81_finite_pole_remainder_analyticOnNhd (N M : ℂ → ℂ) (S : Finset ℂ)
    (U : Set ℂ) (hN : AnalyticOnNhd ℂ N U) (hM : AnalyticOnNhd ℂ M U)
    (hzeros : ∀ s ∈ U, M s = 0 ↔ s ∈ S)
    (hsimple : ∀ ρ ∈ S, deriv M ρ ≠ 0) :
    AnalyticOnNhd ℂ (lemma81FinitePoleRemainder N M S) U := by
  intro s hs
  by_cases hsin : s ∈ S
  · have hzero := (hzeros s hs).mpr hsin
    have hreg := lemma81_simple_pole_regular_part_analytic (hN s hs) (hM s hs) (hsimple s hsin)
    have herase : s ∉ S.erase s := Finset.notMem_erase _ _
    have hsum := lemma81_principal_sum_analyticAt N M (S.erase s) herase
    apply (hreg.sub hsum).congr
    have hn : (↑(S.erase s) : Set ℂ)ᶜ ∈ 𝓝 s :=
      (S.erase s).finite_toSet.isClosed.isOpen_compl.mem_nhds herase
    filter_upwards [hn] with z hz
    exact (lemma81_finite_pole_remainder_at_pole N M S hsin hzero hz).symm
  · have hnonzero : M s ≠ 0 := fun hz => hsin ((hzeros s hs).mp hz)
    have hquot := (hN s hs).div (hM s hs) hnonzero
    have hsum := lemma81_principal_sum_analyticAt N M S hsin
    apply (hquot.sub hsum).congr
    have hn : (↑S : Set ℂ)ᶜ ∈ 𝓝 s := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hsin
    filter_upwards [hn] with z hz
    exact (lemma81_finite_pole_remainder_off_set N M S hz).symm

end ZhangLS.Spec
