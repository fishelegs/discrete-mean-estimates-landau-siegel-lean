import Mathlib.Analysis.Meromorphic.FactorizedRational
import ZhangLS.Spec.Lemma23ArgumentPrinciple
import ZhangLS.Spec.Lemma23RoucheIntegral

/-!
# General argument-principle bridge for Lemma 2.3

The finite-factor formulas are combined here with Mathlib's divisor decomposition for analytic
functions. The first step is compactness of locally finite zero support.
-/

namespace ZhangLS.Spec

open Complex Filter Function Metric Set Topology

/-- A locally finite support contained in a compact domain is finite. -/
theorem lemma23_support_finite_of_isCompact
    {X : Type*} [TopologicalSpace X] {A : Type*} [Zero A]
    {U : Set X} (hU : IsCompact U) (D : Function.locallyFinsuppWithin U A) :
    D.support.Finite := by
  classical
  choose V hV hfinite using D.supportLocallyFiniteWithinDomain
  obtain ⟨s, hcover⟩ := hU.elim_nhds_subcover' (fun x hx => V x hx)
    (fun x hx => hV x hx)
  have hUnion : (⋃ x ∈ (s : Set U), V x x.2 ∩ D.support).Finite := by
    apply s.finite_toSet.biUnion
    intro x hx
    exact hfinite x x.2
  apply hUnion.subset
  intro x hx
  have hxU : x ∈ U := D.supportWithinDomain hx
  obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.mp (hcover hxU)
  exact Set.mem_iUnion₂.mpr ⟨y, hys, ⟨hxy, hx⟩⟩

/-- Argument principle for a function analytic on a closed disk, with the zero divisor made explicit as a
finite sum of multiplicities.  The radius-one enlargement is not needed: the divisor decomposition
is performed on the closed disk itself, and analyticity then extends the derivative identity to its
boundary. -/
theorem lemma23_circleIntegral_logDeriv_eq_sum_zero_multiplicities
    {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0)
    (hDfinite : (MeromorphicOn.divisor f (closedBall 0 R)).support.Finite) :
    let K : Set ℂ := closedBall 0 R
    let D := MeromorphicOn.divisor f K
    let roots : Finset ℂ := hDfinite.toFinset
    let m : ℂ → ℕ := fun a => (D a).toNat
    (∮ z in C(0, R), logDeriv f z) =
      (2 * Real.pi * Complex.I) * ∑ a ∈ roots, (m a : ℂ) := by
  classical
  dsimp only
  let K : Set ℂ := closedBall 0 R
  let D : Function.locallyFinsuppWithin K ℤ := MeromorphicOn.divisor f K
  have hfK : AnalyticOnNhd ℂ f K := by simpa [K] using hf
  have hMer : MeromorphicOn f K := hfK.meromorphicOn
  have hDfiniteD : D.support.Finite := by simpa [D, K] using hDfinite
  have hy : (R : ℂ) ∈ sphere (0 : ℂ) R := by
    rw [mem_sphere_iff_norm]
    simp [abs_of_pos hR]
  have hyK : (R : ℂ) ∈ K := sphere_subset_closedBall hy
  have hyAnalytic : AnalyticAt ℂ f (R : ℂ) := hf (R : ℂ) hyK
  have horderY : meromorphicOrderAt f (R : ℂ) ≠ ⊤ := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hyAnalytic.meromorphicAt).2
    exact eventually_nhdsWithin_of_eventually_nhds
      ((hyAnalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp
        (hboundary (R : ℂ) hy))
  have hfiniteOrders : ∀ u : K, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    exact hMer.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected hyK u.2 horderY
  obtain ⟨g, hg, hgne, hfactor⟩ := hMer.extract_zeros_poles hfiniteOrders hDfiniteD
  let fac : ℂ → ℂ := ∏ᶠ a, (· - a) ^ D a
  let F : ℂ → ℂ := fun z => fac z * g z
  let roots : Finset ℂ := hDfiniteD.toFinset
  let m : ℂ → ℕ := fun a => (D a).toNat
  have hDnonneg : ∀ z : ℂ, 0 ≤ D z := by
    intro z
    by_cases hz : z ∈ K
    · change 0 ≤ MeromorphicOn.divisor f K z
      rw [MeromorphicOn.divisor_apply hMer hz]
      simpa only [WithTop.untop₀_nonneg] using
        (hf z hz).meromorphicOrderAt_nonneg
    · change 0 ≤ MeromorphicOn.divisor f K z
      rw [MeromorphicOn.divisor_def]
      simp [hz]
  have hfacEq : fac = lemma23WeightedRootProduct roots m := by
    funext z
    dsimp [fac]
    rw [Function.FactorizedRational.finprod_eq_fun hDfiniteD]
    change (∏ᶠ a : ℂ, (z - a) ^ D a) = lemma23WeightedRootProduct roots m z
    have hmul : (fun a : ℂ => (z - a) ^ D a).mulSupport ⊆ roots := by
      intro a ha
      by_contra hnot
      have hDa : D a = 0 := by
        by_contra hne
        apply hnot
        exact hDfiniteD.mem_toFinset.mpr (by simp [Function.mem_support, hne])
      rw [Function.mem_mulSupport] at ha
      simp [hDa] at ha
    rw [finprod_eq_prod_of_mulSupport_subset _ hmul]
    unfold lemma23WeightedRootProduct
    apply Finset.prod_congr rfl
    intro a ha
    have hcast : ((D a).toNat : ℤ) = D a := Int.toNat_of_nonneg (hDnonneg a)
    calc
      (z - a) ^ D a = (z - a) ^ ((D a).toNat : ℤ) := by rw [hcast]
      _ = (z - a) ^ (D a).toNat := by rw [zpow_natCast]
  have hFanalytic : AnalyticOnNhd ℂ F K := by
    intro z hz
    have hfacAnalytic : AnalyticAt ℂ fac z := by
      simpa [fac] using Function.FactorizedRational.analyticAt (hDnonneg z)
    simpa [F] using hfacAnalytic.mul (hg z hz)
  have hfactor' : f =ᶠ[codiscreteWithin K] F := by
    simpa [F, fac, Pi.smul_apply, smul_eq_mul] using hfactor
  have hzeroK : (0 : ℂ) ∈ K := by simp [K, hR.le]
  have hKmem : K ∈ 𝓝[≠] (0 : ℂ) := by
    rw [mem_nhdsWithin]
    refine ⟨ball 0 R, isOpen_ball, ?_, ?_⟩
    · simpa [Metric.mem_ball] using hR
    · intro z hz
      exact ball_subset_closedBall hz.1
  have hnear := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfactor') 0 hzeroK
  have hEqEvent : {z : ℂ | f z = F z} ∈ 𝓝[≠] (0 : ℂ) := by
    filter_upwards [hnear, hKmem] with z hz hzK
    rcases hz with hz | hz
    · exact hz
    · exact (hz hzK).elim
  have hEqEvent' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = F z := hEqEvent
  have hEqFreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = F z := hEqEvent'.frequently
  have hEqOn : EqOn f F K :=
    hfK.eqOn_of_preconnected_of_frequently_eq hFanalytic
      (convex_closedBall (0 : ℂ) R).isPreconnected hzeroK hEqFreq
  have hEqOnBall : EqOn f F (ball (0 : ℂ) R) := fun z hz =>
    hEqOn (ball_subset_closedBall hz)
  have hDerivOnBall : EqOn (deriv f) (deriv F) (ball (0 : ℂ) R) :=
    hEqOnBall.deriv isOpen_ball
  have hfDeriv : AnalyticOnNhd ℂ (deriv f) K := by
    intro z hz
    exact (hfK z hz).deriv
  have hFDeriv : AnalyticOnNhd ℂ (deriv F) K := by
    intro z hz
    exact (hFanalytic z hz).deriv
  have hballMem : ball (0 : ℂ) R ∈ 𝓝[≠] (0 : ℂ) := by
    rw [mem_nhdsWithin]
    refine ⟨ball 0 R, isOpen_ball, ?_, ?_⟩
    · simpa [Metric.mem_ball] using hR
    · intro z hz
      exact hz.1
  have hDerivEvent : {z : ℂ | deriv f z = deriv F z} ∈ 𝓝[≠] (0 : ℂ) :=
    Filter.mem_of_superset hballMem hDerivOnBall
  have hDerivEvent' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv f z = deriv F z := hDerivEvent
  have hDerivOn : EqOn (deriv f) (deriv F) K :=
    hfDeriv.eqOn_of_preconnected_of_frequently_eq hFDeriv
      (convex_closedBall (0 : ℂ) R).isPreconnected hzeroK hDerivEvent'.frequently
  have hroots : ∀ a ∈ roots, a ∈ ball (0 : ℂ) R := by
    intro a ha
    have hasupp : a ∈ D.support := hDfiniteD.mem_toFinset.mp ha
    have haK : a ∈ K := D.supportWithinDomain hasupp
    have hnormLe : ‖a‖ ≤ R := by
      simpa [K, Metric.mem_closedBall, dist_zero_right] using haK
    have hnormNe : ‖a‖ ≠ R := by
      intro hnorm
      have hasphere : a ∈ sphere (0 : ℂ) R := by
        simpa [Metric.mem_sphere, dist_zero_right] using hnorm
      have hvalue : f a ≠ 0 := hboundary a hasphere
      have horder0 : analyticOrderAt f a = 0 := (hf a haK).analyticOrderAt_eq_zero.mpr hvalue
      have hDa : D a = 0 := by
        change MeromorphicOn.divisor f K a = 0
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfK haK, horder0]
        simp
      exact (Function.mem_support.mp hasupp) hDa
    have hnormLt : ‖a‖ < R := lt_of_le_of_ne hnormLe hnormNe
    simpa [Metric.mem_ball, dist_zero_right] using hnormLt
  have hgneK : ∀ z ∈ K, g z ≠ 0 := by
    intro z hz
    exact hgne ⟨z, hz⟩
  have hAP := lemma23_circleIntegral_logDeriv_weighted_finite_product
    hR roots m g hroots hg hgneK
  have hFfactor : F = fun z => lemma23WeightedRootProduct roots m z * g z := by
    funext z
    simp [F, ← hfacEq]
  calc
    (∮ z in C(0, R), logDeriv f z) = (∮ z in C(0, R), logDeriv F z) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      change deriv f z / f z = deriv F z / F z
      rw [hDerivOn (sphere_subset_closedBall hz), hEqOn (sphere_subset_closedBall hz)]
    _ = (2 * Real.pi * Complex.I) * ∑ a ∈ roots, (m a : ℂ) := by
      rw [hFfactor]
      exact hAP

/-- Rouché's theorem for functions analytic on a closed disk, stated as equality of zero multiplicity sums.
This converts boundary logarithmic-derivative invariance into the interior zero count required by
the zero-spacing argument. -/
theorem lemma23_rouche_zero_multiplicity_sum
    {R : ℝ} (hR : 0 < R) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hclose : ∀ z ∈ sphere (0 : ℂ) R, ‖f z - g z‖ < ‖g z‖)
    (hDf : (MeromorphicOn.divisor f (closedBall 0 R)).support.Finite)
    (hDg : (MeromorphicOn.divisor g (closedBall 0 R)).support.Finite) :
    (∑ a ∈ hDf.toFinset, ((MeromorphicOn.divisor f (closedBall 0 R) a).toNat : ℂ)) =
      ∑ a ∈ hDg.toFinset, ((MeromorphicOn.divisor g (closedBall 0 R) a).toNat : ℂ) := by
  classical
  have hfne : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0 := by
    intro z hz hfz
    have h := hclose z hz
    rw [hfz, zero_sub, norm_neg] at h
    exact (lt_irrefl _) h
  have hgne : ∀ z ∈ sphere (0 : ℂ) R, g z ≠ 0 := by
    intro z hz hgz
    have h := hclose z hz
    rw [hgz, norm_zero] at h
    exact (not_lt_of_ge (norm_nonneg _)) h
  have hAPf := lemma23_circleIntegral_logDeriv_eq_sum_zero_multiplicities
    hR f hf hfne hDf
  have hAPg := lemma23_circleIntegral_logDeriv_eq_sum_zero_multiplicities
    hR g hg hgne hDg
  change (∮ z in C(0, R), logDeriv f z) =
    (2 * Real.pi * Complex.I) *
      ∑ a ∈ hDf.toFinset, ((MeromorphicOn.divisor f (closedBall 0 R) a).toNat : ℂ) at hAPf
  change (∮ z in C(0, R), logDeriv g z) =
    (2 * Real.pi * Complex.I) *
      ∑ a ∈ hDg.toFinset, ((MeromorphicOn.divisor g (closedBall 0 R) a).toNat : ℂ) at hAPg
  have hboundary := lemma23_circleIntegral_logDeriv_eq_of_boundary_close hR f g
    hf hg hclose
  have hscaled :
      (2 * Real.pi * Complex.I) *
          ∑ a ∈ hDf.toFinset, ((MeromorphicOn.divisor f (closedBall 0 R) a).toNat : ℂ) =
        (2 * Real.pi * Complex.I) *
          ∑ a ∈ hDg.toFinset, ((MeromorphicOn.divisor g (closedBall 0 R) a).toNat : ℂ) := by
    calc
      _ = ∮ z in C(0, R), logDeriv f z := hAPf.symm
      _ = ∮ z in C(0, R), logDeriv g z := hboundary
      _ = _ := hAPg
  have hconst : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  exact (mul_left_cancel₀ hconst) hscaled

end ZhangLS.Spec
