import ZhangLS.Spec.Lemma84TwoPoleRemoval
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Topology
set_option maxHeartbeats 1500000

/-- Open region where U is analytic and original 5.5 excludes every L-zero
except the actual simple exceptional zero. -/
def lemma84AnalyticRegion (D : ℕ) : Set ℂ :=
  {s | 9/10 < (1+s).re ∧ Lemma55InZeroRegion D (1+s)}

lemma lemma84_analytic_region_open (D : ℕ) : IsOpen (lemma84AnalyticRegion D) := by
  unfold lemma84AnalyticRegion Lemma55InZeroRegion
  have h1 : IsOpen {s : ℂ | (9/10:ℝ) < (1+s).re} :=
    isOpen_lt continuous_const (show Continuous (fun s : ℂ => (1+s).re) by fun_prop)
  have h2 : IsOpen {s : ℂ | 1-2/Real.log (D:ℝ) < (1+s).re} :=
    isOpen_lt continuous_const (show Continuous (fun s : ℂ => (1+s).re) by fun_prop)
  have h3 : IsOpen {s : ℂ | |(1+s).im| < 2*(D:ℝ)} :=
    isOpen_lt (show Continuous (fun s : ℂ => |(1+s).im|) by fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

lemma lemma84_actual_poles_distinct {ρ : ℝ} (hρ : ρ < 1) (m : ℂ) (hm : m.re = 0) :
    (ρ:ℂ)-1 ≠ -m := by
  intro he
  have hre := congrArg Complex.re he
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re,Complex.neg_re,hm,neg_zero] at hre
  linarith only [hre,hρ]

lemma lemma84_actual_two_pole_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    {ρ : ℝ} (hρ : ρ < 1) (hzero : dirichletLFunction χ (ρ:ℂ)=0)
    (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z → dirichletLFunction χ z=0 → z=(ρ:ℂ))
    (a b m : ℂ) (hm : m.re = 0) (U : ℂ → ℂ) (x : ℝ)
    (s : ℂ) (hs : s ∈ lemma84AnalyticRegion D)
    (hsa : s ≠ (ρ:ℂ)-1) (hsb : s ≠ -m) :
    let N := lemma84ActualTwoPoleNumerator χ ρ a b U x
    lemma84AnalyticCircleIntegrand χ a b m U x s =
      lemma84TwoPoleCoefficientA N ((ρ:ℂ)-1) (-m)/(s-((ρ:ℂ)-1)) +
        lemma84TwoPoleCoefficientB N ((ρ:ℂ)-1) (-m)/(s-(-m)) +
          lemma84TwoPoleCoefficientC N ((ρ:ℂ)-1) (-m)/(s-(-m))^2 +
            lemma84TwoPoleRemainder N ((ρ:ℂ)-1) (-m) s := by
  dsimp only
  have hL : dirichletLFunction χ (1+s) ≠ 0 := by
    intro he
    have hh := hunique (1+s) hs.2 he
    apply hsa
    linear_combination hh
  have hG := chi_exceptional_removed_ne_zero χ hρ.le hzero hsimple hunique hs.2
    (by linarith only [hs.1])
  rw [lemma84_actual_integrand_two_pole_factorization χ hzero a b m U x s hL hG hsa]
  exact lemma84_two_pole_decomposition _ _ _ s (lemma84_actual_poles_distinct hρ m hm) hsa hsb

/-- The actual remainder is analytic on a neighborhood of every point of the
full region; this is strong enough for either circle or closed-rectangle use. -/
lemma lemma84_actual_two_pole_remainder_analyticOnNhd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {ρ : ℝ} (hρ : ρ ≤ 1)
    (hzero : dirichletLFunction χ (ρ:ℂ)=0) (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z → dirichletLFunction χ z=0 → z=(ρ:ℂ))
    (a b m : ℂ) (U : ℂ → ℂ) (hU : AnalyticOnNhd ℂ U {z : ℂ | 9/10 < z.re})
    {x : ℝ} (hx : 0 < x)
    (ha : (ρ:ℂ)-1 ∈ lemma84AnalyticRegion D) (hb : -m ∈ lemma84AnalyticRegion D) :
    AnalyticOnNhd ℂ
      (lemma84TwoPoleRemainder (lemma84ActualTwoPoleNumerator χ ρ a b U x) ((ρ:ℂ)-1) (-m))
      (lemma84AnalyticRegion D) := by
  have hNd := lemma84_actual_two_pole_numerator_differentiableOn χ hD hρ hzero hsimple hunique
    a b U hU hx (S := lemma84AnalyticRegion D) (fun s hs => hs)
  have hopen := lemma84_analytic_region_open D
  have hRd := lemma84_two_pole_remainder_differentiableOn _ hNd ((ρ:ℂ)-1) (-m)
    (hopen.mem_nhds ha) (hopen.mem_nhds hb)
  exact hRd.analyticOnNhd hopen

end ZhangLS.Spec
