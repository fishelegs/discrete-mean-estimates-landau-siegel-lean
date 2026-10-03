import ZhangLS.Spec.Proposition71PrincipalMellinSource
import ZhangLS.Spec.Proposition71LocalResidues
import Mathlib.NumberTheory.LSeries.Deriv
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

noncomputable def proposition71SupportedKappaCoefficient (β : Fin 3 → ℂ) (d m n : ℕ) : ℂ :=
  if n≠0 ∧ n.primeFactors ⊆ d.primeFactors ∧ n.Coprime m then lemma83Kappa β (d*n) else 0

lemma proposition71_supported_kappa_term (β : Fin 3 → ℂ) (d m : ℕ) (s : ℂ) :
    LSeries.term (proposition71SupportedKappaCoefficient β d m) s =
      {n : ℕ | n≠0 ∧ n.primeFactors ⊆ d.primeFactors ∧ n.Coprime m}.indicator
        (fun n => lemma83Kappa β (d*n)/(n : ℂ)^s) := by
  funext n
  by_cases hn : n=0
  · subst n; simp
  · rw [LSeries.term_of_ne_zero hn]
    unfold proposition71SupportedKappaCoefficient
    by_cases hh : n≠0 ∧ n.primeFactors ⊆ d.primeFactors ∧ n.Coprime m
    · rw [if_pos hh,Set.indicator_of_mem (show n ∈ {n : ℕ | n≠0 ∧ n.primeFactors ⊆ d.primeFactors ∧ n.Coprime m} from hh)]
    · rw [if_neg hh,Set.indicator_of_notMem (show n ∉ {n : ℕ | n≠0 ∧ n.primeFactors ⊆ d.primeFactors ∧ n.Coprime m} from hh),zero_div]

lemma proposition71_supported_kappa_LSeries (β : Fin 3 → ℂ) (d m : ℕ) (s : ℂ) :
    LSeries (proposition71SupportedKappaCoefficient β d m) s=lemma83ModifiedKappa β d m s := by
  rw [LSeries,proposition71_supported_kappa_term,←_root_.tsum_subtype]
  rfl

lemma proposition71_supported_kappa_summable (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) {d : ℕ} (hd : d≠0) (m : ℕ) {s : ℂ} (hs : 0<s.re) :
    LSeriesSummable (proposition71SupportedKappaCoefficient β d m) s := by
  change Summable (LSeries.term _ s)
  rw [proposition71_supported_kappa_term]
  exact summable_subtype_iff_indicator.mp (lemma83_modified_kappa_hasSum β hβ d m hd s hs).summable

/-- The actual supported infinite κ̃ sum is holomorphic throughout Re(s)>0. -/
theorem proposition71_modified_kappa_analytic (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) {d : ℕ} (hd : d≠0) (m : ℕ) :
    AnalyticOnNhd ℂ (lemma83ModifiedKappa β d m) {s : ℂ | 0<s.re} := by
  have ha : LSeries.abscissaOfAbsConv (proposition71SupportedKappaCoefficient β d m)≤(0 : ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro s hs
    exact proposition71_supported_kappa_summable β hβ hd m hs
  have he : LSeries (proposition71SupportedKappaCoefficient β d m)=lemma83ModifiedKappa β d m :=
    funext (proposition71_supported_kappa_LSeries β d m)
  rw [←he]
  intro s hs
  apply LSeries_analyticOnNhd _ s
  exact ha.trans_lt (by exact_mod_cast hs)

lemma proposition71_lambda_factor_analytic (β : Fin 3 → ℂ) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0<s.re) : AnalyticAt ℂ (lemma83LambdaFactor β p) s := by
  have hpSlit : (p : ℂ) ∈ slitPlane := Complex.natCast_mem_slitPlane.mpr hp.ne_zero
  have hpow (j : Fin 3) : AnalyticAt ℂ (fun z : ℂ => (p : ℂ)^(-z-β j)) s := by
    fun_prop (disch := exact hpSlit)
  have hbase : AnalyticAt ℂ (fun z : ℂ => (p : ℂ)^(-z)) s := by fun_prop (disch := exact hpSlit)
  have hne : 1-(p : ℂ)^(-s)≠0 := lemma83_one_sub_ne_zero (by
    rw [←lemma32_prime_monomial_eq_cpow hp.pos]
    exact lemma32_prime_monomial_norm_lt_one hp.one_lt s hs)
  exact (((analyticAt_const.sub (hpow 0)).mul (analyticAt_const.sub (hpow 1))).mul
    (analyticAt_const.sub (hpow 2))).div (analyticAt_const.sub hbase) hne

/-- No denominator vanishes in the actual finite λ Euler factors on Re(s)>0. -/
theorem proposition71_lambda_analytic (β : Fin 3 → ℂ) (m : ℕ) :
    AnalyticOnNhd ℂ (lemma83Lambda β m) {s : ℂ | 0<s.re} := by
  intro s hs
  unfold lemma83Lambda
  exact Finset.analyticAt_fun_prod m.primeFactors (fun p hp => proposition71_lambda_factor_analytic β
    (Nat.prime_of_mem_primeFactors hp) hs)

/-- The exact finite arithmetic factor and q^s are analytic at all three
original residue points, including primes shared by d and m. -/
theorem proposition71_principal_weight_analytic (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) {d : ℕ} (hd : d≠0) (m : ℕ) {q : ℝ} (hq : 0<q)
    {s : ℂ} (hs : 0<s.re) :
    AnalyticAt ℂ (fun z => lemma83ModifiedKappa β d m z*lemma83Lambda β (d*m) z*(q : ℂ)^z) s := by
  exact ((proposition71_modified_kappa_analytic β hβ hd m s hs).mul
    (proposition71_lambda_analytic β (d*m) s hs)).mul (by
      fun_prop (disch := exact Complex.ofReal_mem_slitPlane.mpr hq))

/-- Multiplication by the genuine finite arithmetic factor preserves the
punctured residue limit with its exact value, rather than an assumed pole value. -/
theorem proposition71_principal_integrand_residue_limit {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    {d : ℕ} (hd : d≠0) (m : ℕ) {q : ℝ} (hq : 0<q) (j : Fin 3) :
    Tendsto (fun s => (s-(1-lemma83PaperBeta D c j))*
      proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q s)
      (𝓝[≠] (1-lemma83PaperBeta D c j))
      (𝓝 (proposition71ActualR D c j*
        lemma83ModifiedKappa (lemma83PaperBeta D c) d m (1-lemma83PaperBeta D c j)*
        lemma83Lambda (lemma83PaperBeta D c) (d*m) (1-lemma83PaperBeta D c j)*
        (q : ℂ)^(1-lemma83PaperBeta D c j))) := by
  have hweight := (proposition71_principal_weight_analytic (lemma83PaperBeta D c)
    (lemma83_beta_re D c) hd m hq (s := 1-lemma83PaperBeta D c j) (by simp [lemma83_beta_re])).continuousAt.tendsto
  have hres := (proposition71_actual_residue_local_data hD hL hc hsmall j).2.2
  have hh := hres.mul (hweight.mono_left nhdsWithin_le_nhds)
  convert hh using 1 <;> dsimp only
  · funext s
    unfold proposition71PrincipalMellinIntegrand proposition71ResidueIntegrand
    ring
  · congr 1
    ring

end ZhangLS.Spec
