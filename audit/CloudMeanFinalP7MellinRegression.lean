import ZhangLS.Spec.Proposition71PrincipalEulerBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Filter
open scoped Classical Topology

example (β : Fin 3 → ℂ) (hβ : ∀j, (β j).re=0) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => lemma83Kappa β n) s=
      riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s := by
  simpa [lemma83Lambda] using proposition71_coprime_kappa_LSeries β hβ (m := 1) (by norm_num) hs

/-- Noncoprime d=m=2 retains κ(2), rather than silently cancelling it. -/
example (β : Fin 3 → ℂ) (hβ : ∀j, (β j).re=0) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => if n.Coprime 2 then lemma83Kappa β (2*n) else 0) s=
      lemma83Kappa β 2*lemma83Lambda β 4 s*
        (riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s) := by
  have he := proposition71_shifted_coprime_kappa_LSeries β hβ (d := 2) (m := 2)
    (by norm_num) (by norm_num) hs
  have hk : lemma83ModifiedKappa β 2 2 s=lemma83Kappa β 2 := by
    simpa using lemma83_modified_kappa_prime_power_excluded β Nat.prime_two (show 2 ∣ 2 from dvd_rfl) 1 s
  simpa only [hk,show 2*2=4 from rfl] using he

example (D : ℕ) (c : ℝ) (j : Fin 3) {p m : ℕ} (hp : p.Prime) (hpm : p ∣ m) (e : ℕ) :
    lemma83ModifiedKappa (lemma83PaperBeta D c) (p^e) m (1-lemma83PaperBeta D c j)=
      lemma83Kappa (lemma83PaperBeta D c) (p^e) :=
  lemma83_modified_kappa_prime_power_excluded _ hp hpm e _

example (D : ℕ) (c : ℝ) (j : Fin 3) {p m : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m) (e : ℕ) :
    lemma83ModifiedKappa (lemma83PaperBeta D c) (p^(e+1)) m (1-lemma83PaperBeta D c j)=
      ∑' k : ℕ, lemma83Kappa (lemma83PaperBeta D c) (p^(e+1+k))*
        ((p : ℂ)^(-(1-lemma83PaperBeta D c j)))^k :=
  lemma83_modified_kappa_prime_power_unexcluded _ hp hpm e _

example (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re=0) {d : ℕ} (hd : d≠0) (m : ℕ) :
    AnalyticAt ℂ (lemma83ModifiedKappa β d m) 1 ∧ AnalyticAt ℂ (lemma83Lambda β (d*m)) 1 :=
  ⟨proposition71_modified_kappa_analytic β hβ hd m 1 (by norm_num),
    proposition71_lambda_analytic β (d*m) 1 (by norm_num)⟩

/-- Literal source indices, original shifts, scale, and complete Euler integrand. -/
example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c : ℝ)
    {d₁ d₂ k p l₂ : ℕ} (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hp : 0<p) (hl₂ : 0<l₂) :
    (∑' n : Proposition71CoprimeIndex (d₂*k),
      lemma83Kappa (lemma83PaperBeta D c) (d₁*n.val)*
        lemma53PaperDelta D ((n.val : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ))))=
      ((1/(2*Real.pi) : ℝ) : ℂ)*∫t : ℝ,
        lemma83ModifiedKappa (lemma83PaperBeta D c) d₁ (d₂*k) ((3/2 : ℂ)+(t : ℂ)*I)*
        lemma83Lambda (lemma83PaperBeta D c) (d₁*(d₂*k)) ((3/2 : ℂ)+(t : ℂ)*I)*
        (riemannZeta (((3/2 : ℂ)+(t : ℂ)*I)+lemma83PaperBeta D c 0)*
          riemannZeta (((3/2 : ℂ)+(t : ℂ)*I)+lemma83PaperBeta D c 1)*
          riemannZeta (((3/2 : ℂ)+(t : ℂ)*I)+lemma83PaperBeta D c 2)/
          riemannZeta ((3/2 : ℂ)+(t : ℂ)*I))*
        (((p : ℝ)*(k : ℝ)/(l₂ : ℝ) : ℝ) : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*
        lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I) :=
  (proposition71_original_principal_mellin_source hD hL c hd₁ hd₂ hk hp hl₂).2.2

example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    {d : ℕ} (hd : d≠0) (m : ℕ) {q : ℝ} (hq : 0<q) (j : Fin 3) :
    Tendsto (fun s => (s-(1-lemma83PaperBeta D c j))*
      (lemma83ModifiedKappa (lemma83PaperBeta D c) d m s*
        lemma83Lambda (lemma83PaperBeta D c) (d*m) s*
        (riemannZeta (s+lemma83PaperBeta D c 0)*riemannZeta (s+lemma83PaperBeta D c 1)*
          riemannZeta (s+lemma83PaperBeta D c 2)/riemannZeta s)*
        (q : ℂ)^s*lemma54PaperDeltaMellin D s))
      (𝓝[≠] (1-lemma83PaperBeta D c j))
      (𝓝 (proposition71ActualR D c j*
        lemma83ModifiedKappa (lemma83PaperBeta D c) d m (1-lemma83PaperBeta D c j)*
        lemma83Lambda (lemma83PaperBeta D c) (d*m) (1-lemma83PaperBeta D c j)*
        (q : ℂ)^(1-lemma83PaperBeta D c j))) :=
  proposition71_principal_integrand_residue_limit hD hL hc hsmall hd m hq j

example (σ : ℝ) : proposition71KappaEulerEnvelope 1 σ=1 ∧
    proposition71LambdaEulerEnvelope 1 σ=1 := by
  simp [proposition71KappaEulerEnvelope,proposition71LambdaEulerEnvelope]

end ZhangLS.Spec
