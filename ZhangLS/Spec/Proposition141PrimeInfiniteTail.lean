import ZhangLS.Spec.Proposition141InfiniteCoefficientTail
import ZhangLS.Spec.Proposition141GlobalShift
import ZhangLS.Spec.TauDirichletValues

/-! # The actual long-index tail after prime summation

The infinite κ* tail is absolutely summable, its exact Dirichlet envelope has
mass (π²/6)^5≤243, and all finite/infinite interchanges are justified.
The original χ-conjugate-character coefficient and full complex β remain.
This bound deliberately retains the full (2Phr)² scale before outer sums.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

lemma proposition141_tau_five_square_mass_eq :
    proposition141TauFiveSquareMass=(Real.pi^2/6)^5 := tauDirichlet_square_mass 4

lemma proposition141_tau_five_square_mass_le : proposition141TauFiveSquareMass≤243 :=
  tauDirichlet_five_square_mass_le

/-- Numerical, uniform version of the actual infinite coefficient tail. -/
theorem proposition141_dilated_delta_tail_explicit_bound {D N : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (θ : DirichletCharacter ℂ N)
    {B : ℝ} (hB : 0≤B) {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ)
    {D₁ d : ℕ} (hD₁ : 0<D₁) (hd : 0<d) {q U : ℝ} (hq : 0<q)
    (hU : q*lemma51PaperT0 D^(51/50:ℝ)≤U) :
    ‖∑'l:ℕ,proposition141DilatedDeltaTailTerm D θ κ D₁ d q U l‖ ≤
      243*proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2*
        (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)) := by
  apply (proposition141_dilated_delta_tail_bound hD hL θ hB hκ hD₁ hd hq hU).trans
  have hC := proposition71_large_delta_tail_constant_pos.le
  have hh := mul_le_mul_of_nonneg_left proposition141_tau_five_square_mass_le
    (show 0≤proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2*
      (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)) by positivity)
  convert hh using 1 <;> ring

lemma proposition141_prime_tail_shift_norm {D N p : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (hL : 2000≤lemma23PaperL D) {β : ℂ} (hβ : ‖β‖<5*lemma44PaperAlpha D)
    (hp : p∈lemma56PaperPrimes D) :
    ‖χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β‖≤Real.exp 40 := by
  have hpw := lemma56_paper_prime_weight_parameters hL
  have hp' := (lemma56_mem_paper_primes D p).mp hp
  have hhi : (p:ℝ)≤2*lemma23PaperP D := by linarith [hpw.2.2.2.1]
  have hb := proposition141_small_shift_power_norm hL hβ hp'.2.1.le hhi
  have hc : ‖χ.chi (p:ZMod D)*conj (θ (p:ZMod N))‖≤1 := by
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_one₀ (χ.chi.norm_le_one _) (norm_nonneg _) (θ.norm_le_one _)
  rw [norm_mul]
  simpa only [one_mul,Complex.ofReal_natCast] using mul_le_mul hc hb (norm_nonneg _) (by norm_num : (0:ℝ)≤1)

/-- A cardinal bound by the actual mass, requiring no prime-density theorem. -/
lemma proposition141_prime_card_le_mass (D : ℕ) :
    ((lemma56PaperPrimes D).card:ℝ)≤lemma56PrimeMass D := by
  calc
    _ = ∑p∈lemma56PaperPrimes D,(1:ℝ) := by simp
    _ ≤ ∑p∈lemma56PaperPrimes D,(p:ℝ) := by
      apply sum_le_sum
      intro p hp
      exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.one_le
    _ = _ := rfl

/-- Full prime-summed, absolutely convergent actual long-index tail, with
its complete support scale and coefficient factors still explicit. -/
theorem proposition141_prime_summed_infinite_tail {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {β : ℂ} (hβ : ‖β‖<5*lemma44PaperAlpha D)
    {B : ℝ} (hB : 0≤B) {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ)
    {D₁ d : ℕ} (hD₁ : 0<D₁) (hd : 0<d) {h r U : ℝ} (hh : 0<h) (hr : 0<r)
    (hU : (2*lemma23PaperP D*h*r)*lemma51PaperT0 D^(51/50:ℝ)≤U) :
    ‖∑p∈lemma56PaperPrimes D,
      (χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β)*
        ∑'l:ℕ,proposition141DilatedDeltaTailTerm D θ κ D₁ d ((p:ℝ)*h*r) U l‖ ≤
      (243*Real.exp 40*proposition71LargeDeltaTailConstant)*
        Real.exp (-lemma23PaperL D^10/2)*(2*lemma23PaperP D*h*r)^2*
        (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))*lemma56PrimeMass D := by
  let K := 243*proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*
    (2*lemma23PaperP D*h*r)^2*(B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))
  have hC := proposition71_large_delta_tail_constant_pos.le
  have hK : 0≤K := by dsimp [K]; positivity
  have hpw := lemma56_paper_prime_weight_parameters hL
  have hterm (p : ℕ) (hp : p∈lemma56PaperPrimes D) :
      ‖(χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β)*
        ∑'l:ℕ,proposition141DilatedDeltaTailTerm D θ κ D₁ d ((p:ℝ)*h*r) U l‖≤Real.exp 40*K := by
    have hp' := (lemma56_mem_paper_primes D p).mp hp
    have hpp : 0<(p:ℝ) := by exact_mod_cast hp'.1.pos
    have hhi : (p:ℝ)≤2*lemma23PaperP D := by linarith [hpw.2.2.2.1]
    have hq : (p:ℝ)*h*r≤2*lemma23PaperP D*h*r := by gcongr
    have hcut : ((p:ℝ)*h*r)*lemma51PaperT0 D^(51/50:ℝ)≤U :=
      (mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg (by
        exact pow_nonneg (by linarith : 0≤lemma23PaperL D) _) _)).trans hU
    have hb := proposition141_dilated_delta_tail_explicit_bound hD hL θ hB hκ hD₁ hd
      (mul_pos (mul_pos hpp hh) hr) hcut
    have hb' : ‖∑'l:ℕ,proposition141DilatedDeltaTailTerm D θ κ D₁ d ((p:ℝ)*h*r) U l‖≤K := by
      apply hb.trans
      dsimp [K]
      gcongr
    rw [norm_mul]
    exact mul_le_mul (proposition141_prime_tail_shift_norm χ θ hL hβ hp) hb' (norm_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ ∑p∈lemma56PaperPrimes D,‖(χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β)*
        ∑'l:ℕ,proposition141DilatedDeltaTailTerm D θ κ D₁ d ((p:ℝ)*h*r) U l‖ := norm_sum_le _ _
    _ ≤ ∑p∈lemma56PaperPrimes D,Real.exp 40*K := sum_le_sum hterm
    _ = ((lemma56PaperPrimes D).card:ℝ)*(Real.exp 40*K) := by simp
    _ ≤ lemma56PrimeMass D*(Real.exp 40*K) := mul_le_mul_of_nonneg_right (proposition141_prime_card_le_mass D) (by positivity)
    _ = _ := by dsimp [K]; ring

/-- The infinite-long and finite-prime sums commute by proved absolute
summability of each original tail, not a formal rearrangement. -/
theorem proposition141_prime_tail_interchange {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (β : ℂ)
    {B : ℝ} (hB : 0≤B) {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ)
    {D₁ d : ℕ} (hD₁ : 0<D₁) (hd : 0<d) {h r U : ℝ} (hh : 0<h) (hr : 0<r)
    (hU : (2*lemma23PaperP D*h*r)*lemma51PaperT0 D^(51/50:ℝ)≤U) :
    (∑'l:ℕ,∑p∈lemma56PaperPrimes D,
      (χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β)*
        proposition141DilatedDeltaTailTerm D θ κ D₁ d ((p:ℝ)*h*r) U l) =
    ∑p∈lemma56PaperPrimes D,
      (χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β)*
        ∑'l:ℕ,proposition141DilatedDeltaTailTerm D θ κ D₁ d ((p:ℝ)*h*r) U l := by
  have hpw := lemma56_paper_prime_weight_parameters hL
  have hs (p : ℕ) (hp : p∈lemma56PaperPrimes D) :
      Summable (fun l:ℕ => (χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β)*
        proposition141DilatedDeltaTailTerm D θ κ D₁ d ((p:ℝ)*h*r) U l) := by
    have hp' := (lemma56_mem_paper_primes D p).mp hp
    have hpp : 0<(p:ℝ) := by exact_mod_cast hp'.1.pos
    have hhi : (p:ℝ)≤2*lemma23PaperP D := by linarith [hpw.2.2.2.1]
    apply (proposition141_dilated_delta_tail_summable hD hL θ hB hκ hD₁ hd
      (mul_pos (mul_pos hpp hh) hr) ?_).mul_left
    apply le_trans _ hU
    have ht0 : 0≤lemma51PaperT0 D := le_trans (by norm_num) (proposition141_t0_log_bounds hL).1
    gcongr
  rw [Summable.tsum_finsetSum hs]
  simp only [tsum_mul_left]

end ZhangLS.Spec
