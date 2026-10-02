import ZhangLS.Spec.Proposition141GlobalShift
import ZhangLS.Spec.Proposition141DivisorBounds
import ZhangLS.Spec.Proposition141SmallCoefficientSum
import ZhangLS.Spec.AllModuliLargeSieve

/-! # Genuine Section14 all-modulus second moments

Both moments are proved for arbitrary finite modulus filters, so the exact
D | h*r restriction may be retained. The κ* coefficients are arbitrary under
the original τ₅ majorant. The prime coefficients include χ and the complete
complex β. Every outer divisor factor and the r/φ(r) weight is explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

/-- Energy of the actual long coefficients on any filtered positive interval. -/
theorem proposition141_actual_kappa_interval_energy {B Y : ℝ} (hB : 0≤B) (hY : 0<Y)
    {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ) {D₁ d X : ℕ}
    (hD₁ : 0<D₁) (hd : 0<d) (hX : 1≤X) (S : Finset ℕ) (hS : S⊆Icc 1 X)
    (hYl : ∀l∈S,Y≤(l:ℝ)) {s : ℂ} (hs : s.re=1) :
    (∑ l∈S, ‖κ (D₁*d*l)/(l:ℂ)^s‖^2) ≤
      ((B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))^2/Y)*(1+Real.log (X:ℝ))^25 := by
  have he : (∑ l∈S, ‖κ (D₁*d*l)/(l:ℂ)^s‖^2) =
      ∑ l∈S, ‖κ (D₁*d*l)‖^2/(l:ℝ)^2 := by
    apply sum_congr rfl
    intro l hl
    have hlp : 0<(l:ℝ) := by exact_mod_cast (mem_Icc.mp (hS hl)).1
    rw [norm_div,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hlp,hs,
      Real.rpow_one,div_pow]
  rw [he]
  apply proposition141_bounded_coefficient_interval_energy X hX
    (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)) (by positivity)
    (fun l => κ (D₁*d*l)) S hS _ hY hYl
  intro l hl
  exact proposition141_kappa_three_factor_bound hB hκ hD₁ hd (mem_Icc.mp hl).1

/-- The genuine weighted κ* moment with an arbitrary modulus filter Q. -/
theorem proposition141_actual_weighted_kappa_mean {B Y R : ℝ}
    (hB : 0≤B) (hY : 0<Y) (hR : 1≤R)
    {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ) {D₁ d X : ℕ}
    (hD₁ : 0<D₁) (hd : 0<d) (hX : 1≤X) (S : Finset ℕ) (hS : S⊆Icc 1 X)
    (hYl : ∀l∈S,Y≤(l:ℝ)) (Q : Finset ℕ) (hQ1 : ∀r∈Q,1<r)
    (hQ : ∀r∈Q,(r:ℝ)≤2*R) {s : ℂ} (hs : s.re=1) :
    (∑ r∈Q, ((r:ℝ)/r.totient)*
      ∑ θ∈(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖∑ l∈S, (κ (D₁*d*l)/(l:ℂ)^s)*θ (l:ZMod r)‖^2) ≤
      (32+Real.pi^2)*(R^2+(X:ℝ))*
        (((B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))^2/Y)*(1+Real.log (X:ℝ))^25) := by
  have hh := primitive_large_sieve_finset_weighted Q hQ1 S
    (fun l => κ (D₁*d*l)/(l:ℂ)^s) hR hQ 0 X
    (fun l hl => ⟨Nat.zero_le _,by simpa only [zero_add] using (mem_Icc.mp (hS hl)).2⟩)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (proposition141_actual_kappa_interval_energy hB hY hκ hD₁ hd hX S hS hYl hs) (by positivity))

/-- Actual χ-weighted prime energy for every allowed complex β, expressed
using the real prime mass rather than a density assumption. -/
theorem proposition141_actual_shifted_prime_energy {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hL : 2000≤lemma23PaperL D)
    {β s : ℂ} (hβ : ‖β‖<5*lemma44PaperAlpha D) (hs : s.re=1) :
    (∑ p∈lemma56PaperPrimes D, ‖χ.chi (p:ZMod D)*(p:ℂ)^(s+β)‖^2) ≤
      2*(Real.exp 40)^2*lemma23PaperP D*lemma56PrimeMass D := by
  have hpw := lemma56_paper_prime_weight_parameters hL
  have hterm (p : ℕ) (hp : p∈lemma56PaperPrimes D) :
      ‖χ.chi (p:ZMod D)*(p:ℂ)^(s+β)‖^2 ≤
        (2*(Real.exp 40)^2*lemma23PaperP D)*(p:ℝ) := by
    have hp' := (lemma56_mem_paper_primes D p).mp hp
    have hpp : 0<(p:ℝ) := by exact_mod_cast hp'.1.pos
    have hp0 : (p:ℂ)≠0 := Nat.cast_ne_zero.mpr hp'.1.ne_zero
    have hhi : (p:ℝ)≤2*lemma23PaperP D := by linarith [hpw.2.2.2.1]
    have hbn := proposition141_small_shift_power_norm hL hβ hp'.2.1.le hhi
    have hs' : ‖(p:ℂ)^s‖=(p:ℝ) := by
      rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hpp,hs,Real.rpow_one]
    have hn : ‖χ.chi (p:ZMod D)*(p:ℂ)^(s+β)‖≤(p:ℝ)*Real.exp 40 := by
      rw [Complex.cpow_add _ _ hp0,norm_mul,norm_mul,hs']
      calc
        _ ≤ 1*((p:ℝ)*Real.exp 40) :=
          mul_le_mul (χ.chi.norm_le_one _) (mul_le_mul_of_nonneg_left hbn hpp.le)
            (mul_nonneg hpp.le (norm_nonneg _)) (by norm_num)
        _ = _ := one_mul _
    calc
      _ ≤ ((p:ℝ)*Real.exp 40)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = (Real.exp 40)^2*(p:ℝ)*(p:ℝ) := by ring
      _ ≤ (Real.exp 40)^2*(2*lemma23PaperP D)*(p:ℝ) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ p∈lemma56PaperPrimes D, (2*(Real.exp 40)^2*lemma23PaperP D)*(p:ℝ) := sum_le_sum hterm
    _ = _ := by rw [←mul_sum]; rfl

/-- Conjugating the whole polynomial supplies the exact inverse-character
moment without changing the primitive family or assuming a unit branch. -/
theorem proposition141_actual_weighted_prime_mean {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hL : 2000≤lemma23PaperL D)
    {β s : ℂ} (hβ : ‖β‖<5*lemma44PaperAlpha D) (hs : s.re=1)
    (Q : Finset ℕ) (hQ1 : ∀r∈Q,1<r) {R : ℝ} (hR : 1≤R)
    (hQ : ∀r∈Q,(r:ℝ)≤2*R) :
    (∑ r∈Q, ((r:ℝ)/r.totient)*
      ∑ θ∈(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖∑ p∈lemma56PaperPrimes D,
          χ.chi (p:ZMod D)*conj (θ (p:ZMod r))*(p:ℂ)^(s+β)‖^2) ≤
      (32+Real.pi^2)*(R^2+2*lemma23PaperP D)*
        (2*(Real.exp 40)^2*lemma23PaperP D*lemma56PrimeMass D) := by
  have hpw := lemma56_paper_prime_weight_parameters hL
  have hphi (r : ℕ) (θ : DirichletCharacter ℂ r) :
      ‖∑ p∈lemma56PaperPrimes D,
        χ.chi (p:ZMod D)*conj (θ (p:ZMod r))*(p:ℂ)^(s+β)‖ =
      ‖∑ p∈lemma56PaperPrimes D, conj (χ.chi (p:ZMod D)*(p:ℂ)^(s+β))*θ (p:ZMod r)‖ := by
    rw [←Complex.norm_conj]
    congr 1
    simp only [map_sum,map_mul,conj_conj]
    apply sum_congr rfl
    intro p hp
    ring
  simp_rw [hphi]
  have hh := primitive_large_sieve_finset_weighted Q hQ1 (lemma56PaperPrimes D)
    (fun p => conj (χ.chi (p:ZMod D)*(p:ℂ)^(s+β))) hR hQ 0 ⌊2*lemma23PaperP D⌋₊
    (fun p hp => ⟨Nat.zero_le _,by
      have hp' := (lemma56_mem_paper_primes D p).mp hp
      have hhi : (p:ℝ)≤2*lemma23PaperP D := by linarith [hpw.2.2.2.1]
      simpa only [zero_add] using Nat.le_floor hhi⟩)
  simp only [Complex.norm_conj] at hh
  apply hh.trans
  have henergy := proposition141_actual_shifted_prime_energy χ hL hβ hs
  have hM := lemma56_prime_mass_nonneg D
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  calc
    _ ≤ (32+Real.pi^2)*(R^2+(⌊2*lemma23PaperP D⌋₊:ℝ))*
      (2*(Real.exp 40)^2*lemma23PaperP D*lemma56PrimeMass D) := by gcongr
    _ ≤ _ := by
      gcongr
      exact Nat.floor_le (show 0≤2*lemma23PaperP D by positivity)

end ZhangLS.Spec
