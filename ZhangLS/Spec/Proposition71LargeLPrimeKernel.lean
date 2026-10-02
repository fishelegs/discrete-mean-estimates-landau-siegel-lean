import ZhangLS.Spec.Proposition71LargeLArgument

/-! # The actual Δ-weighted prime kernel in the infinite-l tail -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
set_option maxHeartbeats 2000000

lemma proposition71_prime_second_mass_bound {D : ℕ} (hL : 3≤lemma23PaperL D) :
    (∑ p∈lemma56PaperPrimes D, (p : ℝ)^2)≤2*lemma23PaperP D*lemma56PrimeMass D := by
  calc
    _≤∑ p∈lemma56PaperPrimes D, (2*lemma23PaperP D)*(p : ℝ) := by
      apply sum_le_sum; intro p hp
      have hb := proposition71_paper_prime_le_three_halves_P hL hp
      have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
      have hp2 : (p : ℝ)≤2*lemma23PaperP D := by linarith
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hp2 (Nat.cast_nonneg p)
    _=_ := by rw [lemma56PrimeMass,mul_sum]

lemma proposition71_positive_imaginary_power_norm {u : ℝ} (hu : 0<u) (b : ℝ) :
    ‖(u : ℂ)^(I*(b : ℂ))‖=1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp

lemma proposition71_ratio_inverse_square {l q : ℝ} (hl : 0<l) (hq : 0<q) :
    (l/q)^(-2 : ℝ)=q^2/l^2 := by
  rw [Real.rpow_neg (by positivity),Real.rpow_two]
  field_simp

/-- No cancellation is assumed: the actual large-l kernel is absolutely
bounded by the original prime mass, with every h,r,l factor visible. -/
theorem proposition71_large_l_prime_kernel :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ {D r : ℕ} (θ : DirichletCharacter ℂ r),
      D₀≤D → 1<D → 2000≤lemma23PaperL D → ∀ b h l : ℝ,
        0<h → 0<r → h*(r : ℝ)≤lemma81Cutoff D → lemma23PaperP D^2<l →
          ‖∑ p∈lemma56PaperPrimes D,
            (p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r)*
              lemma53PaperDelta D (l/((p : ℝ)*h*(r : ℝ)))‖≤
            2*proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*
              lemma23PaperP D*lemma56PrimeMass D*(h*(r : ℝ)/l)^2 := by
  obtain ⟨D₀,hD₀,harg⟩ := proposition71_uniform_large_l_argument
  refine ⟨D₀,hD₀,?_⟩
  intro D r θ hDN hD hL b h l hh hr hcut hl
  have hlp : 0<l := (sq_pos_of_pos (Real.exp_pos _)).trans hl
  have hrp : 0<(r : ℝ) := by exact_mod_cast hr
  have hC := proposition71_large_delta_tail_constant_pos
  let K := proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*(h*(r : ℝ)/l)^2
  have hK : 0≤K := by dsimp [K]; positivity
  have hterm (p : ℕ) (hp : p∈lemma56PaperPrimes D) :
      ‖(p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r)*
        lemma53PaperDelta D (l/((p : ℝ)*h*(r : ℝ)))‖≤K*(p : ℝ)^2 := by
    have hpp : 0<(p : ℝ) := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.pos
    have hδ := proposition71_actual_large_delta_tail hD hL
      (harg D hDN p hp h (r : ℝ) l hh hrp hcut hl)
    rw [proposition71_ratio_inverse_square hlp (by positivity)] at hδ
    rw [norm_mul,norm_mul]
    have hn : ‖(p : ℂ)^(I*(b : ℂ))‖=1 := by
      simpa only [Complex.ofReal_natCast] using proposition71_positive_imaginary_power_norm hpp b
    rw [hn,one_mul]
    calc
      _≤1*(proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*
          (((p : ℝ)*h*(r : ℝ))^2/l^2)) :=
        mul_le_mul (θ⁻¹.norm_le_one _) hδ (norm_nonneg _) (by norm_num)
      _=_ := by dsimp [K]; ring
  calc
    _≤∑ p∈lemma56PaperPrimes D, K*(p : ℝ)^2 := (norm_sum_le _ _).trans (sum_le_sum hterm)
    _=K*(∑ p∈lemma56PaperPrimes D, (p : ℝ)^2) := by rw [mul_sum]
    _≤K*(2*lemma23PaperP D*lemma56PrimeMass D) :=
      mul_le_mul_of_nonneg_left (proposition71_prime_second_mass_bound (by linarith)) hK
    _=_ := by dsimp [K]; ring

end ZhangLS.Spec
