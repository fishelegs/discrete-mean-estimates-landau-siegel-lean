import ZhangLS.Spec.Proposition141Objects
import ZhangLS.Spec.Proposition141SmallConductor
import ZhangLS.Spec.Lemma61GaussianWeights

/-! # Genuine Section 14 coefficient supports and convergence

The closed n≤2P₄ support is kept. All bounds here precede the choices of
characters and coefficients. In particular D*k<p is derived, not assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Filter Finset
open scoped Classical

/-- Every actual κ* series converges absolutely in Re(s)>1, directly from
its τ₅ bound. No identification with Section 7 κ is assumed. -/
theorem proposition141_kappa_series_summable {p : ℕ} {B : ℝ} {κ : ℕ → ℂ}
    (hB : 0 ≤ B) (hκ : Proposition141KappaBound B κ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => κ n * ψ (n : ZMod p)) s := by
  have ht := ((lemma32_tau_lseries_summable 4 s hs).smul (B : ℂ)).norm
  rw [LSeriesSummable,← summable_norm_iff]
  apply ht.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  by_cases hn : n = 0
  · subst n; simp
  apply LSeries.norm_term_le
  simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hB,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left (ψ.norm_le_one _) (norm_nonneg _)).trans
    (by simpa using hκ n (Nat.pos_of_ne_zero hn))

/-- Actual Section 14 support, including equality at 2P₄. -/
theorem proposition141_nonzero_support {D n : ℕ} {B : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D B a) (hn : a n ≠ 0) :
    (n : ℝ) ≤ 2 * lemma61PaperP4 D :=
  le_of_not_gt (fun h => hn (ha.2 n h))

/-- No positive coefficient in the original d,k sums is lost when those
indices are restricted to the actual finite box. -/
theorem proposition141_nonzero_product_indices {D d k : ℕ} {B : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D B a) (hd : 0 < d) (hk : 0 < k)
    (han : a (d*k) ≠ 0) :
    d ∈ proposition141Indices D ∧ k ∈ proposition141Indices D := by
  have hc := proposition141_nonzero_support ha han
  have hdd : d ≤ d*k := by nlinarith
  have hkd : k ≤ d*k := by nlinarith
  rw [proposition141_mem_indices,proposition141_mem_indices]
  exact ⟨⟨hd,(by exact_mod_cast hdd : (d : ℝ) ≤ ((d*k : ℕ) : ℝ)).trans hc⟩,
    ⟨hk,(by exact_mod_cast hkd : (k : ℝ) ≤ ((d*k : ℕ) : ℝ)).trans hc⟩⟩

theorem proposition141_omitted_coefficient_zero {D d k : ℕ} {B : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D B a) (hd : 0 < d) (hk : 0 < k)
    (hout : ¬(d ∈ proposition141Indices D ∧ k ∈ proposition141Indices D)) :
    a (d*k) = 0 := by
  by_contra hn
  exact hout (proposition141_nonzero_product_indices ha hd hk hn)

/-- Uniform domination of the paper's height t₀=(log D)^519 by D. -/
theorem proposition141_uniform_t0_le_D :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → lemma51PaperT0 D ≤ D := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := ht.eventually
    ((Real.isLittleO_pow_exp_atTop (n := 519)).bound (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨max N 2,le_max_right _ _,?_⟩
  intro D hD
  have hD2 : 2 ≤ D := (le_max_right N 2).trans hD
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hh := hN D ((le_max_left N 2).trans hD)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg D) 519),
    abs_of_pos (Real.exp_pos _),one_mul,lemma51PaperT0,lemma23PaperL,Real.exp_log hDp,
    abs_of_pos hDp] using hh

/-- Even the extra D required by the common-modulus bridge is smaller than
p throughout the supported range: 2D²P₄≤P eventually. -/
theorem proposition141_uniform_support_modulus_bound :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      2 * (D : ℝ)^2 * lemma61PaperP4 D ≤ lemma23PaperP D := by
  obtain ⟨N₁,hN₁,h₁⟩ := proposition141_uniform_t0_le_D
  obtain ⟨N₂,hN₂,h₂⟩ := proposition141_uniform_fourth_lt_T
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro D hD
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hN₁.trans ((le_max_left N₁ N₂).trans hD)
  have hDt := h₁ D ((le_max_left N₁ N₂).trans hD)
  have hT := h₂ D ((le_max_right N₁ N₂).trans hD)
  have hT1 : 1 ≤ lemma56PaperT D := by
    have hD1 : (1 : ℝ) ≤ (D : ℝ)^4 := one_le_pow₀ (by linarith : (1:ℝ) ≤ D)
    exact hD1.trans hT.le
  have hT2 : 2 * (D : ℝ)^2 * lemma51PaperT0 D ≤ lemma56PaperT D^2 := by
    have ha : 2 * (D : ℝ)^2 * lemma51PaperT0 D ≤ 2 * (D : ℝ)^3 := by nlinarith
    have hb : 2 * (D : ℝ)^3 ≤ (D : ℝ)^4 := by nlinarith [mul_nonneg (show 0≤(D:ℝ)^3 by positivity) (show 0≤(D:ℝ)-2 by linarith)]
    have hc : lemma56PaperT D ≤ lemma56PaperT D^2 := by nlinarith
    exact ha.trans (hb.trans (hT.le.trans hc))
  have hP := (Real.exp_pos (lemma23PaperL D^9))
  have hmul := mul_le_mul_of_nonneg_left hT2 hP.le
  have hscale := lemma61_complementary_scales (D := D)
  have hTp : 0 < lemma56PaperT D^2 := sq_pos_of_pos (Real.exp_pos _)
  apply (mul_le_mul_iff_left₀ hTp).mp
  calc
    (2*(D:ℝ)^2*lemma61PaperP4 D)*(lemma56PaperT D^2) =
        lemma23PaperP D*(2*(D:ℝ)^2*lemma51PaperT0 D) := by
          rw [mul_assoc (2*(D:ℝ)^2),hscale]; ring
    _ ≤ lemma23PaperP D * lemma56PaperT D^2 := hmul

/-- The prime p is a unit modulo D*k, with the short k branch actually
proved from a*(d*k)≠0 and the paper's support. -/
theorem proposition141_supported_modulus_coprime_prime {D p d k : ℕ} {B : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D B a)
    (hD : 1 < D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D ≤ lemma23PaperP D)
    (hp : p ∈ lemma56PaperPrimes D) (hd : 0 < d) (hk : 0 < k)
    (han : a (d*k) ≠ 0) : p.Coprime (D*k) := by
  have hcut := (proposition141_mem_indices D k).mp
    (proposition141_nonzero_product_indices ha hd hk han).2
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast (by omega : 1≤D)
  have hP4 : 0 ≤ lemma61PaperP4 D := (lemma61_P4_pos hD).le
  have hdk : ((D*k : ℕ) : ℝ) ≤ lemma23PaperP D := by
    have hmono : (D:ℝ) ≤ (D:ℝ)^2 := by nlinarith
    calc
      ((D*k : ℕ) : ℝ) = (D:ℝ)*(k:ℝ) := by norm_cast
      _ ≤ (D:ℝ)*(2*lemma61PaperP4 D) := mul_le_mul_of_nonneg_left hcut.2 (Nat.cast_nonneg _)
      _ ≤ 2*(D:ℝ)^2*lemma61PaperP4 D := by nlinarith
      _ ≤ lemma23PaperP D := hmod
  obtain ⟨hpp,hpP,_⟩ := (lemma56_mem_paper_primes D p).mp hp
  have hlt : D*k < p := by exact_mod_cast hdk.trans_lt hpP
  apply hpp.coprime_iff_not_dvd.mpr
  intro hdiv
  exact (not_le_of_gt hlt) (Nat.le_of_dvd (Nat.mul_pos (by omega) hk) hdiv)

end ZhangLS.Spec
