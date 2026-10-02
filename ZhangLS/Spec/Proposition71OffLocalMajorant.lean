import ZhangLS.Spec.Proposition71SigmaSeries

/-! # A genuine summable envelope for the literal σ−localization complement

The complement itself is defined by omitted indices in Proposition71SigmaSeries.
The finite l≤P² portion uses the actual off-center Δ estimate, while the
infinite portion uses the actual large-l kernel. All h,r and τ₅ factors remain.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

lemma proposition71_offlocal_prime_kernel {D r h l : ℕ} {R : ℝ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hR : 1≤R) (hh : 0<h)
    (hr : r∈primitiveDyadicModuli R) (hl : 0<l) (hc : l.Coprime h)
    (hnot : l∉proposition71LocalizedIndices D R h)
    (b : ℝ) (θ : DirichletCharacter ℂ r) :
    ‖∑ p∈lemma56PaperPrimes D, (p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r)*
      lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ)))‖≤
        proposition71OffCenterDeltaConstant*Real.exp (-lemma23PaperL D^10/2)*lemma56PrimeMass D := by
  have hC := proposition71_offcenter_delta_constant_pos
  let K := proposition71OffCenterDeltaConstant*Real.exp (-lemma23PaperL D^10/2)
  have hK : 0≤K := by dsimp [K]; positivity
  calc
    _≤∑ p∈lemma56PaperPrimes D, K*(p : ℝ) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro p hp
      have hpp : 0<(p : ℝ) := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.pos
      have hp1 : (1:ℝ)≤p := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.one_le
      have hδ := proposition71_actual_offlocalized_delta hD hL hR hh hr hp hl hc hnot
      have hn : ‖(p : ℂ)^(I*(b : ℂ))‖=1 := by
        simpa only [Complex.ofReal_natCast] using proposition71_positive_imaginary_power_norm hpp b
      rw [norm_mul,norm_mul,hn,one_mul]
      calc
        _≤1*K := mul_le_mul (θ⁻¹.norm_le_one _) hδ (norm_nonneg _) (by norm_num)
        _≤_ := by simpa only [one_mul] using le_mul_of_one_le_right hK hp1
    _=_ := by rw [lemma56PrimeMass,mul_sum]

lemma proposition71_offlocal_sigma_term {D r h l : ℕ} {R : ℝ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hR : 1≤R) (hh : 0<h)
    (hr : r∈primitiveDyadicModuli R) (hl : 0<l) (hc : l.Coprime h)
    (hnot : l∉proposition71LocalizedIndices D R h)
    (c b : ℝ) {B : ℝ} (hB : 0≤B) (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤B)
    (d : ℕ) (θ : DirichletCharacter ℂ r) :
    ‖proposition71SigmaTerm D c b a h d θ l‖≤
      B*(lemma34Tau 5 d : ℝ)*(lemma34Tau 5 l : ℝ)*
        (proposition71OffCenterDeltaConstant*Real.exp (-lemma23PaperL D^10/2)*lemma56PrimeMass D) := by
  have hk := proposition71_offlocal_prime_kernel hD hL hR hh hr hl hc hnot b θ
  have hf := proposition71_actual_dilated_kappa_majorant D c d hB a ha l
  simp only [proposition71SigmaTerm,if_pos (show 0<l ∧ l.Coprime h from ⟨hl,hc⟩),norm_mul]
  calc
    _≤(B*(lemma34Tau 5 d : ℝ)*(lemma34Tau 5 l : ℝ))*1*
        (proposition71OffCenterDeltaConstant*Real.exp (-lemma23PaperL D^10/2)*lemma56PrimeMass D) := by
      gcongr
      exact θ.norm_le_one _
    _=_ := by ring

/-- The literal infinite off-localization subseries has a proved τ₅/l²
majorant. The P⁴ loss is explicit and will be paid for in the outer sum. -/
theorem proposition71_offlocal_term_majorant :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ {D r : ℕ} (θ : DirichletCharacter ℂ r),
      D₀≤D → 1<D → 2000≤lemma23PaperL D → ∀ c b B : ℝ, 0≤B →
        ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) → ∀ R : ℝ, 1≤R →
          ∀ h d : ℕ, 0<h → r∈primitiveDyadicModuli R →
            ((h*r : ℕ) : ℝ)≤lemma81Cutoff D → ∀ l : ℕ,
              ‖proposition71SigmaOffLocalTerm D c b a R h d θ l‖≤
                ((proposition71OffCenterDeltaConstant+2*proposition71LargeDeltaTailConstant)*
                  B*(lemma34Tau 5 d : ℝ)*((h : ℝ)*(r : ℝ))*lemma56PrimeMass D*
                    lemma23PaperP D^4*Real.exp (-lemma23PaperL D^10/2))*
                      ((lemma34Tau 5 l : ℝ)/(l : ℝ)^2) := by
  obtain ⟨D₀,hD₀,hlarge⟩ := proposition71_large_l_term_majorant
  refine ⟨D₀,hD₀,?_⟩
  intro D r θ hDN hD hL c b B hB a ha R hR h d hh hr hcut l
  have hrp : 0<r := Nat.zero_lt_of_lt (mem_primitiveDyadicModuli.mp hr).1
  have hM := lemma56_prime_mass_nonneg D
  have hC := proposition71_offcenter_delta_constant_pos
  have hC' := proposition71_large_delta_tail_constant_pos
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg (by linarith : 0≤lemma23PaperL D) 9)
  have hhr1 : 1≤(h : ℝ)*(r : ℝ) := by exact_mod_cast Nat.mul_pos hh hrp
  have hhrP : (h : ℝ)*(r : ℝ)≤lemma23PaperP D := by
    simpa only [Nat.cast_mul] using hcut.trans (proposition71_cutoff_le_P D)
  let C := proposition71OffCenterDeltaConstant+2*proposition71LargeDeltaTailConstant
  have hCp : 0<C := by dsimp [C]; positivity
  unfold proposition71SigmaOffLocalTerm
  split_ifs with hloc
  · simp only [norm_zero]; positivity
  by_cases helig : 0<l ∧ l.Coprime h
  swap
  · simp only [proposition71SigmaTerm,if_neg helig,norm_zero]; positivity
  have hlp : 0<(l : ℝ) := by exact_mod_cast helig.1
  by_cases hsmall : (l : ℝ)≤lemma23PaperP D^2
  · have hs := proposition71_offlocal_sigma_term hD hL hR hh hr helig.1 helig.2 hloc c b hB a ha d θ
    have hlsq : (l : ℝ)^2≤lemma23PaperP D^4 := by
      simpa only [←pow_mul] using pow_le_pow_left₀ hlp.le hsmall 2
    have hquot : 1≤lemma23PaperP D^4/(l : ℝ)^2 := (one_le_div (pow_pos hlp 2)).mpr hlsq
    have hfac : proposition71OffCenterDeltaConstant≤C*((h : ℝ)*(r : ℝ))*(lemma23PaperP D^4/(l : ℝ)^2) := by
      calc
        _≤C := by dsimp [C]; linarith
        _≤C*((h : ℝ)*(r : ℝ)) := le_mul_of_one_le_right hCp.le hhr1
        _≤_ := le_mul_of_one_le_right (by positivity) hquot
    apply hs.trans
    have hv := mul_le_mul_of_nonneg_left hfac
      (by positivity : 0≤B*(lemma34Tau 5 d : ℝ)*(lemma34Tau 5 l : ℝ)*lemma56PrimeMass D*
        Real.exp (-lemma23PaperL D^10/2))
    convert hv using 1 <;> dsimp [C] <;> ring
  · have hlt := lt_of_not_ge hsmall
    have hs := hlarge θ hDN hD hL c b B hB a ha h d hh hrp hcut l
    simp only [proposition71SigmaLargeLTerm,if_pos hlt] at hs
    have hbudget : lemma23PaperP D*((h : ℝ)*(r : ℝ))^2≤
        lemma23PaperP D^4*((h : ℝ)*(r : ℝ)) := by
      have hv := mul_le_mul_of_nonneg_left hhrP (by positivity : 0≤lemma23PaperP D*((h : ℝ)*(r : ℝ)))
      have hp24 : lemma23PaperP D^2≤lemma23PaperP D^4 := pow_le_pow_right₀ hP1 (by norm_num)
      calc
        _≤lemma23PaperP D^2*((h : ℝ)*(r : ℝ)) := by convert hv using 1 <;> ring
        _≤_ := mul_le_mul_of_nonneg_right hp24 (by positivity)
    have hc : 2*proposition71LargeDeltaTailConstant≤C := by dsimp [C]; linarith
    apply hs.trans
    calc
      _=(B*(lemma34Tau 5 d : ℝ)*lemma56PrimeMass D*Real.exp (-lemma23PaperL D^10/2)*
          ((lemma34Tau 5 l : ℝ)/(l : ℝ)^2))*
            (2*proposition71LargeDeltaTailConstant*(lemma23PaperP D*((h : ℝ)*(r : ℝ))^2)) := by ring
      _≤(B*(lemma34Tau 5 d : ℝ)*lemma56PrimeMass D*Real.exp (-lemma23PaperL D^10/2)*
          ((lemma34Tau 5 l : ℝ)/(l : ℝ)^2))*(C*(lemma23PaperP D^4*((h : ℝ)*(r : ℝ)))) := by gcongr
      _=_ := by dsimp [C]; ring

end ZhangLS.Spec
