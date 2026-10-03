import ZhangLS.Spec.Proposition71GcdAttachment

/-! Actual local principal-contour scales from the original strict support.
The complete q=p*k/l2 is bounded below by T^2; no numerical contour size is
assumed independently of the coefficient support. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2500000

theorem proposition71_principal_local_scales {D p d₁ d₂ k l₂ : ℕ}
    (hL : 3≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hl₂ : 0<l₂)
    (hs₂ : d₂*l₂∈lemma81PolynomialIndices D)
    (hsk : d₁*d₂*k∈lemma81PolynomialIndices D) :
    k∈lemma81PolynomialIndices D ∧ l₂∈lemma81PolynomialIndices D ∧
      1≤(p : ℝ)*(k : ℝ)/(l₂ : ℝ) ∧
      (p : ℝ)*(k : ℝ)/(l₂ : ℝ)≤lemma23PaperP D^10 ∧
      lemma56PaperT D^2<(p : ℝ)*(k : ℝ)/(l₂ : ℝ) := by
  have hkS := (proposition71_short_factors (Nat.mul_pos hd₁ hd₂) hk hsk).2
  have hlS := (proposition71_short_factors hd₂ hl₂ hs₂).2
  have hsc := (proposition71_prime_short_absolute_scales hL hp hkS).2.2
  have hlR : 0<(l₂ : ℝ) := by exact_mod_cast hl₂
  have hl1 : 1≤(l₂ : ℝ) := by exact_mod_cast hl₂
  have hk1 : 1≤(k : ℝ) := by exact_mod_cast hk
  have hpp := (lemma56_mem_paper_primes D p).mp hp
  have hpR : 0<(p : ℝ) := by exact_mod_cast hpp.1.pos
  have hT : 0<lemma56PaperT D := Real.exp_pos _
  have hT1 : 1≤lemma56PaperT D := by
    apply Real.one_le_exp_iff.mpr
    exact Real.rpow_nonneg (Real.log_natCast_nonneg D) _
  have hlcut := ((proposition71_mem_indices D l₂).mp hlS).2
  have hlT : (l₂ : ℝ)*lemma56PaperT D^2<lemma23PaperP D := by
    have hh := mul_lt_mul_of_pos_right hlcut (sq_pos_of_pos hT)
    unfold lemma81Cutoff at hh
    have he : lemma23PaperP D*lemma56PaperT D^(-2 : ℤ)*lemma56PaperT D^2=lemma23PaperP D := by
      rw [zpow_neg,zpow_ofNat]
      field_simp
    rwa [he] at hh
  have hqT : lemma56PaperT D^2<(p : ℝ)*(k : ℝ)/(l₂ : ℝ) := by
    apply (lt_div_iff₀ hlR).mpr
    calc
      lemma56PaperT D^2*(l₂ : ℝ)<lemma23PaperP D := by simpa only [mul_comm] using hlT
      _<(p : ℝ) := hpp.2.1
      _≤(p : ℝ)*(k : ℝ) := le_mul_of_one_le_right hpR.le hk1
  refine ⟨hkS,hlS,?_,?_,hqT⟩
  · exact (one_le_pow₀ hT1).trans hqT.le
  · exact (div_le_self (mul_nonneg hpR.le (le_trans (by norm_num) hk1)) hl1).trans hsc.2

end ZhangLS.Spec
