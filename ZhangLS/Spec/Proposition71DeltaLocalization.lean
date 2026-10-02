import ZhangLS.Spec.Proposition71DeltaGaussianTail
import ZhangLS.Spec.Proposition71LocalizedGeometry
import ZhangLS.Spec.AllModuliLargeSieve

/-! # Actual localization geometry for the original closed interval I(Rh) -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
set_option maxHeartbeats 2000000

lemma proposition71_paper_prime_le_three_halves_P {D p : ℕ}
    (hL : 3≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D) :
    (p : ℝ)≤(3/2 : ℝ)*lemma23PaperP D := by
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hpow : 2≤lemma23PaperL D^68 := by
    have hh := pow_le_pow_right₀ (by linarith : 1≤lemma23PaperL D) (by norm_num : 1≤(68:ℕ))
    simp only [pow_one] at hh
    linarith
  have hz : lemma23PaperL D^(-68 : ℤ)≤1/2 := by
    have hi : (lemma23PaperL D^68)⁻¹≤(2 : ℝ)⁻¹ :=
      (inv_le_inv₀ (pow_pos (by linarith : 0<lemma23PaperL D) 68) (by norm_num)).mpr hpow
    simpa only [zpow_neg,zpow_ofNat,one_div] using hi
  have hh := ((lemma56_mem_paper_primes D p).mp hp).2.2
  unfold lemma56PrimeUpper at hh
  nlinarith only [hh,mul_le_mul_of_nonneg_left hz hP]

lemma proposition71_offlocalized_clearance {D p r h l : ℕ} {R : ℝ}
    (hL : 3≤lemma23PaperL D) (hR : 1≤R) (hh : 0<h)
    (hr : r∈primitiveDyadicModuli R) (hp : p∈lemma56PaperPrimes D)
    (hoff : (l : ℝ)<proposition71LocalScale D R h/3 ∨
      4*proposition71LocalScale D R h<(l : ℝ)) :
    lemma51PaperT0 D/3≤
      |(l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))-lemma51PaperT0 D| := by
  have hr' := mem_primitiveDyadicModuli.mp hr
  have hp' := lemma56_mem_paper_primes D p |>.mp hp
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hT : 0≤lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hRp : 0<R := by linarith
  have hhp : 0<(h : ℝ) := by exact_mod_cast hh
  have hrp : 0<(r : ℝ) := by exact_mod_cast (show 0<r by omega)
  have hpp : 0<(p : ℝ) := by exact_mod_cast hp'.1.pos
  have hden : 0<(p : ℝ)*(h : ℝ)*(r : ℝ) := by positivity
  have hlo : lemma23PaperP D*R*(h : ℝ)≤(p : ℝ)*(h : ℝ)*(r : ℝ) := by
    calc
      _≤(p : ℝ)*(r : ℝ)*(h : ℝ) := by gcongr; exact hp'.2.1.le; exact hr'.2.1
      _=_ := by ring
  have hhi : (p : ℝ)*(h : ℝ)*(r : ℝ)≤3*lemma23PaperP D*R*(h : ℝ) := by
    calc
      _=(p : ℝ)*(r : ℝ)*(h : ℝ) := by ring
      _≤((3/2 : ℝ)*lemma23PaperP D)*(2*R)*(h : ℝ) := by
        gcongr
        · exact proposition71_paper_prime_le_three_halves_P hL hp
        · exact hr'.2.2.le
      _=_ := by ring
  rcases hoff with hoff|hoff
  · have hx : (l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))≤lemma51PaperT0 D/3 := by
      apply (div_le_iff₀ hden).mpr
      apply hoff.le.trans
      have hv := mul_le_mul_of_nonneg_left hlo (div_nonneg hT (by norm_num : (0:ℝ)≤3))
      convert hv using 1 <;> unfold proposition71LocalScale <;> ring
    have habs := neg_le_abs ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))-lemma51PaperT0 D)
    linarith
  · have hx : (4/3 : ℝ)*lemma51PaperT0 D≤(l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ)) := by
      apply (le_div_iff₀ hden).mpr
      have hv := mul_le_mul_of_nonneg_left hhi (by positivity : 0≤(4/3 : ℝ)*lemma51PaperT0 D)
      apply hv.trans
      apply le_trans _ hoff.le
      unfold proposition71LocalScale
      ring_nf
      exact le_rfl
    have habs := le_abs_self ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))-lemma51PaperT0 D)
    linarith

/-- Every omitted positive coprime l term is genuinely off-center. No endpoint
is removed: the original l interval is closed at both ends. -/
theorem proposition71_actual_offlocalized_delta {D p r h l : ℕ} {R : ℝ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hR : 1≤R) (hh : 0<h)
    (hr : r∈primitiveDyadicModuli R) (hp : p∈lemma56PaperPrimes D)
    (hl : 0<l) (hc : l.Coprime h) (hnot : l∉proposition71LocalizedIndices D R h) :
    ‖lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ)))‖≤
      proposition71OffCenterDeltaConstant*Real.exp (-lemma23PaperL D^10/2) := by
  have hoff : (l : ℝ)<proposition71LocalScale D R h/3 ∨
      4*proposition71LocalScale D R h<(l : ℝ) := by
    by_contra hn
    push_neg at hn
    exact hnot (proposition71_mem_localized_indices.mpr ⟨hl,hn.1,hn.2,hc⟩)
  have hpp : 0<(p : ℝ) := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.pos
  have hrp : 0<(r : ℝ) := by exact_mod_cast (show 0<r from Nat.zero_lt_of_lt (mem_primitiveDyadicModuli.mp hr).1)
  have hhp : 0<(h : ℝ) := by exact_mod_cast hh
  have hlp : 0<(l : ℝ) := by exact_mod_cast hl
  exact proposition71_actual_delta_offcenter hD hL (by positivity)
    (proposition71_offlocalized_clearance (by linarith) hR hh hr hp hoff)

end ZhangLS.Spec
