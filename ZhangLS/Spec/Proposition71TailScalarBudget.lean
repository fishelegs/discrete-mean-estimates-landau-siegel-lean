import ZhangLS.Spec.Proposition71DeltaLargeTail

/-! # Explicit absorption of all polynomial-exponential losses in the Δ tails -/
set_option autoImplicit false
namespace ZhangLS.Spec
set_option maxHeartbeats 2000000

lemma proposition71_tail_scalar_budget {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) :
    lemma23PaperP D^6*lemma23PaperL D^72*Real.exp (-lemma23PaperL D^10/2)≤(D : ℝ)⁻¹ := by
  let L := lemma23PaperL D
  have hLp : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have hDp : 0<(D : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hL9 : L≤L^9 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1≤(9:ℕ))
  have hlarge : 158*L^9≤L^10 := by
    have hh := mul_le_mul_of_nonneg_left (show 158≤L by dsimp [L]; linarith) (pow_nonneg hLp.le 9)
    convert hh using 1 <;> ring
  have hex : 6*L^9+72*L-L^10/2≤-L := by nlinarith only [hlarge,hL9]
  have hpoly : L^72≤Real.exp (72*L) := by
    have hh : L≤Real.exp L := by linarith [Real.add_one_le_exp L]
    have he := pow_le_pow_left₀ hLp.le hh 72
    rw [←Real.exp_nat_mul] at he
    norm_num only [Nat.cast_ofNat] at he
    exact he
  calc
    _=Real.exp (6*L^9)*L^72*Real.exp (-L^10/2) := by
      dsimp [L]
      rw [lemma23PaperP,←Real.exp_nat_mul]
      norm_num
    _≤Real.exp (6*L^9)*Real.exp (72*L)*Real.exp (-L^10/2) := by gcongr
    _=Real.exp (6*L^9+72*L-L^10/2) := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
    _≤Real.exp (-L) := Real.exp_le_exp.mpr hex
    _=_ := by dsimp [L,lemma23PaperL]; rw [Real.exp_neg,Real.exp_log hDp]

end ZhangLS.Spec
