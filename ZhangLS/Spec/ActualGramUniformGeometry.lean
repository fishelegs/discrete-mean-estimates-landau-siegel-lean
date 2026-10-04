import ZhangLS.Spec.ActualGramWeightedProfileAssembly
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Geometry for fixed actual profiles. The active set is the literal original
strict box restricted at the true first-profile ceiling. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def actualGramUniformPairs (D : ℕ) (B b : ℝ) : Finset (ℕ × ℕ) :=
  ((lemma81PolynomialIndices D) ×ˢ (lemma81PolynomialIndices D)).filter
    (fun dr : ℕ × ℕ => Real.log (dr.1 * dr.2 : ℕ) / B ≤ b)

lemma actualGramUniform_support_ceiling {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {b : ℝ} (hb : b ≤ 201/400) :
    Real.exp (Real.log (lemma23PaperP D) * b) < lemma81Cutoff D := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpow7 : 5 ≤ lemma23PaperL D^7 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 7
    norm_num at hh
    linarith
  have h9 : 5*lemma23PaperL D^2 ≤ lemma23PaperL D^9 := by
    calc
      _ ≤ lemma23PaperL D^7 * lemma23PaperL D^2 :=
        mul_le_mul_of_nonneg_right hpow7 (sq_nonneg _)
      _ = _ := by ring
  have h11 : lemma23PaperL D^(11/10 : ℝ) ≤ lemma23PaperL D^2 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
      hL1 (by norm_num : (11/10 : ℝ) ≤ (2 : ℕ))
  have hbudget : lemma23PaperL D^9*b <
      lemma23PaperL D^9-2*lemma23PaperL D^(11/10 : ℝ) := by
    have hb' := mul_le_mul_of_nonneg_left hb (pow_nonneg hLp.le 9)
    nlinarith only [h9,h11,hb',pow_pos hLp 2]
  have hc : lemma81Cutoff D =
      Real.exp (lemma23PaperL D^9-2*lemma23PaperL D^(11/10 : ℝ)) := by
    unfold lemma81Cutoff lemma56PaperT lemma23PaperP
    rw [zpow_neg,zpow_ofNat,←Real.exp_nat_mul,←Real.exp_neg,←Real.exp_add] <;>
      congr 1 <;> norm_num
  rw [hc,lemma23PaperP,Real.log_exp]
  exact Real.exp_lt_exp.mpr hbudget

lemma actualGramUniform_pair_geometry (D : ℕ) {B b : ℝ} (hB : 0 < B)
    (dr : ℕ × ℕ) (hdr : dr ∈ actualGramUniformPairs D B b) :
    0 < dr.1 ∧ 0 < dr.2 ∧ 0 ≤ Real.log (dr.1*dr.2 : ℕ)/B ∧
      Real.log (dr.1*dr.2 : ℕ)/B ≤ b ∧
      (dr.1*dr.2 : ℕ) ≤ Real.exp (B*b) := by
  obtain ⟨hm, ht⟩ := mem_filter.mp hdr
  have hm' := mem_product.mp hm
  have hd := ((proposition71_mem_indices D dr.1).mp hm'.1).1
  have hr := ((proposition71_mem_indices D dr.2).mp hm'.2).1
  have hq : 0 < dr.1*dr.2 := Nat.mul_pos hd hr
  have hqR : (0 : ℝ) < (dr.1*dr.2 : ℕ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (dr.1*dr.2 : ℕ) := by exact_mod_cast hq
  have hlog : Real.log (dr.1*dr.2 : ℕ) ≤ B*b := by
    simpa only [mul_comm] using (div_le_iff₀ hB).mp ht
  refine ⟨hd, hr, div_nonneg (Real.log_nonneg hq1) hB.le, ht, ?_⟩
  simpa only [Real.exp_log hqR] using Real.exp_le_exp.mpr hlog

lemma actualGramUniform_pairs_subset (D : ℕ) {B b : ℝ} (hB : 0 < B) :
    actualGramUniformPairs D B b ⊆
      (Icc 1 ⌊Real.exp (B*b)⌋₊) ×ˢ (Icc 1 ⌊Real.exp (B*b)⌋₊) := by
  intro dr hdr
  obtain ⟨hd,hr,ht,htb,hq⟩ := actualGramUniform_pair_geometry D hB dr hdr
  have hdn : (dr.1 : ℝ) ≤ (dr.1*dr.2 : ℕ) := by
    exact_mod_cast Nat.le_mul_of_pos_right dr.1 hr
  have hrn : (dr.2 : ℝ) ≤ (dr.1*dr.2 : ℕ) := by
    exact_mod_cast Nat.le_mul_of_pos_left dr.2 hd
  exact mem_product.mpr ⟨mem_Icc.mpr ⟨hd, Nat.le_floor (hdn.trans hq)⟩,
    mem_Icc.mpr ⟨hr, Nat.le_floor (hrn.trans hq)⟩⟩

lemma actualGramUniform_harmonic_bound {B b : ℝ} (hB : 1 ≤ B)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (harmonic ⌊Real.exp (B*b)⌋₊ : ℝ) ≤ 2*B := by
  have he : 1 ≤ Real.exp (B*b) := Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hb0)
  have hn : 1 ≤ ⌊Real.exp (B*b)⌋₊ := (Nat.le_floor_iff (Real.exp_pos _).le).mpr (by simpa using he)
  have hnR : (0 : ℝ) < (⌊Real.exp (B*b)⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊Real.exp (B*b)⌋₊ by omega)
  have hlog : Real.log (⌊Real.exp (B*b)⌋₊ : ℝ) ≤ B := by
    have hh := Real.log_le_log hnR (Nat.floor_le (Real.exp_pos (B*b)).le)
    rw [Real.log_exp] at hh
    exact hh.trans (by nlinarith)
  exact (harmonic_le_one_add_log _).trans (by linarith)

end ZhangLS.Spec
