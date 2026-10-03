import ZhangLS.Spec.ActualPhaseObjects

/-! The fixed logarithmic support windows and their inclusion in the original
strict polynomial cutoff. The coefficient bound is fixed before D and chi
in later uniform statements. No lower bound for a polynomial norm is inferred.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Classical
set_option maxHeartbeats 2000000

/-- Uniform coefficients with support in a specified closed logarithmic window. -/
def ActualPhaseWindowSequence (D : ℕ) (C u v : ℝ) (a : ℕ → ℂ) : Prop :=
  (∀ n : ℕ, ‖a n‖ ≤ C) ∧
    ∀ n : ℕ, a n ≠ 0 → (lemma23PaperP D)^u ≤ (n : ℝ) ∧ (n : ℝ) ≤ (lemma23PaperP D)^v

def ActualPhaseASequence (D : ℕ) (C : ℝ) (a : ℕ → ℂ) : Prop :=
  ActualPhaseWindowSequence D C (251/500) (63/125) a

def ActualPhaseBSequence (D : ℕ) (C : ℝ) (b : ℕ → ℂ) : Prop :=
  ActualPhaseWindowSequence D C (499/1000) (1/2) b

def ActualPhaseJSequence (D : ℕ) (C : ℝ) (j : ℕ → ℂ) : Prop :=
  ActualPhaseWindowSequence D C (1/2) (63/125) j

/-- The entire admitted box lies strictly below P T^-2, already for log D at least 3. -/
theorem actualPhase_support_ceiling_lt_original_cutoff {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) :
    (lemma23PaperP D)^(63/125 : ℝ) < lemma81Cutoff D := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hPpos : 0 < lemma23PaperP D := Real.exp_pos _
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
  have hbudget : lemma23PaperL D^9*(63/125 : ℝ) <
      lemma23PaperL D^9-2*lemma23PaperL D^(11/10 : ℝ) := by
    nlinarith only [h9,h11,pow_pos hLp 2]
  have hc : lemma81Cutoff D =
      Real.exp (lemma23PaperL D^9-2*lemma23PaperL D^(11/10 : ℝ)) := by
    unfold lemma81Cutoff lemma56PaperT lemma23PaperP
    rw [zpow_neg,zpow_ofNat,←Real.exp_nat_mul,←Real.exp_neg,←Real.exp_add] <;>
      congr 1 <;> norm_num
  rw [hc,Real.rpow_def_of_pos hPpos,lemma23PaperP,Real.log_exp]
  exact Real.exp_lt_exp.mpr hbudget

theorem actualPhase_window_admissible {D : ℕ} {C u v : ℝ} {a : ℕ → ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hv : v ≤ 63/125)
    (ha : ActualPhaseWindowSequence D C u v a) : Lemma81AdmissibleSequence D C a := by
  have hP : 1 ≤ lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg (by linarith) _)
  have hup : (lemma23PaperP D)^v ≤ (lemma23PaperP D)^(63/125 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP hv
  refine ⟨ha.1,?_⟩
  intro n hn
  by_contra hne
  exact (not_lt_of_ge hn) (((ha.2 n hne).2.trans hup).trans_lt
    (actualPhase_support_ceiling_lt_original_cutoff hL))

theorem actualPhase_A_admissible {D : ℕ} {C : ℝ} {a : ℕ → ℂ}
    (hL : 3 ≤ lemma23PaperL D) (ha : ActualPhaseASequence D C a) :
    Lemma81AdmissibleSequence D C a := actualPhase_window_admissible hL le_rfl ha

theorem actualPhase_B_admissible {D : ℕ} {C : ℝ} {b : ℕ → ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hb : ActualPhaseBSequence D C b) :
    Lemma81AdmissibleSequence D C b := actualPhase_window_admissible hL (by norm_num) hb

theorem actualPhase_J_admissible {D : ℕ} {C : ℝ} {j : ℕ → ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hj : ActualPhaseJSequence D C j) :
    Lemma81AdmissibleSequence D C j := actualPhase_window_admissible hL le_rfl hj

/-- The same coefficient bound permits T1[A,A] and every ordered A_i,A_j pair. -/
theorem actualPhase_A_is_J {D : ℕ} {C : ℝ} {a : ℕ → ℂ}
    (hL : 3 ≤ lemma23PaperL D) (ha : ActualPhaseASequence D C a) :
    ActualPhaseJSequence D C a := by
  have hP : 1 ≤ lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg (by linarith) _)
  refine ⟨ha.1,?_⟩
  intro n hn
  exact ⟨(Real.rpow_le_rpow_of_exponent_le hP (by norm_num : (1/2 : ℝ) ≤ 251/500)).trans
    (ha.2 n hn).1,(ha.2 n hn).2⟩

/-- A nonzero supported coefficient is a positive integer, hence present in
the original strict polynomial. This prevents silent lower-support deletion. -/
theorem actualPhase_supported_index_present {D : ℕ} {C u v : ℝ} {a : ℕ → ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hv : v ≤ 63/125)
    (ha : ActualPhaseWindowSequence D C u v a) {n : ℕ} (hn : a n ≠ 0) :
    n ∈ lemma81PolynomialIndices D := by
  have hp : 0 < (n : ℝ) := (Real.rpow_pos_of_pos (Real.exp_pos _) u).trans_le (ha.2 n hn).1
  have hnpos : 1 ≤ n := by
    have hh : 0 < n := by exact_mod_cast hp
    omega
  have hP : 1 ≤ lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg (by linarith) _)
  have hcut : (n : ℝ) < lemma81Cutoff D :=
    ((ha.2 n hn).2.trans (Real.rpow_le_rpow_of_exponent_le hP hv)).trans_lt
      (actualPhase_support_ceiling_lt_original_cutoff hL)
  have hnceil : n ≤ ⌈lemma81Cutoff D⌉₊ := by
    exact_mod_cast (hcut.le.trans (Nat.le_ceil (lemma81Cutoff D)))
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnpos,hnceil⟩,hcut⟩

end ZhangLS.Spec
