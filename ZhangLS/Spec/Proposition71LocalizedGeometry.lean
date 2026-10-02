import ZhangLS.Spec.Proposition71Support
import ZhangLS.Spec.Lemma81SixOneLengths

/-! # The original localized Section7 interval and its genuine parameter bounds -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def proposition71LocalScale (D : ℕ) (R : ℝ) (h : ℕ) : ℝ :=
  lemma23PaperP D*lemma51PaperT0 D*R*(h : ℝ)

noncomputable def proposition71LocalizedIndices (D : ℕ) (R : ℝ) (h : ℕ) : Finset ℕ :=
  (Icc 1 ⌊4*proposition71LocalScale D R h⌋₊).filter
    (fun l => proposition71LocalScale D R h/3≤(l : ℝ) ∧ l.Coprime h)

/-- Exactly the closed interval I(Rh)=[Pt₀Rh/3,4Pt₀Rh] with (l,h)=1. -/
lemma proposition71_mem_localized_indices {D l h : ℕ} {R : ℝ} :
    l∈proposition71LocalizedIndices D R h ↔
      0<l ∧ proposition71LocalScale D R h/3≤(l : ℝ) ∧
        (l : ℝ)≤4*proposition71LocalScale D R h ∧ l.Coprime h := by
  simp only [proposition71LocalizedIndices,mem_filter,mem_Icc]
  constructor
  · intro hl
    exact ⟨hl.1.1,hl.2.1,(Nat.le_floor_iff' (by omega : l≠0)).mp hl.1.2,hl.2.2⟩
  · intro hl
    exact ⟨⟨hl.1,Nat.le_floor hl.2.2.1⟩,hl.2.1,hl.2.2.2⟩

/-- All scale constraints used in the localized large-sieve application are
proved from the original positive d,h and dhR≤PT⁻² bound. -/
theorem proposition71_uniform_localized_geometry :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → 3≤lemma23PaperL D ∧
      ∀ R : ℝ, 1≤R → ∀ d h : ℕ, 0<d → 0<h →
        ((d*h : ℕ) : ℝ)*R≤lemma81Cutoff D →
        1≤proposition71LocalScale D R h ∧ R^2≤proposition71LocalScale D R h ∧
          proposition71LocalScale D R h≤lemma23PaperP D^2/2 := by
  obtain ⟨D₀,hD₀,hlength⟩ := lemma81_uniform_six_one_lengths
  refine ⟨D₀,?_⟩
  intro D hD
  have h61 := hD₀.trans hD
  have hL : 3≤lemma23PaperL D := by linarith only [(lemma61_parameters_at_threshold h61).2]
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg (by linarith : 0≤lemma23PaperL D) 9)
  have hT1 : 1≤lemma51PaperT0 D := one_le_pow₀ hL1
  have hP4 : 2*lemma61PaperP4 D≤lemma23PaperP D := by
    have hh := (hlength D hD).1
    have hr : (⌈2*lemma61PaperP4 D⌉₊ : ℝ)≤⌊lemma23PaperP D⌋₊ := by exact_mod_cast hh
    exact (Nat.le_ceil _).trans (hr.trans (Nat.floor_le hP.le))
  refine ⟨hL,?_⟩
  intro R hR d h hd hh hcut
  have hR0 : 0≤R := by linarith
  have hdR : 1≤(d : ℝ) := by exact_mod_cast hd
  have hhR : 1≤(h : ℝ) := by exact_mod_cast hh
  have hdhR : 1≤((d*h : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd hh
  have hRcut : R≤lemma81Cutoff D := by
    have hb := mul_le_mul_of_nonneg_right hdhR hR0
    simpa only [one_mul] using hb.trans hcut
  have hRP : R≤lemma23PaperP D := hRcut.trans (proposition71_cutoff_le_P D)
  have hRh : R*(h : ℝ)≤lemma81Cutoff D := by
    have hdh : (h : ℝ)≤(d : ℝ)*(h : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg h)
    have hb : R*(h : ℝ)≤((d*h : ℕ) : ℝ)*R := by
      simpa only [Nat.cast_mul,mul_comm,mul_left_comm,mul_assoc] using mul_le_mul_of_nonneg_left hdh hR0
    exact hb.trans hcut
  have hscale1 : 1≤proposition71LocalScale D R h := by
    calc
      (1:ℝ)=1*1*1*1 := by ring
      _≤_ := by unfold proposition71LocalScale; gcongr
  have hscale2 : R^2≤proposition71LocalScale D R h := by
    calc
      _≤lemma23PaperP D*R := by simpa only [pow_two] using mul_le_mul_of_nonneg_right hRP hR0
      _=lemma23PaperP D*1*R*1 := by ring
      _≤_ := by unfold proposition71LocalScale; gcongr
  have hscaleupper : proposition71LocalScale D R h≤lemma23PaperP D^2/2 := by
    calc
      _=lemma23PaperP D*lemma51PaperT0 D*(R*(h : ℝ)) := by unfold proposition71LocalScale; ring
      _≤lemma23PaperP D*lemma51PaperT0 D*lemma81Cutoff D := by gcongr
      _=lemma23PaperP D*lemma61PaperP4 D := by unfold lemma81Cutoff lemma61PaperP4; ring
      _≤_ := by nlinarith [mul_le_mul_of_nonneg_left hP4 hP.le]
  exact ⟨hscale1,hscale2,hscaleupper⟩

/-- The localized natural prefix and its logarithmic energy scale. -/
lemma proposition71_localized_length_budget {D h : ℕ} {R : ℝ}
    (hL : 3≤lemma23PaperL D) (hX : 1≤proposition71LocalScale D R h)
    (hupper : proposition71LocalScale D R h≤lemma23PaperP D^2/2) :
    1≤⌊4*proposition71LocalScale D R h⌋₊ ∧
      (1+Real.log (⌊4*proposition71LocalScale D R h⌋₊ : ℝ))^25≤
        4^25*lemma23PaperL D^225 := by
  have hN : 1≤⌊4*proposition71LocalScale D R h⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hNp : 0<(⌊4*proposition71LocalScale D R h⌋₊ : ℝ) := by exact_mod_cast hN
  have hNupper : (⌊4*proposition71LocalScale D R h⌋₊ : ℝ)≤2*lemma23PaperP D^2 :=
    (Nat.floor_le (by linarith : 0≤4*proposition71LocalScale D R h)).trans (by linarith)
  have hlog := Real.log_le_log hNp hNupper
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero 2 hP.ne'),Real.log_pow,
    lemma23PaperP,Real.log_exp] at hlog
  have hL1 : 1≤lemma23PaperL D := by linarith
  have h9 : 2≤lemma23PaperL D^9 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hL 9
    norm_num at hh
    linarith
  have hlog0 : 0≤1+Real.log (⌊4*proposition71LocalScale D R h⌋₊ : ℝ) := by
    have hh := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤⌊4*proposition71LocalScale D R h⌋₊)
    linarith
  refine ⟨hN,?_⟩
  have hh := pow_le_pow_left₀ hlog0
    (show 1+Real.log (⌊4*proposition71LocalScale D R h⌋₊ : ℝ)≤4*lemma23PaperL D^9 by
      have hlog2 := Real.log_le_self (by norm_num : (0:ℝ)≤2)
      norm_num only [Nat.cast_ofNat] at hlog
      linarith) 25
  simpa only [mul_pow,←pow_mul] using hh

end ZhangLS.Spec
