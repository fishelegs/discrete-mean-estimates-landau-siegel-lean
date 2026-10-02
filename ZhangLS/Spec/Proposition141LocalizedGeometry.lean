import ZhangLS.Spec.Proposition141GlobalShift

/-! # Actual Section14 localization geometry with the extra D factor

The internal interval is I(Rh)=[P t₀ R h/3,4 P t₀ R h], retaining (l,h)=1.
The source support gives d h R≤2 D P₄. The factor D is not dropped or replaced
by the smaller Section7 cutoff. Existing uniform support bounds pay for it.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Finset
open scoped Classical

noncomputable def proposition141LocalScale (D:ℕ) (R:ℝ) (h:ℕ) : ℝ :=
  lemma23PaperP D*lemma51PaperT0 D*R*(h:ℝ)

noncomputable def proposition141LocalizedIndices (D:ℕ) (R:ℝ) (h:ℕ) : Finset ℕ :=
  (Icc 1 ⌊4*proposition141LocalScale D R h⌋₊).filter
    (fun l=>proposition141LocalScale D R h/3≤(l:ℝ) ∧ l.Coprime h)

lemma proposition141_mem_localized_indices {D l h:ℕ} {R:ℝ} :
    l∈proposition141LocalizedIndices D R h ↔
      0<l ∧ proposition141LocalScale D R h/3≤(l:ℝ) ∧
        (l:ℝ)≤4*proposition141LocalScale D R h ∧ l.Coprime h := by
  simp only [proposition141LocalizedIndices,mem_filter,mem_Icc]
  constructor
  · intro hl
    exact ⟨hl.1.1,hl.2.1,(Nat.le_floor_iff' (by omega : l≠0)).mp hl.1.2,hl.2.2⟩
  · intro hl
    exact ⟨⟨hl.1,Nat.le_floor hl.2.2.1⟩,hl.2.1,hl.2.2.2⟩

/-- Every geometric condition is derived from the actual support, including
its additional D, and the already proved genuine parameter bounds. -/
theorem proposition141_localized_geometry {D:ℕ} (hD:1<D)
    (hL:2000≤lemma23PaperL D) (ht:lemma51PaperT0 D≤(D:ℝ))
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {R:ℝ} (hR:1≤R) {d h:ℕ} (hd:0<d) (hh:0<h)
    (hcut:((d*h:ℕ):ℝ)*R≤2*(D:ℝ)*lemma61PaperP4 D) :
    1≤proposition141LocalScale D R h ∧ R^2≤proposition141LocalScale D R h ∧
      proposition141LocalScale D R h≤lemma23PaperP D^2 ∧ R≤lemma23PaperP D := by
  have hdR : 1≤(d:ℝ) := by exact_mod_cast hd
  have hhR : 1≤(h:ℝ) := by exact_mod_cast hh
  have hDR : 1≤(D:ℝ) := by exact_mod_cast (by omega : 1≤D)
  have hR0 : 0≤R := by linarith
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg (by linarith : 0≤lemma23PaperL D) 9)
  have ht1 := (proposition141_t0_log_bounds hL).1
  have hRh : R*(h:ℝ)≤2*(D:ℝ)*lemma61PaperP4 D := by
    have hdh : (h:ℝ)≤(d:ℝ)*(h:ℝ) := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hdh hR0
    have hm' : R*(h:ℝ)≤((d*h:ℕ):ℝ)*R := by simpa only [Nat.cast_mul,mul_comm] using hm
    exact hm'.trans hcut
  have hDRh : (D:ℝ)*(R*(h:ℝ))≤lemma23PaperP D := by
    have hm := mul_le_mul_of_nonneg_left hRh (Nat.cast_nonneg D)
    have he : (D:ℝ)*(2*(D:ℝ)*lemma61PaperP4 D)=2*(D:ℝ)^2*lemma61PaperP4 D := by ring
    rw [he] at hm
    exact hm.trans hmod
  have hRP : R≤lemma23PaperP D := by
    have h1 : R≤(D:ℝ)*(R*(h:ℝ)) := by
      calc
        R=1*(R*1) := by ring
        _≤_ := by gcongr
    exact h1.trans hDRh
  refine ⟨?_,?_,?_,hRP⟩
  · calc
      (1:ℝ)=1*1*1*1 := by ring
      _≤_ := by unfold proposition141LocalScale; gcongr
  · calc
      R^2≤lemma23PaperP D*R := by nlinarith
      _=lemma23PaperP D*1*R*1 := by ring
      _≤_ := by unfold proposition141LocalScale; gcongr
  · calc
      proposition141LocalScale D R h = lemma23PaperP D*lemma51PaperT0 D*(R*(h:ℝ)) := by unfold proposition141LocalScale; ring
      _≤lemma23PaperP D*(D:ℝ)*(R*(h:ℝ)) := by gcongr
      _=lemma23PaperP D*((D:ℝ)*(R*(h:ℝ))) := by ring
      _≤lemma23PaperP D*lemma23PaperP D := mul_le_mul_of_nonneg_left hDRh hP
      _=_ := by ring

/-- The natural cutoff and logarithmic energy are uniformly controlled
without changing the original positive integer endpoints. -/
theorem proposition141_localized_length_budget {D h:ℕ} {R:ℝ}
    (hL:2000≤lemma23PaperL D) (hX:1≤proposition141LocalScale D R h)
    (hupper:proposition141LocalScale D R h≤lemma23PaperP D^2) :
    1≤⌊4*proposition141LocalScale D R h⌋₊ ∧
      (1+Real.log (⌊4*proposition141LocalScale D R h⌋₊:ℝ))^25≤4^25*lemma23PaperL D^225 := by
  have hN : 1≤⌊4*proposition141LocalScale D R h⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hNp : 0<(⌊4*proposition141LocalScale D R h⌋₊:ℝ) := by exact_mod_cast hN
  have hNu : (⌊4*proposition141LocalScale D R h⌋₊:ℝ)≤4*lemma23PaperP D^2 :=
    (Nat.floor_le (by linarith : 0≤4*proposition141LocalScale D R h)).trans (by linarith)
  have hlog := Real.log_le_log hNp hNu
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (pow_ne_zero 2 hP.ne'),Real.log_pow,
    lemma23PaperP,Real.log_exp] at hlog
  have h9 : 3≤lemma23PaperL D^9 := by
    have hh : lemma23PaperL D≤lemma23PaperL D^9 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hlog0 : 0≤1+Real.log (⌊4*proposition141LocalScale D R h⌋₊:ℝ) := by
    have hh := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤⌊4*proposition141LocalScale D R h⌋₊)
    linarith
  refine ⟨hN,?_⟩
  have hh := pow_le_pow_left₀ hlog0
    (show 1+Real.log (⌊4*proposition141LocalScale D R h⌋₊:ℝ)≤4*lemma23PaperL D^9 by
      have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      norm_num only [Nat.cast_ofNat] at hlog
      linarith) 25
  simpa only [mul_pow,←pow_mul] using hh

end ZhangLS.Spec
