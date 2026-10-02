import ZhangLS.Spec.Lemma84BoundaryPerronBound
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

/-- A genuine harmonic interval estimate with arbitrary real endpoints; the
extra unit handles the possible integer left endpoint exactly. -/
theorem lemma84_harmonic_real_layer (S : Finset ℕ) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) (hS : ∀n∈S, 0<n ∧ a≤n ∧ (n:ℝ)<b) :
    (∑ n∈S, (n:ℝ)⁻¹)≤2+Real.log (b/a) := by
  have hb : 0<b := ha.trans_le hab
  by_cases hb1 : b≤1
  · have hs : S=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hn0,_,hnb⟩ := hS n hn
      have hn1 : (1:ℝ)≤n := by exact_mod_cast hn0
      linarith
    rw [hs,sum_empty]
    have hl : 0≤Real.log (b/a) := Real.log_nonneg ((le_div_iff₀ ha).mpr (by simpa using hab))
    linarith
  have hb1' : 1≤b := (lt_of_not_ge hb1).le
  let A := Icc 1 ⌊b⌋₊
  let B := Icc 1 ⌊a⌋₊
  have hBA : B⊆A := Icc_subset_Icc_right (Nat.floor_le_floor hab)
  have hsub : S⊆insert ⌊a⌋₊ (A\B) := by
    intro n hn
    obtain ⟨hn0,han,hnb⟩ := hS n hn
    have hnA : n∈A := mem_Icc.mpr ⟨hn0,(Nat.le_floor_iff hb.le).mpr hnb.le⟩
    by_cases hnB : n∈B
    · apply mem_insert.mpr
      left
      have hnf := (mem_Icc.mp hnB).2
      have haf : ⌊a⌋₊≤n := Nat.floor_le_of_le han
      omega
    · exact mem_insert_of_mem (mem_sdiff.mpr ⟨hnA,hnB⟩)
  have hinv : (⌊a⌋₊:ℝ)⁻¹≤1 := by
    by_cases hf : ⌊a⌋₊=0
    · simp [hf]
    · have hf1 : (1:ℝ)≤⌊a⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf
      simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hf1
  have hsplit : (∑ n∈A\B, (n:ℝ)⁻¹)=(harmonic ⌊b⌋₊:ℝ)-(harmonic ⌊a⌋₊:ℝ) := by
    have hh : (∑ n∈A\B, (n:ℝ)⁻¹)+(∑ n∈B, (n:ℝ)⁻¹)=∑ n∈A, (n:ℝ)⁻¹ := sum_sdiff hBA
    simp only [A,B,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hh ⊢
    linarith
  have hsumins : (∑ n∈insert ⌊a⌋₊ (A\B), (n:ℝ)⁻¹)≤
      (⌊a⌋₊:ℝ)⁻¹+∑ n∈A\B, (n:ℝ)⁻¹ := by
    by_cases hf : ⌊a⌋₊∈A\B
    · rw [insert_eq_of_mem hf]
      exact le_add_of_nonneg_left (by positivity)
    · rw [sum_insert hf]
  calc
    _ ≤ ∑ n∈insert ⌊a⌋₊ (A\B), (n:ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ (⌊a⌋₊:ℝ)⁻¹+∑ n∈A\B, (n:ℝ)⁻¹ := hsumins
    _ ≤ 1+((harmonic ⌊b⌋₊:ℝ)-(harmonic ⌊a⌋₊:ℝ)) := by rw [hsplit]; linarith
    _ ≤ 2+Real.log (b/a) := by
      have hh := harmonic_floor_le_one_add_log b hb1'
      have hl := log_le_harmonic_floor a ha.le
      rw [Real.log_div hb.ne' ha.ne']
      linarith

/-- The actual dr band costs log T, not log P. The fixed polylogarithmic λ/φ
loss and the convergent r^-2 sum are all retained explicitly. -/
theorem lemma84_actual_weight_layer {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (S : Finset (ℕ×ℕ)) (N : ℕ)
    (hS : S⊆(Icc 1 N)×ˢ(Icc 1 N)) {Q T y : ℝ} (hQ : 0<Q) (hT : 1≤T)
    (hy : 1<y) (hlog : Real.log Q≤y)
    (hband : ∀a∈S, Q/T≤(a.1*a.2:ℕ) ∧ ((a.1*a.2:ℕ):ℝ)<Q) :
    (∑ a∈S, ‖lemma84Section8Weight χ c j a.1 a.2‖)≤
      2*lemma84WeightScale y*(2+Real.log T) := by
  have hT0 : 0<T := by linarith
  have hlT : 0≤Real.log T := Real.log_nonneg hT
  let R := Icc 1 N
  let A : ℕ → Finset ℕ := fun r => R.filter (fun d => (d,r)∈S)
  have hsplit : (∑ a∈S, ‖lemma84Section8Weight χ c j a.1 a.2‖)=
      ∑ r∈R, ∑ d∈A r, ‖lemma84Section8Weight χ c j d r‖ := by
    rw [show (∑ a∈S, ‖lemma84Section8Weight χ c j a.1 a.2‖)=
      ∑ a∈R×ˢR, if a∈S then ‖lemma84Section8Weight χ c j a.1 a.2‖ else 0 from by
        rw [←sum_filter]
        have he : (R×ˢR).filter (fun a => a∈S)=S := by
          ext a
          simp only [mem_filter]
          exact ⟨fun h => h.2,fun h => ⟨hS h,h⟩⟩
        rw [he]]
    rw [sum_product,sum_comm]
    simp only [A,sum_filter]
  have hrbound (r : ℕ) (hr : r∈R) :
      (∑ d∈A r, ‖lemma84Section8Weight χ c j d r‖)≤
        lemma84WeightScale y*(r:ℝ)⁻¹^2*(2+Real.log T) := by
    have hr0 : 0<r := (mem_Icc.mp hr).1
    have hrp : 0<(r:ℝ) := by exact_mod_cast hr0
    have hInt := lemma84_harmonic_real_layer (A r)
      (a:=Q/(T*(r:ℝ))) (b:=Q/(r:ℝ)) (by positivity) (by
        apply div_le_div_of_nonneg_left hQ.le hrp
        nlinarith) (by
        intro d hd
        obtain ⟨hdR,hdS⟩ := mem_filter.mp hd
        obtain ⟨hlo,hhi⟩ := hband (d,r) hdS
        refine ⟨(mem_Icc.mp hdR).1,?_,?_⟩
        · apply (div_le_iff₀ (mul_pos hT0 hrp)).mpr
          have hh := (div_le_iff₀ hT0).mp hlo
          push_cast at hh
          nlinarith only [hh]
        · apply (lt_div_iff₀ hrp).mpr
          simpa only [Nat.cast_mul] using hhi)
    have he : (Q/(r:ℝ))/(Q/(T*(r:ℝ)))=T := by field_simp
    rw [he] at hInt
    calc
      _ ≤ ∑ d∈A r, lemma84WeightScale y*(r:ℝ)⁻¹^2*(d:ℝ)⁻¹ := by
        apply sum_le_sum
        intro d hd
        obtain ⟨hdR,hdS⟩ := mem_filter.mp hd
        have hd0 : 0<d := (mem_Icc.mp hdR).1
        have hb := lemma84_actual_weight_bound χ c j hd0 hr0 hy
          ((Real.log_lt_log (by exact_mod_cast Nat.mul_pos hd0 hr0) (hband (d,r) hdS).2).le.trans hlog)
        nlinarith only [hb]
      _ = lemma84WeightScale y*(r:ℝ)⁻¹^2*(∑ d∈A r, (d:ℝ)⁻¹) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hInt (by positivity [lemma84_weight_scale_nonneg y])
  rw [hsplit]
  calc
    _ ≤ ∑ r∈R, lemma84WeightScale y*(r:ℝ)⁻¹^2*(2+Real.log T) := sum_le_sum hrbound
    _ = lemma84WeightScale y*(2+Real.log T)*(∑ r∈R, (r:ℝ)⁻¹^2) := by rw [mul_sum]; apply sum_congr rfl; intro r hr; ring
    _ ≤ lemma84WeightScale y*(2+Real.log T)*2 := mul_le_mul_of_nonneg_left
      (lemma84_finite_reciprocal_square R) (by positivity [lemma84_weight_scale_nonneg y])
    _ = _ := by ring

end ZhangLS.Spec
