import ZhangLS.Spec.Lemma102Perron
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
set_option maxHeartbeats 2000000

lemma lemma102_positive_log_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) {x : ℝ} (hx : 0<x)
    (N : ℕ) (hN : ⌊x⌋₊≤N) :
    (∑ n ∈ Finset.Icc 1 N,
      χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ)*
        (max (Real.log (x/(n:ℝ))) 0:ℝ)) = lemma102LogSum χ c j d r x := by
  unfold lemma102LogSum
  symm
  calc
    _ = ∑ n ∈ lemma84StrictCutoff x,
      χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ)*
        (max (Real.log (x/(n:ℝ))) 0:ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hh := (lemma84_mem_strictCutoff hx.le n).mp hn
      have hn0 : (0:ℝ)<n := by exact_mod_cast hh.1
      rw [max_eq_left (Real.log_nonneg ((le_div_iff₀ hn0).mpr (by simpa using hh.2.le)))]
    _ = _ := by
      apply Finset.sum_subset
      · intro n hn
        have hh := (lemma84_mem_strictCutoff hx.le n).mp hn
        exact Finset.mem_Icc.mpr ⟨hh.1,((Nat.le_floor_iff hx.le).mpr hh.2.le).trans hN⟩
      · intro n hn hnnot
        have hn0 : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hnx : x≤(n:ℝ) := by
          by_contra h
          exact hnnot ((lemma84_mem_strictCutoff hx.le n).mpr
            ⟨(Finset.mem_Icc.mp hn).1,lt_of_not_ge h⟩)
        rw [max_eq_right (Real.log_nonpos (div_nonneg hx.le hn0.le) ((div_le_one hn0).mpr hnx))]
        simp

/-- Exact second difference of three unshifted logarithmic ξ sums, with the
original tent and actual coefficients. All three cutoff endpoints are kept. -/
lemma lemma102_sum_exact_bridge {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) (d r : ℕ) (hd : 0<d) (hr : 0<r) :
    lemma102Sum χ c j d r = (500/(Real.log (lemma23PaperP D):ℂ))*
      (lemma102LogSum χ c j d r (lemma101Cutoff D (d*r:ℝ) (63/125)) -
        2*lemma102LogSum χ c j d r (lemma101Cutoff D (d*r:ℝ) (251/500)) +
        lemma102LogSum χ c j d r (lemma101Cutoff D (d*r:ℝ) (1/2))) := by
  have hy : (0:ℝ)<d*r := by positivity
  unfold lemma102Sum
  rw [← lemma102_positive_log_sum χ c j d r (lemma101_cutoff_pos D hy (63/125)) _ le_rfl,
    ← lemma102_positive_log_sum χ c j d r (lemma101_cutoff_pos D hy (251/500)) _
      (Nat.floor_mono (lemma101_cutoff_mono hD hy (by norm_num : (251/500:ℝ)≤63/125))),
    ← lemma102_positive_log_sum χ c j d r (lemma101_cutoff_pos D hy (1/2)) _
      (Nat.floor_mono (lemma101_cutoff_mono hD hy (by norm_num : (1/2:ℝ)≤63/125)))]
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [lemma101_tent_log_kernel hD hy (Finset.mem_Icc.mp hn).1]
  push_cast
  ring

lemma lemma102_log_sum_zero_of_le_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) {x : ℝ} (hx : 0<x) (hx1 : x≤1) :
    lemma102LogSum χ c j d r x=0 := by
  unfold lemma102LogSum
  apply Finset.sum_eq_zero
  intro n hn
  have hh := (lemma84_mem_strictCutoff hx.le n).mp hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hh.1
  linarith only [hh.2,hx1,hn1]

/-- The finite definition is exactly the source sum over all natural n.
The n=0 term and the top endpoint both contribute zero. -/
lemma lemma102_sum_eq_tsum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) (d r : ℕ) (hd : 0<d) (hr : 0<r) :
    lemma102Sum χ c j d r = ∑' n : ℕ,
      χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ)*
        (lemma111Tent (Real.log ((d*r:ℝ)*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ) := by
  have hy : (0:ℝ)<d*r := by positivity
  have hP : 0< lemma23PaperP D := Real.exp_pos _
  have hlogP : 0<Real.log (lemma23PaperP D) := by
    rw [lemma23PaperP,Real.log_exp]
    exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  unfold lemma102Sum
  symm
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n=0
  · subst n
    simp
  have hnpos : 0<n := Nat.pos_of_ne_zero hn0
  have hfloor : ⌊lemma101Cutoff D (d*r:ℝ) (63/125)⌋₊<n := by
    apply lt_of_not_ge
    intro hle
    exact hn (Finset.mem_Icc.mpr ⟨hnpos,hle⟩)
  have hcut := ((Nat.floor_lt (lemma101_cutoff_pos D hy (63/125)).le).mp hfloor).le
  have hmul : lemma23PaperP D^(63/125:ℝ)≤(d*r:ℝ)*(n:ℝ) := by
    have hh := (div_le_iff₀ hy).mp hcut
    simpa only [mul_comm] using hh
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hP (63/125)) hmul
  rw [Real.log_rpow hP] at hh
  have ht : (63/125:ℝ)≤Real.log ((d*r:ℝ)*(n:ℝ))/Real.log (lemma23PaperP D) :=
    (le_div_iff₀ hlogP).mpr hh
  rw [lemma101_tent_zero_of_ge ht]
  simp

end ZhangLS.Spec
