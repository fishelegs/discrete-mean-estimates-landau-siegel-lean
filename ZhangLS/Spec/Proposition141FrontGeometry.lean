import ZhangLS.Spec.Proposition141Support
import ZhangLS.Spec.Proposition141GlobalShift
import ZhangLS.Spec.Lemma44SectionFourGamma

/-! # Actual Dp conductor and closed short-support geometry for the front end

The extra D is retained. In particular the common exceptional-family tail
condition is derived from 2P₄=2PT⁻²t₀, rather than inserted as a new hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset

lemma proposition141_front_short_scale {D:ℕ} (hD:1<D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    2*lemma61PaperP4 D≤lemma23PaperP D := by
  have hD1:(1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have hD2 : (1:ℝ)≤(D:ℝ)^2 := one_le_pow₀ hD1
  have hP4 := (lemma61_P4_pos hD).le
  apply le_trans _ hmod
  nlinarith only [mul_le_mul_of_nonneg_right hD2 hP4]

lemma proposition141_front_conductor_bound {D p:ℕ} (hD:0<D)
    (hL:2000≤lemma23PaperL D) (hp:p∈lemma56PaperPrimes D) :
    ((D*p:ℕ):ℝ)≤2*lemma23PaperP D^2 ∧ D*p≠1 := by
  have hDpos:0<(D:ℝ) := by exact_mod_cast hD
  have hL1:1≤lemma23PaperL D := by linarith
  have hDP:(D:ℝ)≤lemma23PaperP D := by
    have hh := Real.exp_le_exp.mpr (le_self_pow₀ hL1 (by norm_num : 9≠0))
    simpa only [lemma23PaperL,Real.exp_log hDpos,lemma23PaperP] using hh
  have hp' := (lemma56_mem_paper_primes D p).mp hp
  have hpw := lemma56_paper_prime_weight_parameters hL
  have hpP:(p:ℝ)≤2*lemma23PaperP D := by linarith [hpw.2.2.2.1]
  refine ⟨?_,?_⟩
  · have hh := mul_le_mul hDP hpP (Nat.cast_nonneg p) (Real.exp_pos _).le
    push_cast
    convert hh using 1; ring
  · have hh : p≤D*p := Nat.le_mul_of_pos_left p hD
    have hp2 := hp'.1.two_le
    omega

lemma proposition141_front_support_gap {D p n:ℕ} (hD:1<D)
    (hL:2000≤lemma23PaperL D) (ht:lemma51PaperT0 D≤(D:ℝ))
    (hT:(D:ℝ)^4<lemma56PaperT D) (hp:p∈lemma56PaperPrimes D)
    (hn:n∈proposition141Indices D) :
    (((D*p:ℕ):ℝ)*(n:ℝ))*lemma51PaperT0 D^(51/50:ℝ)<lemma23PaperP D^2 := by
  have hD1:(1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have hD2:(2:ℝ)≤D := by exact_mod_cast (show 2≤D by omega)
  have hDp:0<(D:ℝ) := by linarith
  have ht0:0≤lemma51PaperT0 D := pow_nonneg (by linarith : 0≤lemma23PaperL D) _
  have hcut : lemma51PaperT0 D^(51/50:ℝ)≤(D:ℝ)^2 := by
    apply (Real.rpow_le_rpow ht0 ht (by norm_num : (0:ℝ)≤51/50)).trans
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num : (51/50:ℝ)≤2)
  have hnp := proposition141_mem_indices D n |>.mp hn
  have hp' := (lemma56_mem_paper_primes D p).mp hp
  have hpw := lemma56_paper_prime_weight_parameters hL
  have hpP:(p:ℝ)≤2*lemma23PaperP D := by linarith [hpw.2.2.2.1]
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hT2 : 0<lemma56PaperT D^2 := sq_pos_of_pos (Real.exp_pos _)
  have hsmall : 4*(D:ℝ)^4<lemma56PaperT D^2 := by
    have hD4 : (4:ℝ)≤(D:ℝ)^4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hD2 4
      norm_num at hh
      linarith
    have hs := (sq_lt_sq₀ (pow_nonneg hDp.le _) (Real.exp_pos _).le).mpr hT
    have hm := mul_le_mul_of_nonneg_right hD4 (pow_nonneg hDp.le 4)
    apply hm.trans_lt
    simpa only [pow_two] using hs
  have hsize : (((D*p:ℕ):ℝ)*(n:ℝ))*lemma51PaperT0 D^(51/50:ℝ)≤
      4*(D:ℝ)^3*lemma23PaperP D*lemma61PaperP4 D := by
    have hP4 := (lemma61_P4_pos hD).le
    calc
      _≤((D:ℝ)*(2*lemma23PaperP D))*(2*lemma61PaperP4 D)*(D:ℝ)^2 := by
        push_cast
        gcongr
        exact hnp.2
      _=_ := by ring
  apply (mul_lt_mul_iff_left₀ hT2).mp
  calc
    _≤(4*(D:ℝ)^3*lemma23PaperP D*lemma61PaperP4 D)*lemma56PaperT D^2 :=
      mul_le_mul_of_nonneg_right hsize hT2.le
    _=4*(D:ℝ)^3*lemma23PaperP D*(lemma23PaperP D*lemma51PaperT0 D) := by
      rw [mul_assoc,lemma61_complementary_scales]
    _≤4*(D:ℝ)^4*lemma23PaperP D^2 := by
      have hh := mul_le_mul_of_nonneg_left ht (show 0≤4*(D:ℝ)^3*lemma23PaperP D^2 by positivity)
      convert hh using 1 <;> ring
    _<lemma23PaperP D^2*lemma56PaperT D^2 := by
      have hh := mul_lt_mul_of_pos_right hsmall (sq_pos_of_pos hP)
      simpa only [mul_comm] using hh

/-- One threshold is fixed before any character, coefficient or shift. -/
theorem proposition141_uniform_front_geometry :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D →
      20000≤lemma23PaperL D ∧ 2*lemma61PaperP4 D≤lemma23PaperP D ∧
      ∀p∈lemma56PaperPrimes D,
        (((D*p:ℕ):ℝ)≤2*lemma23PaperP D^2 ∧ D*p≠1) ∧
        ∀n∈proposition141Indices D,
          (((D*p:ℕ):ℝ)*(n:ℝ))*lemma51PaperT0 D^(51/50:ℝ)<lemma23PaperP D^2 := by
  obtain ⟨Nt,ht2,ht⟩ := proposition141_uniform_t0_le_D
  obtain ⟨NT,hT2,hT⟩ := proposition141_uniform_fourth_lt_T
  obtain ⟨Nm,hm2,hm⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max Nt (max NT (max Nm ⌈Real.exp 20000⌉₊))
  refine ⟨D₀,ht2.trans (le_max_left _ _),?_⟩
  intro D hlarge
  have hNt:Nt≤D := (le_max_left _ _).trans hlarge
  have hNT:NT≤D := ((le_max_left _ _).trans (le_max_right _ _)).trans hlarge
  have hNm:Nm≤D := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hlarge
  have hNe:⌈Real.exp 20000⌉₊≤D := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hlarge
  have hD:1<D := by have := ht2.trans hNt; omega
  have hL:20000≤lemma23PaperL D := by
    have he:Real.exp 20000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 20000) he
  refine ⟨hL,proposition141_front_short_scale hD (hm D hNm),?_⟩
  intro p hp
  exact ⟨proposition141_front_conductor_bound (by omega) (by linarith) hp,
    fun n hn=>proposition141_front_support_gap hD (by linarith) (ht D hNt) (hT D hNT) hp hn⟩

end ZhangLS.Spec
