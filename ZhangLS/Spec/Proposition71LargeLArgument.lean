import ZhangLS.Spec.Proposition71DeltaLocalization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Genuine large-l arguments of Δ under the original strict support scale -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter
open scoped Topology
set_option maxHeartbeats 2000000

lemma proposition71_log_power_linear_quarter_threshold (k : ℕ) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → lemma23PaperL D^k≤(D : ℝ)/4 := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) (k : ℝ)
    (by norm_num)).bound (by norm_num : (0:ℝ)<1/4)
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp ht
  refine ⟨D₀,?_⟩
  intro D hD
  have hh := hD₀ D hD
  simp only [Real.rpow_natCast,Real.rpow_one,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg D) k),
    abs_of_nonneg (show (0:ℝ)≤(D : ℝ) by positivity)] at hh
  convert hh using 1 <;> ring

lemma proposition71_uniform_large_l_geometry :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      3≤lemma23PaperL D ∧ lemma51PaperT0 D^(51/50 : ℝ)≤(D : ℝ)/4 ∧
        lemma56PaperT D^(-2 : ℤ)≤(D : ℝ)⁻¹ := by
  obtain ⟨Da,ha⟩ := proposition71_log_power_linear_quarter_threshold 530
  refine ⟨max 2 (max Da ⌈Real.exp 3⌉₊),le_max_left _ _,?_⟩
  intro D hD
  have hDa := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDe := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hL : 3≤lemma23PaperL D := lemma33_parameters_at_threshold hDe
  have hLp : 0≤lemma23PaperL D := by linarith
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by have := (le_max_left _ _).trans hD; omega)
  refine ⟨hL,?_,?_⟩
  · apply le_trans _ (ha D hDa)
    unfold lemma51PaperT0
    rw [←Real.rpow_natCast (lemma23PaperL D) 519,←Real.rpow_mul hLp,
      ←Real.rpow_natCast (lemma23PaperL D) 530]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  · have hh := lemma81_T_inverse_square_le_exp_neg_log hL
    simpa [Real.exp_neg,lemma23PaperL,Real.exp_log hDp] using hh

/-- For every actual prime p and every original h r≤PT⁻², l>P² lies in
Lemma5.3's genuine large-x range. The full h r scale is retained. -/
theorem proposition71_uniform_large_l_argument :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ p∈lemma56PaperPrimes D, ∀ h r l : ℝ, 0<h → 0<r →
        h*r≤lemma81Cutoff D → lemma23PaperP D^2<l →
          lemma51PaperT0 D^(51/50 : ℝ)<l/((p : ℝ)*h*r) := by
  obtain ⟨D₀,hD₀,hgeo⟩ := proposition71_uniform_large_l_geometry
  refine ⟨D₀,hD₀,?_⟩
  intro D hD p hp h r l hh hr hcut hl
  have hg := hgeo D hD
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hpp : 0<(p : ℝ) := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.pos
  have hp2 : (p : ℝ)≤2*lemma23PaperP D := by
    have hp' := proposition71_paper_prime_le_three_halves_P hg.1 hp
    nlinarith only [hp',hP.le]
  have hhr : h*r≤lemma23PaperP D/(D : ℝ) := by
    apply hcut.trans
    unfold lemma81Cutoff
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hg.2.2 hP.le
  have hden : (p : ℝ)*h*r≤2*lemma23PaperP D^2/(D : ℝ) := by
    calc
      _=(p : ℝ)*(h*r) := by ring
      _≤(2*lemma23PaperP D)*(lemma23PaperP D/(D : ℝ)) :=
        mul_le_mul hp2 hhr (mul_nonneg hh.le hr.le) (by positivity)
      _=_ := by ring
  have hdenp : 0<(p : ℝ)*h*r := by positivity
  have hx : (D : ℝ)/2<l/((p : ℝ)*h*r) := by
    apply (lt_div_iff₀ hdenp).mpr
    have hd := mul_le_mul_of_nonneg_left hden (by positivity : 0≤(D : ℝ)/2)
    have he : (D : ℝ)/2*(2*lemma23PaperP D^2/(D : ℝ))=lemma23PaperP D^2 := by field_simp
    rw [he] at hd
    exact hd.trans_lt hl
  have hd : (D : ℝ)/4<(D : ℝ)/2 := by linarith
  exact hg.2.1.trans_lt (hd.trans hx)

end ZhangLS.Spec
