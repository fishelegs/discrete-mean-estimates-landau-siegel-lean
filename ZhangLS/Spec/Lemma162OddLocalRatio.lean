import ZhangLS.Spec.Lemma162OddVarpi
import Mathlib.Analysis.Normed.Group.Bounded

/-! Exact odd prime-power ratios and an honest parameter-dependent inverse
bound used only for absolute convergence. It is not a uniform strip bound. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_odd_base_prime_nonzero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (s : ℂ) (hs : 9/10 ≤ s.re)
    (hB : lemma162OddMEulerProduct χ β 1 1 s ≠ 0) (q : Nat.Primes) (hq : 2<q.val) :
    lemma161PrimeFactor χ β q s ≠ 0 := by
  have hh := (lemma162_odd_m_multipliable χ β hβ (by norm_num : (1:ℕ)≠0)
    (by norm_num : (1:ℕ)≠0) s hs).hasProd
  intro hz
  apply hB
  exact hh.unique (hasProd_zero_of_exists_eq_zero ⟨q,by
    simpa [lemma162OddMPrimeFactor,hq] using hz⟩)

lemma lemma162_odd_m_prime_power_ratio {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (q : Nat.Primes) (hq : 2<q.val)
    (k l : ℕ) (s : ℂ) (hs : 9/10 ≤ s.re)
    (hB : lemma162OddMEulerProduct χ β 1 1 s ≠ 0) :
    lemma162OddMEulerProduct χ β (q.val^k) (q.val^l) s /
      lemma162OddMEulerProduct χ β 1 1 s =
        lemma162GeneralMPrimeFactor χ β (q.val^k) (q.val^l) q s/lemma161PrimeFactor χ β q s := by
  have hb := (lemma162_odd_m_multipliable χ β hβ (by norm_num : (1:ℕ)≠0)
    (by norm_num : (1:ℕ)≠0) s hs).hasProd
  have hg := (lemma162_odd_m_multipliable χ β hβ (pow_ne_zero k q.property.ne_zero)
    (pow_ne_zero l q.property.ne_zero) s hs).hasProd
  rw [lemma153_finite_replacement_ratio ({q} : Finset Nat.Primes)
    (fun r => lemma162OddMPrimeFactor χ β 1 1 r s)
    (fun r => lemma162OddMPrimeFactor χ β (q.val^k) (q.val^l) r s)
    (lemma162OddMEulerProduct χ β 1 1 s)
    (lemma162OddMEulerProduct χ β (q.val^k) (q.val^l) s) hb hg hB (by
      intro r hr
      have hne : r ≠ q := by simpa using hr
      have hn : ¬r.val ∣ q.val := by
        intro hh
        rcases (Nat.dvd_prime q.property).mp hh with h | h
        · exact r.property.ne_one h
        · exact hne (Subtype.ext h)
      have hk : ¬r.val ∣ q.val^k := fun h => hn (r.property.dvd_of_dvd_pow h)
      have hl : ¬r.val ∣ q.val^l := fun h => hn (r.property.dvd_of_dvd_pow h)
      simp [lemma162OddMPrimeFactor,lemma162GeneralMPrimeFactor,hk,hl,r.property.not_dvd_one])]
  simp [lemma162OddMPrimeFactor,hq]

lemma lemma162_odd_inverse_family_bounded {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ∃ K : ℝ, 0<K ∧ ∀ q : Nat.Primes, 2<q.val → ‖(lemma161PrimeFactor χ β q s)⁻¹‖ ≤ K := by
  let f : Nat.Primes → ℂ := fun q => lemma161RestrictedFactor χ β (fun p => 2<p.val) q s
  have hn : Summable (fun q : Nat.Primes => ‖f q-1‖) :=
    lemma152_majorant_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => lemma161_restricted_error χ β hβ (fun p => 2<p.val) q s hs)
  have hh : Summable (fun q : Nat.Primes => f q-1) := summable_norm_iff.mp hn
  have ht : Tendsto f cofinite (𝓝 (1:ℂ)) := by
    simpa only [sub_add_cancel,zero_add] using hh.tendsto_cofinite_zero.add
      (tendsto_const_nhds : Tendsto (fun _ : Nat.Primes => (1:ℂ)) cofinite (𝓝 1))
  have hi : Tendsto (fun q => (f q)⁻¹) cofinite (𝓝 (1:ℂ)) := by
    simpa using ht.inv₀ (by norm_num : (1:ℂ)≠0)
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto_cofinite hi).exists_norm_le
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro q hq
  have h := hC ((f q)⁻¹) ⟨q,rfl⟩
  have he : f q = lemma161PrimeFactor χ β q s := by simp [f,lemma161RestrictedFactor,hq]
  rw [he] at h
  exact h.trans (le_max_right _ _)

noncomputable def lemma162GeneralMNormBound : ℝ :=
  1+lemma152CorrectionConstant+lemma162GeneralMExceptionBound

lemma lemma162_general_m_norm_bound_pos : 0<lemma162GeneralMNormBound := by
  have hC := lemma152_correction_constant_pos
  have hE := lemma162_general_m_exception_bound_pos
  unfold lemma162GeneralMNormBound
  linarith

lemma lemma162_general_m_local_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d l : ℕ) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma162GeneralMPrimeFactor χ β d l q s‖ ≤ lemma162GeneralMNormBound := by
  have he := lemma162_general_m_prime_error_bound χ β hβ d l q s hs
  have hn := norm_add_le (lemma162GeneralMPrimeFactor χ β d l q s-1) (1:ℂ)
  simp only [sub_add_cancel,norm_one] at hn
  have hp : (q.val:ℝ)^(-(19/10:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast q.property.one_lt.le) (by norm_num)
  have hC := lemma152_correction_constant_pos
  have hE := lemma162_general_m_exception_bound_pos
  unfold lemma162GeneralMNormBound
  split_ifs at he <;> nlinarith

end ZhangLS.Spec
