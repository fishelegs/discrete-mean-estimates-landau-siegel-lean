import ZhangLS.Spec.Proposition141SourceLargeBlock

/-! # Literal source support makes all conductor outer indices finite

No finite d,h box is inserted as an extra hypothesis. The nonzero original
short coefficient, D₂|hr and D=D₁D₂ imply d,h,r,hr≤P uniformly.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

theorem proposition141_source_outer_support {D D₁ D₂ d h r:ℕ}
    {Ba:ℝ} {a:ℕ→ℂ} (ha:Proposition141AdmissibleSequence D Ba a)
    (hD:1<D) (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hDD:D=D₁*D₂) (hD₁:0<D₁) (hd:0<d) (hh:0<h) (hr:0<r)
    (hdiv:D₂∣h*r) (han:a (d*(h*r/D₂))≠0) :
    d≤⌊lemma23PaperP D⌋₊ ∧ h≤⌊lemma23PaperP D⌋₊ ∧
      r≤⌊lemma23PaperP D⌋₊ ∧ h*r≤⌊lemma23PaperP D⌋₊ := by
  have hD₂:0<D₂ := by
    by_contra hn
    have hz:D₂=0 := by omega
    rw [hz,mul_zero] at hDD
    omega
  have hk:0<h*r/D₂ := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hh hr) hdiv) hD₂
  have hN:h*r=D₂*(h*r/D₂) := (Nat.mul_div_cancel' hdiv).symm
  have hcut := proposition141_supported_conductor_scale ha hDD hD₁ hd hk han hN
    (Nat.cast_nonneg r) (le_refl (r:ℝ))
  have hP4 := (lemma61_P4_pos hD).le
  have hD1 : (1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have hDsq : (D:ℝ)≤(D:ℝ)^2 := le_self_pow₀ hD1 (by norm_num)
  have hprod : ((d*h*r:ℕ):ℝ)≤lemma23PaperP D := by
    rw [Nat.cast_mul]
    apply hcut.trans
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDsq (by norm_num : (0:ℝ)≤2)) hP4).trans hmod
  have hprodN : d*h*r≤⌊lemma23PaperP D⌋₊ := Nat.le_floor hprod
  have hdr : d≤d*h*r := (Nat.le_mul_of_pos_right d hh).trans (Nat.le_mul_of_pos_right (d*h) hr)
  have hhr : h≤d*h*r := (Nat.le_mul_of_pos_left h hd).trans (Nat.le_mul_of_pos_right (d*h) hr)
  have hrr : r≤d*h*r := Nat.le_mul_of_pos_left r (Nat.mul_pos hd hh)
  have hhrprod : h*r≤d*h*r := by
    simpa only [mul_assoc] using Nat.le_mul_of_pos_left (h*r) hd
  exact ⟨hdr.trans hprodN,hhr.trans hprodN,hrr.trans hprodN,hhrprod.trans hprodN⟩

/-- Either outer index outside the proved box forces the exact actual
source block to be empty, rather than estimating an invented truncation. -/
theorem proposition141_source_large_moduli_empty {D D₁ D₂ d h:ℕ}
    {Ba:ℝ} {a:ℕ→ℂ} (ha:Proposition141AdmissibleSequence D Ba a)
    (hD:1<D) (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hDD:D=D₁*D₂) (hD₁:0<D₁) (hd:0<d) (hh:0<h) (R:ℝ)
    (hout:⌊lemma23PaperP D⌋₊<d ∨ ⌊lemma23PaperP D⌋₊<h) :
    proposition141SourceLargeModuli D₁ D₂ d h R a=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hp := proposition141_source_large_moduli_mem hr
  have hs := proposition141_source_outer_support ha hD hmod hDD hD₁ hd hh
    (by omega : 0<r) hp.2.2.2.1 hp.2.2.2.2.2
  omega

/-- Uniform original-parameter version of the exact finiteness statement. -/
theorem proposition141_uniform_source_outer_support :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀Ba:ℝ,∀a:ℕ→ℂ,
      Proposition141AdmissibleSequence D Ba a → ∀D₁ D₂ d h r:ℕ,
      D=D₁*D₂ → 0<D₁ → 0<d → 0<h → 0<r → D₂∣h*r → a (d*(h*r/D₂))≠0 →
      d≤⌊lemma23PaperP D⌋₊ ∧ h≤⌊lemma23PaperP D⌋₊ ∧
        r≤⌊lemma23PaperP D⌋₊ ∧ h*r≤⌊lemma23PaperP D⌋₊ := by
  obtain ⟨D₀,hD₀,hs⟩ := proposition141_uniform_support_modulus_bound
  refine ⟨D₀,hD₀,?_⟩
  intro D hlarge Ba a ha D₁ D₂ d h r hDD hD₁ hd hh hr hdiv han
  exact proposition141_source_outer_support ha (by have := hD₀.trans hlarge; omega)
    (hs D hlarge) hDD hD₁ hd hh hr hdiv han

end ZhangLS.Spec
