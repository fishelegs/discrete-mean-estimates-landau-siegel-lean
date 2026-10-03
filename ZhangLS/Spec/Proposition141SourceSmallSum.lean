import ZhangLS.Spec.Proposition141PrimitiveOffDiagonalSum
import ZhangLS.Spec.Proposition141SourceOuterSupport
import ZhangLS.Spec.Proposition141SmallConductorAggregate

/-! # Both actual Section14 small-conductor branches

The source modulus family retains D₂|hr, (hr/D₂,D₁)=1 and a*(d hr/D₂)≠0.
For D₁=1 both principal and χ-induced characters are removed. For D₁>1,
D∤hr follows from the source coprimality, so χ-induction is impossible.
All invocations concern the true primitive conductor r>1.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

noncomputable def proposition141SourceSmallModuli (D D₁ D₂ d h:ℕ) (a:ℕ→ℂ) : Finset ℕ :=
  (Icc 1 (D^3)).filter (fun r=>1<r ∧ r<D^3 ∧ D₂∣r*h ∧
    (r*h/D₂).Coprime D₁ ∧ a (d*(r*h/D₂))≠0)

lemma proposition141_source_small_moduli_mem {D D₁ D₂ d h r:ℕ} {a:ℕ→ℂ}
    (hr:r∈proposition141SourceSmallModuli D D₁ D₂ d h a) :
    1<r ∧ r<D^3 ∧ D₂∣r*h ∧ (r*h/D₂).Coprime D₁ ∧ a (d*(r*h/D₂))≠0 :=
  (mem_filter.mp hr).2

/-- The original coefficient support proves the common-level height bound
and source classification before either branch applies prime cancellation. -/
theorem proposition141_uniform_source_small_character_sum :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),
      D₀≤D → NormalizedAssumptionA χ → ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
      ∀Bκ Ba:ℝ,0≤Bκ → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      ∀D₁ D₂ d h r:ℕ,D=D₁*D₂ → 0<D₁ → 0<d → 0<h →
      r∈proposition141SourceSmallModuli D D₁ D₂ d h a →
      ∀θ:DirichletCharacter ℂ r,θ∈proposition141SmallPrimitiveFamily χ h r →
      ∀Y:ℕ,1≤Y → ∀S:Finset ℕ,S⊆Icc 1 Y →
      ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h S‖ ≤
        C*Bκ*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*lemma23PaperL D^7200*
          ((h:ℝ)*(r:ℝ))*lemma56PrimeMass D*(lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*
            (1+Real.log (Y:ℝ))^5 := by
  obtain ⟨C₁,hC₁,N₁,hN₁,hmain⟩ := proposition141_uniform_primitive_small_character_sum_bound
  obtain ⟨C₂,hC₂,N₂,hN₂,hoff⟩ := proposition141_uniform_primitive_off_diagonal_sum_bound
  obtain ⟨N₃,hN₃,hmod⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max N₁ (max N₂ N₃)
  refine ⟨max C₁ C₂,hC₁.trans_le (le_max_left _ _),D₀,hN₁.trans (le_max_left _ _),?_⟩
  intro D χ hlarge hA β hβ Bκ Ba hBκ κ a hκ ha D₁ D₂ d h r hDD hD₁ hd hh hr θ hθ Y hY S hS
  have hN1 : N₁≤D := (le_max_left _ _).trans hlarge
  have hN2 : N₂≤D := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hlarge
  have hN3 : N₃≤D := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hlarge
  have hD : 1<D := by have := hN₁.trans hN1; omega
  have hp := proposition141_source_small_moduli_mem hr
  have hrp : 0<r := by omega
  letI : NeZero r := ⟨by omega⟩
  letI : NeZero h := ⟨by omega⟩
  have hD₂ : 0<D₂ := by
    by_contra hn
    have hz:D₂=0 := by omega
    rw [hz,mul_zero] at hDD
    omega
  have hk : 0<r*h/D₂ := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hrp hh) hp.2.2.1) hD₂
  have hN : D₂*(r*h/D₂)=r*h := Nat.mul_div_cancel' hp.2.2.1
  have hcommon : ((D*(r*h):ℕ):ℝ)≤lemma23PaperP D := by
    have hb := proposition141_supported_off_diagonal_common_modulus χ ha hDD hD₁ hd hk hp.2.2.2.2 (hmod D hN3)
    rwa [hN] at hb
  have hNP : ((r*h:ℕ):ℝ)≤lemma23PaperP D := by
    have hn : r*h≤D*(r*h) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hn : ((r*h:ℕ):ℝ)≤((D*(r*h):ℕ):ℝ)).trans hcommon
  have hprim := (mem_filter.mp hθ).2
  have hM := lemma56_prime_mass_nonneg D
  have hdec := (lemma56_decay_pos D).le
  have hlog : 0≤1+Real.log (Y:ℝ) := by have := Real.log_natCast_nonneg Y; linarith
  have hL : 0≤lemma23PaperL D := Real.log_natCast_nonneg D
  by_cases hcase:D₁=1
  · have hDD₂ : D=D₂ := by simpa only [hcase,one_mul] using hDD
    have hDN:D∣r*h := hDD₂ ▸ hp.2.2.1
    have hb := hmain χ hDN θ hN1 hA hNP hprim.1 hp.1 hp.2.1 (hprim.2 hDN)
      β hβ Bκ hBκ κ hκ D₁ d Y hD₁ hd hY S hS
    apply hb.trans
    gcongr
    exact le_max_left C₁ C₂
  · have hD₁gt : 1<D₁ := by omega
    have hnot : ¬D∣r*h := by
      have hn := proposition141_off_diagonal_not_dvd hDD hD₂ hD₁gt hp.2.2.2.1.symm
      rwa [hN] at hn
    have hDr : ¬D∣r := fun he=>hnot (he.trans (r.dvd_mul_right h))
    have hDrP : ((D*r:ℕ):ℝ)≤lemma23PaperP D := by
      have hn : D*r≤D*(r*h) := by
        simpa only [mul_assoc] using Nat.le_mul_of_pos_right (D*r) hh
      exact (by exact_mod_cast hn : ((D*r:ℕ):ℝ)≤((D*(r*h):ℕ):ℝ)).trans hcommon
    have hb := hoff χ θ hN2 hA hDrP hDr hprim.1 hp.1 hp.2.1 hh
      β hβ Bκ hBκ κ hκ D₁ d Y hD₁ hd hY S hS
    apply hb.trans
    gcongr
    exact le_max_right C₁ C₂

end ZhangLS.Spec
