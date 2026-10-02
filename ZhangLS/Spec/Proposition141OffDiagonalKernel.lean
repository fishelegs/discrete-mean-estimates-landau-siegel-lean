import ZhangLS.Spec.Proposition141SmallKernel
import ZhangLS.Spec.Proposition141OffDiagonal
import ZhangLS.Spec.Proposition141Support

/-! # The actual small-conductor off-diagonal kernel in (14.6)

Conductor invariance excludes χ from modulus D₂k when D₁>1 and (D₁,k)=1.
Changing to the common modulus only uses actual prime units, proved from
support; no equality of character values on general nonunits is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped ComplexConjugate

/-- Common-level induction preserves the actual prime kernel on its proved
unit domain. This includes the full complex β weight and the actual Δ. -/
theorem proposition141_prime_kernel_changeLevel {D m : ℕ} [NeZero m]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ m)
    (hNP : ((D*m:ℕ):ℝ)≤lemma23PaperP D) (β : ℂ) (h r l : ℝ) :
    proposition141ActualShiftedPrimeKernel χ (θ.changeLevel (m.dvd_mul_left D)) β h r l =
      proposition141ActualShiftedPrimeKernel χ θ β h r l := by
  letI : NeZero (D*m) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne m)⟩
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpp,hpP,_⟩ := (lemma56_mem_paper_primes D p).mp hp
  have hlt : D*m<p := by exact_mod_cast hNP.trans_lt hpP
  have hc : p.Coprime (D*m) := hpp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact (not_le_of_gt hlt) (Nat.le_of_dvd
      (Nat.mul_pos (Nat.pos_of_ne_zero χ.modulus_ne_zero) (Nat.pos_of_ne_zero (NeZero.ne m))) hd))
  have he := changeLevel_eq_cast_of_dvd θ (m.dvd_mul_left D) (ZMod.unitOfCoprime p hc)
  simp only [ZMod.coe_unitOfCoprime,ZMod.cast_natCast (m.dvd_mul_left D) p] at he
  rw [he]

/-- Uniform full-frequency off-diagonal kernel estimate. The χ-exclusion
is derived from D∤m, not passed as a fictitious primitive-character premise. -/
theorem proposition141_uniform_off_diagonal_small_kernel_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ {D m : ℕ} [NeZero m] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ m),
      D₀≤D → NormalizedAssumptionA χ → ((D*m:ℕ):ℝ)≤lemma23PaperP D →
      ¬D∣m → θ≠1 → θ.conductor<D^3 →
      ∀ β : ℂ, ‖β‖<5*lemma44PaperAlpha D → ∀ h r l : ℝ, 0<h → 0<r → 0<l →
        ‖proposition141ActualShiftedPrimeKernel χ θ β h r l‖ ≤
          C*lemma23PaperL D^7200*(h*r/l)*lemma56PrimeMass D*
            (lemma56Decay D+(D:ℝ)^(-(7:ℤ))) := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_uniform_small_shifted_prime_kernel_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D m _ χ θ hDN hA hNP hDm hθ hcond β hβ h r l hh hr hl
  letI : NeZero (D*m) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne m)⟩
  have hn : θ.changeLevel (m.dvd_mul_left D)≠1 := by
    intro he
    exact hθ ((changeLevel_eq_one_iff (m.dvd_mul_left D)).mp he)
  have hc : (θ.changeLevel (m.dvd_mul_left D)).conductor<D^3 := by
    rwa [lemma44_conductor_changeLevel θ]
  have hb := hbound χ (D.dvd_mul_right m) (θ.changeLevel (m.dvd_mul_left D))
    hDN hA hNP hn (proposition141_lift_ne_chi_of_not_dvd χ θ hDm) hc β hβ h r l hh hr hl
  rwa [proposition141_prime_kernel_changeLevel χ θ hNP] at hb

/-- The actual closed Section14 support supplies the common-modulus bound
in the off-diagonal case, retaining D₁, D₂ and the product factors. -/
theorem proposition141_supported_off_diagonal_common_modulus {D D₁ D₂ d k : ℕ}
    {B : ℝ} {a : ℕ → ℂ} (χ : RealPrimitiveCharacter D)
    (ha : Proposition141AdmissibleSequence D B a) (hD : D=D₁*D₂)
    (hD₁ : 0<D₁) (hd : 0<d) (hk : 0<k) (han : a (d*k)≠0)
    (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    ((D*(D₂*k):ℕ):ℝ)≤lemma23PaperP D := by
  have hD₂ : 0<D₂ := by
    have hz := χ.modulus_ne_zero
    by_contra hh
    have he : D₂=0 := by omega
    simp [he] at hD
    exact hz hD
  have hD₂le : D₂≤D := by rw [hD]; nlinarith
  have hcut := ((proposition141_mem_indices D k).mp
    (proposition141_nonzero_product_indices ha hd hk han).2).2
  have hD₂leR : (D₂:ℝ)≤D := by exact_mod_cast hD₂le
  calc
    ((D*(D₂*k):ℕ):ℝ) = (D:ℝ)*(D₂:ℝ)*(k:ℝ) := by push_cast; ring
    _ ≤ (D:ℝ)*(D:ℝ)*(k:ℝ) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hD₂leR (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = (D:ℝ)^2*(k:ℝ) := by ring
    _ ≤ (D:ℝ)^2*(2*lemma61PaperP4 D) := mul_le_mul_of_nonneg_left hcut (sq_nonneg _)
    _ = 2*(D:ℝ)^2*lemma61PaperP4 D := by ring
    _ ≤ _ := hmod

/-- The source (14.6) small-conductor branch, with all source support and
coprimality conditions rather than assumed common-level admissibility. -/
theorem proposition141_uniform_supported_off_diagonal_small_kernel_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ {D D₁ D₂ d k : ℕ} (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ (D₂*k)) (B : ℝ) (a : ℕ → ℂ),
      D₀≤D → NormalizedAssumptionA χ → D=D₁*D₂ → 1<D₁ → D₁.Coprime k →
      Proposition141AdmissibleSequence D B a → 0<d → 0<k → a (d*k)≠0 →
      θ≠1 → θ.conductor<D^3 →
      ∀ β : ℂ, ‖β‖<5*lemma44PaperAlpha D → ∀ h r l : ℝ, 0<h → 0<r → 0<l →
        ‖proposition141ActualShiftedPrimeKernel χ θ β h r l‖ ≤
          C*lemma23PaperL D^7200*(h*r/l)*lemma56PrimeMass D*
            (lemma56Decay D+(D:ℝ)^(-(7:ℤ))) := by
  obtain ⟨C,hC,N₁,hN₁,hbound⟩ := proposition141_uniform_off_diagonal_small_kernel_bound
  obtain ⟨N₂,hN₂,hsupport⟩ := proposition141_uniform_support_modulus_bound
  refine ⟨C,hC,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro D D₁ D₂ d k χ θ B a hDN hA hD hD₁ hcop ha hd hk han hθ hcond β hβ h r l hh hr hl
  have hD₂ : 0<D₂ := by
    have hz := χ.modulus_ne_zero
    by_contra hb
    have he : D₂=0 := by omega
    simp [he] at hD
    exact hz hD
  letI : NeZero (D₂*k) := ⟨(Nat.mul_pos hD₂ hk).ne'⟩
  have hNP := proposition141_supported_off_diagonal_common_modulus χ ha hD (by omega) hd hk han
    (hsupport D ((le_max_right N₁ N₂).trans hDN))
  exact hbound χ θ ((le_max_left N₁ N₂).trans hDN) hA hNP
    (proposition141_off_diagonal_not_dvd hD hD₂ hD₁ hcop) hθ hcond β hβ h r l hh hr hl

end ZhangLS.Spec
