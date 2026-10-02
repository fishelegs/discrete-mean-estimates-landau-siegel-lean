import ZhangLS.Spec.CoprimeGaussResidues
import ZhangLS.Spec.Lemma53Kernels

/-! # Actual additive reciprocity in (14.4)

The identity comes from the genuine CRT permutation and standard additive
characters. It holds for every long index l, without inventing coprimality
of l. The original Δ₁→Δ phase is then combined with it exactly.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex

/-- Exact reciprocal additive phases for coprime positive moduli. -/
theorem additiveReciprocity_stdAddChar {N p : ℕ} [NeZero N] [NeZero p]
    (hcop : N.Coprime p) (l : ℕ) :
    letI : NeZero (N*p) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne p)⟩
    ZMod.stdAddChar ((l:ZMod p)*(N:ZMod p)⁻¹) =
      ZMod.stdAddChar (l:ZMod (N*p))*ZMod.stdAddChar (-(l:ZMod N)*(p:ZMod N)⁻¹) := by
  letI : NeZero (N*p) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne p)⟩
  have hpunit : IsUnit (p:ZMod N) := by simpa only [ZMod.isUnit_iff_coprime] using hcop.symm
  have hNunit : IsUnit (N:ZMod p) := by simpa only [ZMod.isUnit_iff_coprime] using hcop
  let a : ZMod N := (l:ZMod N)*(p:ZMod N)⁻¹
  let b : ZMod p := (l:ZMod p)*(N:ZMod p)⁻¹
  have ha : (p:ZMod N)*a=(l:ZMod N) := by
    calc
      _ = (l:ZMod N)*((p:ZMod N)*(p:ZMod N)⁻¹) := by dsimp [a]; ring
      _ = _ := by rw [ZMod.mul_inv_of_unit _ hpunit,mul_one]
  have hb : (N:ZMod p)*b=(l:ZMod p) := by
    calc
      _ = (l:ZMod p)*((N:ZMod p)*(N:ZMod p)⁻¹) := by dsimp [b]; ring
      _ = _ := by rw [ZMod.mul_inv_of_unit _ hNunit,mul_one]
  have he : coprimeGaussResidueEquiv hcop (a,b)=(l:ZMod (N*p)) := by
    apply (ZMod.chineseRemainder hcop).injective
    rw [coprimeGauss_residue_coordinates,map_natCast]
    change ((p:ZMod N)*a,(N:ZMod p)*b)=((l:ZMod N),(l:ZMod p))
    rw [ha,hb]
  have hf := coprimeGauss_additive_factorization hcop a b
  rw [he] at hf
  have hcancel : ZMod.stdAddChar a*ZMod.stdAddChar (-a)=(1:ℂ) := by
    rw [← AddChar.map_add_eq_mul,add_neg_cancel,AddChar.map_zero_eq_one]
  have hphase : ZMod.stdAddChar b=ZMod.stdAddChar (l:ZMod (N*p))*ZMod.stdAddChar (-a) := by
    calc
      _ = ZMod.stdAddChar b*(ZMod.stdAddChar a*ZMod.stdAddChar (-a)) := by rw [hcancel,mul_one]
      _ = (ZMod.stdAddChar a*ZMod.stdAddChar b)*ZMod.stdAddChar (-a) := by ring
      _ = _ := by rw [← hf]
  simpa only [a,b,neg_mul] using hphase

/-- The standard additive character at N*p is the actual phase used in
Delta, with the full denominator retained. -/
theorem additiveReciprocity_product_phase {N p : ℕ} [NeZero N] [NeZero p]
    (l : ℕ) :
    letI : NeZero (N*p) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne p)⟩
    ZMod.stdAddChar (l:ZMod (N*p)) =
      Complex.exp ((2*Real.pi:ℂ)*I*((l:ℝ)/((N:ℝ)*(p:ℝ)):ℝ)) := by
  letI : NeZero (N*p) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne p)⟩
  have he := ZMod.stdAddChar_coe (N := N*p) (l:ℤ)
  simp only [Int.cast_natCast] at he
  rw [he]
  congr 1
  push_cast
  ring

/-- Precisely the Δ₁-to-Δ identity in (14.4), including additive reciprocity.
No summation error or omitted nonunit term is hidden in this equality. -/
theorem additiveReciprocity_delta {D N p : ℕ} [NeZero N] [NeZero p]
    (hcop : N.Coprime p) (l : ℕ) :
    lemma53PaperDeltaOne D ((l:ℝ)/((N:ℝ)*(p:ℝ)))*
      ZMod.stdAddChar ((l:ZMod p)*(N:ZMod p)⁻¹) =
      lemma53PaperDelta D ((l:ℝ)/((N:ℝ)*(p:ℝ)))*
        ZMod.stdAddChar (-(l:ZMod N)*(p:ZMod N)⁻¹) := by
  rw [additiveReciprocity_stdAddChar hcop l,additiveReciprocity_product_phase l]
  unfold lemma53PaperDelta
  ring

end ZhangLS.Spec
