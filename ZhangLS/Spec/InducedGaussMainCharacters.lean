import ZhangLS.Spec.InducedGaussConductor
import ZhangLS.Spec.RealDirichletCharacter

/-! # Principal and real χ-induced terms of the actual character expansion

The principal Gauss value is μ(N), including N=1. The χ-induced phase
product and totient denominator are genuine identities, including k sharing
a prime with D; those terms vanish through χ(k), not an omitted condition.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

/-- Exact principal Gauss sum, with modulus one retained. -/
theorem inducedGauss_principal_value {N : ℕ} [NeZero N] :
    gaussSum (1:DirichletCharacter ℂ N) ZMod.stdAddChar=(ArithmeticFunction.moebius N:ℂ) := by
  have he := inducedGauss_changeLevel_formula_dvd (1:DirichletCharacter ℂ 1) (one_dvd N)
  have hv : (1:DirichletCharacter ℂ 1) (N:ZMod 1)=1 := by
    rw [show (N:ZMod 1)=1 by exact Subsingleton.elim _ _,map_one]
  simpa only [map_one,Nat.div_one,hv,inducedGauss_level_one_value,mul_one] using he

/-- Negative natural arguments obey the same exact unit-domain induction
bridge. Only coprimality with the EXTRA factor h is required. -/
theorem inducedGauss_changeLevel_neg_nat {r h : ℕ} [NeZero r] [NeZero h]
    (χ : DirichletCharacter ℂ r) (a : ℕ) (ha : a.Coprime h) :
    χ.changeLevel (r.dvd_mul_right h) (-(a:ZMod (r*h)))=χ (-(a:ZMod r)) := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  have hn := changeLevel_eq_cast_of_dvd χ (r.dvd_mul_right h) (-1:(ZMod (r*h))ˣ)
  have hminus : χ.changeLevel (r.dvd_mul_right h) (-1:ZMod (r*h))=χ (-1:ZMod r) := by
    simpa using hn
  rw [show -(a:ZMod (r*h))=(-1)*(a:ZMod (r*h)) by ring,map_mul,hminus,
    inducedGauss_changeLevel_nat χ a,if_pos ha,← map_mul]
  congr 1
  ring

/-- The exact induced term before using reality of χ. -/
theorem inducedGauss_phase_product {r h : ℕ} [NeZero r] [NeZero h]
    (χ : DirichletCharacter ℂ r) (p l : ℕ) (hp : p.Coprime h) (hl : l.Coprime h) :
    letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
    let θ := χ.changeLevel (r.dvd_mul_right h)
    gaussSum θ ZMod.stdAddChar*θ (p:ZMod (r*h))*θ (-(l:ZMod (r*h))) =
      (ArithmeticFunction.moebius h:ℂ)*χ (h:ZMod r)*gaussSum χ ZMod.stdAddChar*
        χ (-(p:ZMod r)*(l:ZMod r)) := by
  dsimp only
  rw [inducedGauss_changeLevel_formula,inducedGauss_changeLevel_nat χ p,if_pos hp,
    inducedGauss_changeLevel_neg_nat χ l hl]
  have hc : χ (p:ZMod r)*χ (-(l:ZMod r))=χ (-(p:ZMod r)*(l:ZMod r)) := by
    rw [← map_mul]
    congr 1
    ring
  calc
    _ = ((ArithmeticFunction.moebius h:ℂ)*χ (h:ZMod r)*gaussSum χ ZMod.stdAddChar)*
        (χ (p:ZMod r)*χ (-(l:ZMod r))) := by ring
    _ = _ := by rw [hc]

/-- Reality is proved from the original quadratic character structure. -/
theorem inducedGauss_real_changeLevel_inv {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (hDN : D∣N) :
    (χ.chi.changeLevel hDN)⁻¹=χ.chi.changeLevel hDN := by
  have hχ : χ.chi⁻¹=χ.chi := by
    have he := χ.quadratic
    rw [pow_two] at he
    exact inv_eq_of_mul_eq_one_left he
  rw [← map_inv,hχ]

/-- Precisely the real χ-induced contribution in (14.7), with both
conjugations and the order of the two phase factors accounted for. -/
theorem inducedGauss_real_phase_product {D k : ℕ} [NeZero k]
    (χ : RealPrimitiveCharacter D) (p l : ℕ) (hp : p.Coprime k) (hl : l.Coprime k) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
    let θ := χ.chi.changeLevel (D.dvd_mul_right k)
    gaussSum θ⁻¹ ZMod.stdAddChar*θ (-(l:ZMod (D*k)))*θ⁻¹ (p:ZMod (D*k)) =
      (ArithmeticFunction.moebius k:ℂ)*χ.chi (k:ZMod D)*gaussSum χ.chi ZMod.stdAddChar*
        χ.chi (-(p:ZMod D)*(l:ZMod D)) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
  dsimp only
  rw [inducedGauss_real_changeLevel_inv]
  have he := inducedGauss_phase_product χ.chi p l hp hl
  dsimp only at he
  convert he using 1 <;> ring

/-- The φ(Dk)→φ(D)φ(k) passage is exact: the noncoprime branch has χ(k)=0.
It does not assume that k and D were coprime in the original outer sum. -/
theorem inducedGauss_totient_denominator {D : ℕ} (χ : DirichletCharacter ℂ D) (k : ℕ) :
    ((ArithmeticFunction.moebius k:ℂ)*χ (k:ZMod D))/(Nat.totient (D*k):ℂ) =
      ((ArithmeticFunction.moebius k:ℂ)*χ (k:ZMod D))/((Nat.totient D:ℂ)*(Nat.totient k:ℂ)) := by
  by_cases hcop : D.Coprime k
  · rw [Nat.totient_mul hcop,Nat.cast_mul]
  · have hz : χ (k:ZMod D)=0 := MulChar.map_nonunit χ (by
      rw [ZMod.isUnit_iff_coprime]
      exact fun hk => hcop hk.symm)
    simp only [hz,mul_zero,zero_div]

/-- After inserting χ(l), dropping only the D-coprimality restriction is
an exact pointwise identity, including the nonunit branch. -/
theorem inducedGauss_coprime_filter {D : ℕ} (χ : DirichletCharacter ℂ D) (k l : ℕ) (z : ℂ) :
    (if l.Coprime (D*k) then χ (l:ZMod D)*z else 0) =
      if l.Coprime k then χ (l:ZMod D)*z else 0 := by
  by_cases hk : l.Coprime k
  · by_cases hD : l.Coprime D
    · rw [if_pos (hD.mul_right hk),if_pos hk]
    · have hn : ¬l.Coprime (D*k) := fun hh => hD (hh.of_dvd_right (D.dvd_mul_right k))
      have hz : χ (l:ZMod D)=0 := MulChar.map_nonunit χ (by simpa only [ZMod.isUnit_iff_coprime] using hD)
      simp only [if_neg hn,if_pos hk,hz,zero_mul]
  · have hn : ¬l.Coprime (D*k) := fun hh => hk (hh.of_dvd_right (k.dvd_mul_left D))
    rw [if_neg hn,if_neg hk]

/-- The real primitive Gauss normalization used to recover 1/φ(D) in
Proposition14.1, proved from the genuine functional-equation Gauss identity. -/
theorem inducedGauss_real_square {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : D≠1) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    χ.chi (-1)*(gaussSum χ.chi ZMod.stdAddChar)^2=(D:ℂ) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hχ : χ.chi⁻¹=χ.chi := by
    have he := χ.quadratic
    rw [pow_two] at he
    exact inv_eq_of_mul_eq_one_left he
  have hg := lemma23_gaussSum_mul_inverse χ.chi χ.primitive hD
  rw [hχ] at hg
  have hm : χ.chi (-1)*χ.chi (-1)=1 := by
    rw [← map_mul]
    simp
  rw [pow_two,hg]
  calc
    _ = (D:ℂ)*(χ.chi (-1)*χ.chi (-1)) := by ring
    _ = _ := by rw [hm,mul_one]

end ZhangLS.Spec
