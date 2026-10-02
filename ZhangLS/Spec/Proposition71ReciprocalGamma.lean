import ZhangLS.Spec.Lemma23PrimitiveGaussSum
import ZhangLS.Spec.Lemma23DirichletUnitModulus
import ZhangLS.Spec.Lemma53Kernels
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-! # Exact reciprocal-Z to the original Γ kernel

The actual primitive-character root number and Γℝ factors are reduced by
proved Gauss reciprocity and exact reflection/duplication. The parity
correction is retained exactly, rather than assumed as a Stirling error.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_front_gammaR_ne_zero {s : ℂ} (hs : s.im≠0) : Gammaℝ s≠0 := by
  rw [Ne,Gammaℝ_eq_zero_iff,not_exists]
  intro n hn
  apply hs
  have hh := congrArg Complex.im hn
  simpa using hh

lemma proposition71_front_gammaR_even_quotient {s : ℂ} (hs : s.im≠0) :
    Gammaℝ s/Gammaℝ (1-s)=Gammaℂ s*cos ((Real.pi : ℂ)*s/2) := by
  apply Gammaℝ_div_Gammaℝ_one_sub
  intro n hn
  apply hs
  have hh := congrArg Complex.im hn
  simpa using hh

lemma proposition71_front_gammaR_odd_quotient {s : ℂ} (hs : s.im≠0) :
    Gammaℝ (s+1)/Gammaℝ (2-s)=Gammaℂ s*sin ((Real.pi : ℂ)*s/2) := by
  have hn : ∀n : ℕ, s≠-n := by
    intro n hn
    apply hs
    have hh := congrArg Complex.im hn
    simpa using hh
  have hg : Gammaℝ (s+1)≠0 := proposition71_front_gammaR_ne_zero (by simpa using hs)
  rw [div_eq_mul_inv,inv_Gammaℝ_two_sub hn]
  field_simp

lemma proposition71_front_theta_even_exact (s : ℂ) :
    Gammaℂ s*cos ((Real.pi : ℂ)*s/2)=
      lemma53PaperThetaStar s*(1+Complex.exp ((Real.pi : ℂ)*I*s)) := by
  let z : ℂ := (Real.pi : ℂ)*s/2*I
  have hphase : (2*Real.pi : ℂ)*I*(-s/4)=-z := by dsimp [z]; ring
  have hphase2 : (Real.pi : ℂ)*I*s=2*z := by dsimp [z]; ring
  have he : Complex.exp (-z)*Complex.exp (2*z)=Complex.exp z := by
    rw [←Complex.exp_add]
    congr 1
    ring
  rw [Gammaℂ_def,lemma53PaperThetaStar]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [hphase,hphase2]
  have hc := Complex.two_cos ((Real.pi : ℂ)*s/2)
  have hneg : -((Real.pi : ℂ)*s/2)*I=-z := by dsimp [z]; ring
  rw [hneg] at hc
  change 2*cos ((Real.pi : ℂ)*s/2)=Complex.exp z+Complex.exp (-z) at hc
  calc
    _=((2*Real.pi : ℂ)^(-s)*Gamma s)*(2*cos ((Real.pi : ℂ)*s/2)) := by ring
    _=((2*Real.pi : ℂ)^(-s)*Gamma s)*(Complex.exp z+Complex.exp (-z)) := by rw [hc]
    _=_ := by linear_combination -((2*Real.pi : ℂ)^(-s)*Gamma s)*he

lemma proposition71_front_theta_odd_exact (s : ℂ) :
    (-I)*Gammaℂ s*sin ((Real.pi : ℂ)*s/2)=
      lemma53PaperThetaStar s*(1-Complex.exp ((Real.pi : ℂ)*I*s)) := by
  let z : ℂ := (Real.pi : ℂ)*s/2*I
  have hphase : (2*Real.pi : ℂ)*I*(-s/4)=-z := by dsimp [z]; ring
  have hphase2 : (Real.pi : ℂ)*I*s=2*z := by dsimp [z]; ring
  have he : Complex.exp (-z)*Complex.exp (2*z)=Complex.exp z := by rw [←Complex.exp_add]; congr 1; ring
  rw [Gammaℂ_def,lemma53PaperThetaStar]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [hphase,hphase2]
  have hc := Complex.two_sin ((Real.pi : ℂ)*s/2)
  have hneg : -((Real.pi : ℂ)*s/2)*I=-z := by dsimp [z]; ring
  rw [hneg] at hc
  change 2*sin ((Real.pi : ℂ)*s/2)=(Complex.exp (-z)-Complex.exp z)*I at hc
  calc
    _=(-I)*((2*Real.pi : ℂ)^(-s)*Gamma s)*(2*sin ((Real.pi : ℂ)*s/2)) := by ring
    _=(-I)*((2*Real.pi : ℂ)^(-s)*Gamma s)*((Complex.exp (-z)-Complex.exp z)*I) := by rw [hc]
    _=((2*Real.pi : ℂ)^(-s)*Gamma s)*(Complex.exp (-z)-Complex.exp z) := by
      linear_combination -((2*Real.pi : ℂ)^(-s)*Gamma s)*(Complex.exp (-z)-Complex.exp z)*Complex.I_sq
    _=_ := by linear_combination ((2*Real.pi : ℂ)^(-s)*Gamma s)*he

lemma proposition71_front_reciprocal_Z_archimedean {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1) (s : ℂ) :
    (lemma23DirichletZ θ s)⁻¹=
      gaussSum θ⁻¹ ZMod.stdAddChar*(N : ℂ)^(s-1)*
        (I^(if θ.Even then 0 else 1)/θ (-1))*
          (DirichletCharacter.gammaFactor θ s/DirichletCharacter.gammaFactor θ⁻¹ (1-s)) := by
  classical
  have hn : (N : ℂ)≠0 := by exact_mod_cast (NeZero.ne N)
  have hminusSq : θ (-1)^2=1 := by rw [←map_pow]; simp
  have hminus : θ (-1)≠0 := by intro hz; rw [hz] at hminusSq; norm_num at hminusSq
  have hprod := lemma23_gaussSum_mul_inverse θ hθ hN
  have htau : gaussSum θ ZMod.stdAddChar≠0 := by
    have hh : gaussSum θ ZMod.stdAddChar*gaussSum θ⁻¹ ZMod.stdAddChar≠0 := by
      rw [hprod]; exact mul_ne_zero hn hminus
    exact (mul_ne_zero_iff.mp hh).1
  have hi : (gaussSum θ ZMod.stdAddChar)⁻¹=
      gaussSum θ⁻¹ ZMod.stdAddChar/((N : ℂ)*θ (-1)) := by
    apply (eq_div_iff (mul_ne_zero hn hminus)).mpr
    rw [←hprod,←mul_assoc,inv_mul_cancel₀ htau,one_mul]
  have hp : ((N : ℂ)^((1/2 : ℂ)-s))⁻¹*(N : ℂ)^(1/2 : ℂ)/(N : ℂ)=(N : ℂ)^(s-1) := by
    calc
      _=(N : ℂ)^(-((1/2 : ℂ)-s)+(1/2 : ℂ))/(N : ℂ) := by
        rw [←Complex.cpow_neg,←Complex.cpow_add _ _ hn]
      _=(N : ℂ)^s/(N : ℂ) := by congr 2; ring
      _=_ := by rw [Complex.cpow_sub _ _ hn,Complex.cpow_one]
  unfold lemma23DirichletZ DirichletCharacter.rootNumber
  simp only [div_eq_mul_inv,mul_inv,inv_inv]
  rw [hi]
  calc
    _=(((N : ℂ)^((1/2 : ℂ)-s))⁻¹*(N : ℂ)^(1/2 : ℂ)/(N : ℂ))*
        gaussSum θ⁻¹ ZMod.stdAddChar*(I^(if θ.Even then 0 else 1)/θ (-1))*
          (DirichletCharacter.gammaFactor θ s/DirichletCharacter.gammaFactor θ⁻¹ (1-s)) := by ring
    _=_ := by rw [hp]; ring

lemma proposition71_front_even_inv {N : ℕ} (θ : DirichletCharacter ℂ N) (hθ : θ.Even) : θ⁻¹.Even := by
  change θ⁻¹ (-1)=1
  rw [MulChar.inv_apply_eq_inv',hθ]
  simp

lemma proposition71_front_odd_inv {N : ℕ} (θ : DirichletCharacter ℂ N) (hθ : θ.Odd) : θ⁻¹.Odd := by
  change θ⁻¹ (-1)=-1
  rw [MulChar.inv_apply_eq_inv',hθ]
  simp

/-- Exact reciprocal functional-equation factor, including its parity term. -/
theorem proposition71_reciprocal_Z_exact {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1) {s : ℂ} (hs : s.im≠0) :
    (lemma23DirichletZ θ s)⁻¹=
      gaussSum θ⁻¹ ZMod.stdAddChar*(N : ℂ)^(s-1)*lemma53PaperThetaStar s*
        (1+θ (-1)*Complex.exp ((Real.pi : ℂ)*I*s)) := by
  rw [proposition71_front_reciprocal_Z_archimedean θ hθ hN]
  rcases θ.even_or_odd with he|ho
  · have hi := proposition71_front_even_inv θ he
    rw [if_pos he,pow_zero,he,div_one,mul_one,he.gammaFactor_def,hi.gammaFactor_def,
      proposition71_front_gammaR_even_quotient hs,proposition71_front_theta_even_exact]
    ring
  · have hi := proposition71_front_odd_inv θ ho
    have hne : ¬θ.Even := by
      intro he
      have hh : (-1 : ℂ)=1 := by rw [←ho,he]
      norm_num at hh
    rw [if_neg hne,pow_one,ho,ho.gammaFactor_def,hi.gammaFactor_def,
      show 1-s+1=2-s by ring,proposition71_front_gammaR_odd_quotient hs]
    calc
      _=(gaussSum θ⁻¹ ZMod.stdAddChar*(N : ℂ)^(s-1))*
          ((-I)*Gammaℂ s*sin ((Real.pi : ℂ)*s/2)) := by ring
      _=(gaussSum θ⁻¹ ZMod.stdAddChar*(N : ℂ)^(s-1))*
          (lemma53PaperThetaStar s*(1-Complex.exp ((Real.pi : ℂ)*I*s))) := by rw [proposition71_front_theta_odd_exact]
      _=_ := by ring

end ZhangLS.Spec
