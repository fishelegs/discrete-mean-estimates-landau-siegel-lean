import ZhangLS.Spec.Proposition141LargeSieveMoments
import ZhangLS.Spec.Proposition71WeightedCauchy

/-! # Genuine weighted bilinear mean for the Section14 Mellin integrand

Both square means below are derived from the actual all-modulus large sieve.
The κ* and χ-conjugate-character prime polynomials are exactly the factors
which occur after Mellin inversion. No mean estimate is an input hypothesis.
The modulus filter Q and coefficient filter S remain arbitrary and explicit.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate
set_option maxHeartbeats 2000000

theorem proposition141_actual_weighted_bilinear_mean {D D₁ d X : ℕ}
    (χ : RealPrimitiveCharacter D) (hL : 2000≤lemma23PaperL D)
    {B Y R : ℝ} (hB : 0≤B) (hY : 0<Y) (hR : 1≤R)
    {κ : ℕ→ℂ} (hκ : Proposition141KappaBound B κ)
    (hD₁ : 0<D₁) (hd : 0<d) (hX : 1≤X) (S : Finset ℕ) (hS : S⊆Icc 1 X)
    (hYl : ∀l∈S,Y≤(l:ℝ)) (Q : Finset ℕ) (hQ1 : ∀r∈Q,1<r)
    (hQ : ∀r∈Q,(r:ℝ)≤2*R) {s β : ℂ} (hs : s.re=1)
    (hβ : ‖β‖<5*lemma44PaperAlpha D) :
    (∑r∈Q, ((r:ℝ)/r.totient)*
      ∑θ∈(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖∑l∈S,(κ (D₁*d*l)/(l:ℂ)^s)*θ (l:ZMod r)‖*
        ‖∑p∈lemma56PaperPrimes D,χ.chi (p:ZMod D)*conj (θ (p:ZMod r))*(p:ℂ)^(s+β)‖) ≤
      Real.sqrt ((32+Real.pi^2)*(R^2+(X:ℝ))*
        (((B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))^2/Y)*(1+Real.log (X:ℝ))^25))*
      Real.sqrt ((32+Real.pi^2)*(R^2+2*lemma23PaperP D)*
        (2*(Real.exp 40)^2*lemma23PaperP D*lemma56PrimeMass D)) := by
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hM := lemma56_prime_mass_nonneg D
  have hlog : 0≤1+Real.log (X:ℝ) := by
    have hx := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)
    linarith
  apply proposition71_weighted_primitive_cauchy_bound Q
    (fun r => (r:ℝ)/r.totient) (fun _ => by positivity)
    (fun r θ => ∑l∈S,(κ (D₁*d*l)/(l:ℂ)^s)*θ (l:ZMod r))
    (fun r θ => ∑p∈lemma56PaperPrimes D,χ.chi (p:ZMod D)*conj (θ (p:ZMod r))*(p:ℂ)^(s+β))
    (by positivity) (by positivity)
  · exact proposition141_actual_weighted_kappa_mean hB hY hR hκ hD₁ hd hX S hS hYl Q hQ1 hQ hs
  · exact proposition141_actual_weighted_prime_mean χ hL hβ hs Q hQ1 hR hQ

end ZhangLS.Spec
