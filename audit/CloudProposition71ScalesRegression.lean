import ZhangLS.Spec.Proposition71PrincipalLocalScales
namespace ZhangLS.Spec
open scoped Classical
example {D p d₁ d₂ k l₂ : ℕ} (hL : 3≤lemma23PaperL D)
    (hp : p∈lemma56PaperPrimes D) (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hl₂ : 0<l₂)
    (hs₂ : d₂*l₂∈lemma81PolynomialIndices D) (hsk : d₁*d₂*k∈lemma81PolynomialIndices D) :
    1≤(p : ℝ)*(k : ℝ)/(l₂ : ℝ) ∧
      (p : ℝ)*(k : ℝ)/(l₂ : ℝ)≤lemma23PaperP D^10 ∧
      lemma56PaperT D^2<(p : ℝ)*(k : ℝ)/(l₂ : ℝ) :=
  (proposition71_principal_local_scales hL hp hd₁ hd₂ hk hl₂ hs₂ hsk).2.2
end ZhangLS.Spec
#print axioms ZhangLS.Spec.proposition71_principal_local_scales
#print ZhangLS.Spec.proposition71_principal_local_scales
#print ZhangLS.Spec.Proposition71Target
#print ZhangLS.Spec.Proposition71AtConstant
#print ZhangLS.Spec.Lemma81AdmissibleSequence
