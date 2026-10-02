import ZhangLS.Spec.Lemma57MellinIdentity

/-!
# Step 35 full Mellin-identity regression

This check pins the absolute series/integral interchange and the resulting
unconditional Mellin identity from Zhang's Lemma 5.7.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57MellinIdentity χ :=
  lemma57MellinIdentity_proved χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57VerticalIntegrable χ 1 :=
  (lemma57MellinIdentity_proved χ hD).1

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    lemma57VerticalIntegral χ 1 =
      (lemma57FullSmoothedSum χ (zhangGaussianWeight D) : ℂ) :=
  (lemma57MellinIdentity_proved χ hD).2

end ZhangLS.Spec
