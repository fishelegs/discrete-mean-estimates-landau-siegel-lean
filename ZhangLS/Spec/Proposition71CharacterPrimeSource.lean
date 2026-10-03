import ZhangLS.Spec.Proposition71SigmaSourceAttachment
import ZhangLS.Spec.PrimitiveConductorFamily

/-! Exact original weighted nonprincipal source rows and finite prime
exchange. Primitive-conductor amplitudes are bounded only after the genuine
complete prime cancellation has been transported into sigma. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate
set_option maxHeartbeats 3500000

noncomputable def proposition71CharacterPrimeSource {k : ℕ} (D d : ℕ) (c : ℝ)
    (a : ℕ → ℂ) (θ : DirichletCharacter ℂ k) : ℂ :=
  ∑p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*conj (θ (p : ZMod k))*
    proposition71CharacterDeltaFiber D d ((p : ℝ)*(k : ℝ))
      (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m) θ

noncomputable def proposition71NonprincipalSourceBlock (D d k : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  if h : 0<d ∧ 0<k ∧ d*k∈lemma81PolynomialIndices D then
    letI : NeZero k := ⟨h.2.1.ne'⟩
    (d : ℂ)⁻¹*(a₂ (d*k)/(k : ℂ))*(k.totient : ℂ)⁻¹*
      ∑θ∈(univ : Finset (DirichletCharacter ℂ k)).erase 1,
        gaussSum θ⁻¹ ZMod.stdAddChar*proposition71CharacterPrimeSource D d c a₁ θ
  else 0

/-- All prime, support and character sums here are genuinely finite. The
infinite long series stays intact inside each row. -/
theorem proposition71_weighted_nonprincipal_source_exchange (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    (∑p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*
      proposition71PrimeNonprincipalMean D p c a₁ a₂)=
    ∑d∈lemma81PolynomialIndices D, ∑k∈lemma81PolynomialIndices D,
      proposition71NonprincipalSourceBlock D d k c a₁ a₂ := by
  unfold proposition71PrimeNonprincipalMean
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  unfold proposition71NonprincipalGcdBlock proposition71NonprincipalSourceBlock
  by_cases hs : 0<d ∧ 0<k ∧ d*k∈lemma81PolynomialIndices D
  · simp only [dif_pos hs,proposition71CharacterPrimeSource,mul_sum,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro θ hθ
    apply sum_congr rfl
    intro p hp
    ring
  · simp only [dif_neg hs,mul_zero,sum_const_zero]

/-- Arbitrary modulus-divisor version of the actual induced source bound.
The primitive divisor r is the true conductor, and h=k/r is retained. -/
theorem proposition71_induced_dvd_source_bound {D k r d : ℕ} [NeZero k] [NeZero r]
    (hdiv : r∣k) (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    (hk : k∈lemma81PolynomialIndices D) (hd : 0<d) {B : ℝ} (hB : 0≤B)
    (c : ℝ) (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a)
    (θ : DirichletCharacter ℂ r) (hθ : θ.IsPrimitive) :
    ‖gaussSum (θ.changeLevel hdiv)⁻¹ ZMod.stdAddChar*
      proposition71CharacterPrimeSource D d c a (θ.changeLevel hdiv)‖≤
      Real.sqrt (r : ℝ)*‖proposition71OriginalSigmaSeries D c a (k/r) d θ‖ := by
  have hr : 0<r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hk0 : 0<k := Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨h,rfl⟩ := hdiv
  have hh : 0<h := Nat.pos_of_mul_pos_left hk0
  letI : NeZero h := ⟨hh.ne'⟩
  have hkh : h*r∈lemma81PolynomialIndices D := by simpa only [mul_comm] using hk
  simpa only [proposition71CharacterPrimeSource,Nat.mul_div_cancel_left h hr] using
    proposition71_induced_gauss_source_bound hD hL hkh hd hB c a ha θ hθ

/-- Every finite full-modulus character is transported by its actual
primitive inducer, rather than by an arbitrary primitive-label hypothesis. -/
theorem proposition71_primitive_family_source_bound {D k d : ℕ} [NeZero k]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hk : k∈lemma81PolynomialIndices D)
    (hd : 0<d) {B : ℝ} (hB : 0≤B) (c : ℝ) (a : ℕ → ℂ)
    (ha : Lemma81AdmissibleSequence D B a) (i : primitiveConductorFamilyIndex k) :
    ‖gaussSum (primitiveConductorFamilyLift k i)⁻¹ ZMod.stdAddChar*
      proposition71CharacterPrimeSource D d c a (primitiveConductorFamilyLift k i)‖≤
      Real.sqrt (i.1.val : ℝ)*‖proposition71OriginalSigmaSeries D c a (k/i.1.val) d i.2.val‖ := by
  letI : NeZero i.1.val := ⟨(primitiveConductorFamily_index_pos i).ne'⟩
  exact proposition71_induced_dvd_source_bound (Nat.mem_divisors.mp i.1.property).1
    hD hL hk hd hB c a ha i.2.val i.2.property

end ZhangLS.Spec
