import ZhangLS.Spec.Proposition71PrincipalSplitAttachment
import ZhangLS.Spec.Proposition71OriginalConductorLittleO

/-! Exact actual Section7 finite-prime / full-sigma attachment. All rows use
the original kappa convolution and beta3, with the full complementary h*r. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate
set_option maxHeartbeats 3500000

noncomputable def proposition71PrimitivePrimeDeltaTerm {r : ℕ} (D : ℕ) (c : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) (p l : ℕ) : ℂ :=
  if 0<l ∧ l.Coprime h then
    (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
      lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))) else 0

lemma proposition71_primitive_prime_delta_summable {D r h d p : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    (hk : h*r∈lemma81PolynomialIndices D) (hd : 0<d)
    {B : ℝ} (hB : 0≤B) (c : ℝ) (a : ℕ → ℂ)
    (ha : Lemma81AdmissibleSequence D B a) (θ : DirichletCharacter ℂ r) :
    Summable (proposition71PrimitivePrimeDeltaTerm D c a h d θ p) := by
  let κ := fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m
  let w := fun l : ℕ => if l.Coprime h then θ (l : ZMod r) else 0
  have hs := (proposition71_prime_short_absolute_scales (by linarith) hp hk).2.2
  have hq : 1≤(p : ℝ)*(h : ℝ)*(r : ℝ) ∧
      (p : ℝ)*(h : ℝ)*(r : ℝ)≤lemma23PaperP D^10 := by
    simpa only [Nat.cast_mul,mul_assoc] using hs
  have ht := (tauDelta_actual_dilated_character_sum hD hL κ w hB
    (fun m hm => proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB a ha.1 m)
    (fun l hl => by dsimp [w]; split_ifs; exact θ.norm_le_one _; simp) hd hq.1 hq.2).1
  exact ht.congr (fun l => by
    dsimp [tauDeltaDilatedTerm,proposition71PrimitivePrimeDeltaTerm,w,κ]
    by_cases hl : 0<l <;> by_cases hc : l.Coprime h <;> simp [hl,hc])

/-- The complete actual sigma, with its exact beta3, is the finite prime sum
of the complete absolutely convergent long rows. -/
theorem proposition71_original_sigma_prime_exchange {D r h d : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hk : h*r∈lemma81PolynomialIndices D)
    (hd : 0<d) {B : ℝ} (hB : 0≤B) (c : ℝ) (a : ℕ → ℂ)
    (ha : Lemma81AdmissibleSequence D B a) (θ : DirichletCharacter ℂ r) :
    proposition71OriginalSigmaSeries D c a h d θ=
      ∑p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*θ⁻¹ (p : ZMod r)*
        ∑'l : ℕ, proposition71PrimitivePrimeDeltaTerm D c a h d θ p l := by
  let C := fun p : ℕ => (p : ℂ)^lemma52PaperBetaThree D c*θ⁻¹ (p : ZMod r)
  let F := fun (p l : ℕ) => C p*proposition71PrimitivePrimeDeltaTerm D c a h d θ p l
  have hs (p : ℕ) (hp : p∈lemma56PaperPrimes D) : Summable (F p) :=
    (proposition71_primitive_prime_delta_summable hD hL hp hk hd hB c a ha θ).mul_left (C p)
  rw [proposition71_original_sigma_series_expanded]
  have he (l : ℕ) :
      (if 0<l ∧ l.Coprime h then
        (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
          ∑p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*θ⁻¹ (p : ZMod r)*
            lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))) else 0)=
        ∑p∈lemma56PaperPrimes D,F p l := by
    dsimp [F,C,proposition71PrimitivePrimeDeltaTerm]
    by_cases hl : 0<l ∧ l.Coprime h
    · simp only [if_pos hl,mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    · simp only [if_neg hl,mul_zero,sum_const_zero]
  simp_rw [he]
  rw [Summable.tsum_finsetSum hs]
  simp only [F,C,tsum_mul_left]

lemma proposition71_induced_negative_nat {r h : ℕ} [NeZero r] [NeZero h]
    (θ : DirichletCharacter ℂ r) (l : ℕ) :
    θ.changeLevel (r.dvd_mul_right h) (-(l : ZMod (r*h)))=
      if l.Coprime h then θ (-1 : ZMod r)*θ (l : ZMod r) else 0 := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  have hn : θ.changeLevel (r.dvd_mul_right h) (-1 : ZMod (r*h))=θ (-1 : ZMod r) := by
    simpa only [Nat.cast_one] using inducedGauss_changeLevel_neg_nat θ 1 (Nat.coprime_one_left h)
  rw [show -(l : ZMod (r*h))=(-1)*(l : ZMod (r*h)) by ring,map_mul,hn,
    inducedGauss_changeLevel_nat]
  split_ifs <;> simp

/-- Literal induced character fiber; the condition (l,h)=1 is restored by
actual changeLevel evaluation and not an extra source assumption. -/
theorem proposition71_induced_character_fiber {D r h d p : ℕ} [NeZero r] [NeZero h]
    (c : ℝ) (a : ℕ → ℂ) (θ : DirichletCharacter ℂ r) :
    proposition71CharacterDeltaFiber D d ((p : ℝ)*((r*h : ℕ) : ℝ))
      (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m)
      (θ.changeLevel (r.dvd_mul_right h))=
      θ (-1 : ZMod r)*∑'l : ℕ, proposition71PrimitivePrimeDeltaTerm D c a h d θ p l := by
  unfold proposition71CharacterDeltaFiber
  rw [←proposition71_positive_nat_tsum _ (by simp [proposition71PrimitivePrimeDeltaTerm]),←tsum_mul_left]
  apply tsum_congr
  intro l
  rcases l with ⟨l,hl0⟩
  dsimp only
  rw [proposition71_induced_negative_nat]
  have hscale : (p : ℝ)*((r*h : ℕ) : ℝ)=(p : ℝ)*(h : ℝ)*(r : ℝ) := by push_cast; ring
  rw [hscale]
  by_cases hl : l.Coprime h <;> simp [proposition71PrimitivePrimeDeltaTerm,hl,hl0] <;> ring

/-- Genuine full prime-average transport to the already defined original
sigma, with its negative-character factor left visible. -/
theorem proposition71_induced_source_sigma {D r h d : ℕ} [NeZero r] [NeZero h]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hk : h*r∈lemma81PolynomialIndices D)
    (hd : 0<d) {B : ℝ} (hB : 0≤B) (c : ℝ) (a : ℕ → ℂ)
    (ha : Lemma81AdmissibleSequence D B a) (θ : DirichletCharacter ℂ r) :
    (∑p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*
      conj (θ.changeLevel (r.dvd_mul_right h) (p : ZMod (r*h)))*
      proposition71CharacterDeltaFiber D d ((p : ℝ)*((r*h : ℕ) : ℝ))
        (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m)
        (θ.changeLevel (r.dvd_mul_right h)))=
      θ (-1 : ZMod r)*proposition71OriginalSigmaSeries D c a h d θ := by
  rw [proposition71_original_sigma_prime_exchange hD hL hk hd hB c a ha θ,mul_sum]
  apply sum_congr rfl
  intro p hp
  have hh : 0<h := Nat.pos_of_ne_zero (NeZero.ne h)
  have hr : 0<r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hhS := (proposition71_short_factors hh hr hk).1
  have hh' := (proposition71_mem_indices D h).mp hhS
  have hph : p.Coprime h := by
    simpa only [ZMod.isUnit_iff_coprime,Nat.coprime_comm] using
      proposition71_short_index_unit hp hh'.1 hh'.2
  rw [inducedGauss_changeLevel_nat,if_pos hph,proposition71_induced_character_fiber]
  rw [←MulChar.star_apply' θ (p : ZMod r)]
  simp only [starRingEnd_apply]
  ring

/-- The true induced Gauss amplitude costs sqrt(r), while the entire prime
cancellation is retained inside the original sigma. -/
theorem proposition71_induced_gauss_source_bound {D r h d : ℕ} [NeZero r] [NeZero h]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hk : h*r∈lemma81PolynomialIndices D)
    (hd : 0<d) {B : ℝ} (hB : 0≤B) (c : ℝ) (a : ℕ → ℂ)
    (ha : Lemma81AdmissibleSequence D B a) (θ : DirichletCharacter ℂ r) (hθ : θ.IsPrimitive) :
    letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
    ‖gaussSum (θ.changeLevel (r.dvd_mul_right h))⁻¹ ZMod.stdAddChar*
      (∑p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*
        conj (θ.changeLevel (r.dvd_mul_right h) (p : ZMod (r*h)))*
        proposition71CharacterDeltaFiber D d ((p : ℝ)*((r*h : ℕ) : ℝ))
          (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m)
          (θ.changeLevel (r.dvd_mul_right h)))‖≤
      Real.sqrt (r : ℝ)*‖proposition71OriginalSigmaSeries D c a h d θ‖ := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  rw [proposition71_induced_source_sigma hD hL hk hd hB c a ha θ]
  simp only [norm_mul]
  have hg := inducedGauss_inverse_norm_le_sqrt_conductor (θ.changeLevel (r.dvd_mul_right h))
  rw [lemma44_conductor_changeLevel,hθ] at hg
  have hc := θ.norm_le_one (-1 : ZMod r)
  have hc' := mul_le_mul_of_nonneg_right hc (norm_nonneg (proposition71OriginalSigmaSeries D c a h d θ))
  simpa only [one_mul] using mul_le_mul hg hc' (by positivity) (Real.sqrt_nonneg _)

end ZhangLS.Spec
