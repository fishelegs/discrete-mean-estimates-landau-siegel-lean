import ZhangLS.Spec.Proposition141FrontObjects
import ZhangLS.Spec.Proposition141FrontGeometry

/-! # The actual Section14 ambient Gauss/Δ₁ mean

The common analytic theorem is instantiated at its true conductor Dp and
functional-equation character χψ. The coefficient characters remain ψ.
The exact original (pt₀)^β weight and arbitrary κ*,a* remain visible.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141GaussDeltaOneTerm {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (κ a:ℕ→ℂ) (ψ:DirichletCharacter ℂ p) : ℂ :=
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  (gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar/((D*p:ℕ):ℂ))*
    ∑'m:ℕ,proposition71DeltaOneDoubleTerm D (fun n=>κ n*ψ (n:ZMod p))
      (proposition141Indices D) (fun n=>a n*ψ⁻¹ (n:ZMod p)) ((D*p:ℕ):ℝ) m

noncomputable def proposition141GaussDeltaOneMean {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  ∑ψ∈lemma33ActualFamily D,proposition141ShiftWeight D ψ.1.val β*
    proposition141GaussDeltaOneTerm χ κ a ψ.2

/-- Fully instantiated ambient-family transformation, with a quantitative
mass/D error and no assumption (A) or averaged analytic premise. -/
theorem proposition141_uniform_front_mean_rate :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      ‖proposition141AmbientMean χ β κ a-proposition141GaussDeltaOneMean χ β κ a‖≤
        (Real.exp 60*proposition71FrontErrorConstant*Bκ*Ba/(D:ℝ))*lemma33ActualPrimeMass D := by
  obtain ⟨D₀,hD₀,hgeo⟩ := proposition141_uniform_front_geometry
  refine ⟨D₀,hD₀,?_⟩
  intro D χ hlarge β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hg := hgeo D hlarge
  have hD:1<D := by have := hD₀.trans hlarge; omega
  have hL:2000≤lemma23PaperL D := by linarith [hg.1]
  let N:lemma33CharacterIndex D→ℕ := fun ψ=>D*ψ.1.val
  letI (ψ:lemma33CharacterIndex D) : NeZero (N ψ) :=
    ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne ψ.1.val)⟩
  let θ:(ψ:lemma33CharacterIndex D)→DirichletCharacter ℂ (N ψ) := fun ψ=>lemma44CharacterTwist χ ψ.2
  let c:lemma33CharacterIndex D→ℕ→ℂ := fun ψ n=>κ n*ψ.2 (n:ZMod ψ.1.val)
  let b:lemma33CharacterIndex D→ℕ→ℂ := fun ψ n=>a n*ψ.2⁻¹ (n:ZMod ψ.1.val)
  let w:lemma33CharacterIndex D→ℂ := fun ψ=>proposition141ShiftWeight D ψ.1.val β
  have hp (ψ:lemma33CharacterIndex D) : ψ.1.val∈lemma56PaperPrimes D := by
    rw [←proposition141_prime_windows_equal]
    exact ψ.1.property
  have hθ (ψ:lemma33CharacterIndex D) (hψ:ψ∈lemma33ActualFamily D) : (θ ψ).IsPrimitive := by
    have hmem:Lemma23InPsi (D:=D) ψ.2 := (mem_filter.mp hψ).2
    exact lemma44CharacterTwist_isPrimitive χ ψ.2 hmem.2.1 (lemma44_family_coprime χ ψ.2 (by linarith) hmem)
  have hN (ψ:lemma33CharacterIndex D) (_hψ:ψ∈lemma33ActualFamily D) : N ψ≠1 := (hg.2.2 ψ.1.val (hp ψ)).1.2
  have hNP (ψ:lemma33CharacterIndex D) (_hψ:ψ∈lemma33ActualFamily D) : (N ψ:ℝ)≤2*lemma23PaperP D^2 :=
    (hg.2.2 ψ.1.val (hp ψ)).1.1
  have hc (ψ:lemma33CharacterIndex D) (_hψ:ψ∈lemma33ActualFamily D) (n:ℕ) (hn:0<n) :
      ‖c ψ n‖≤Bκ*(lemma34Tau 5 n:ℝ) := by
    dsimp [c]
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (ψ.2.norm_le_one _)).trans (hκ n hn)
  have hS (ψ:lemma33CharacterIndex D) (_hψ:ψ∈lemma33ActualFamily D) (n:ℕ) (hn:n∈proposition141Indices D) :
      0<n ∧ (n:ℝ)≤lemma23PaperP D := by
    have hh := proposition141_mem_indices D n |>.mp hn
    exact ⟨hh.1,hh.2.trans hg.2.1⟩
  have hb (ψ:lemma33CharacterIndex D) (_hψ:ψ∈lemma33ActualFamily D) (n:ℕ) (hn:n∈proposition141Indices D) :
      ‖b ψ n‖≤Ba := by
    dsimp [b]
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (ψ.2⁻¹.norm_le_one _)).trans
      (ha.1 n (proposition141_mem_indices D n |>.mp hn).1)
  have hw (ψ:lemma33CharacterIndex D) (_hψ:ψ∈lemma33ActualFamily D) : ‖w ψ‖≤Real.exp 60 := by
    have hh := proposition141_prime_t0_shift_norm (p:=ψ.1.val) hL hβ (hp ψ)
    simpa only [w,proposition141ShiftWeight,Complex.ofReal_mul,Complex.ofReal_natCast] using hh
  have hbound := proposition71_front_actual_family_rate hD hg.1 (lemma33ActualFamily D) Subset.rfl
    N θ hθ hN hNP hBκ hBa (Real.exp_nonneg 60) c b hc (fun _=>proposition141Indices D) hS hb w hw
  have heq : proposition141AmbientMean χ β κ a-proposition141GaussDeltaOneMean χ β κ a=
      ∑ψ∈lemma33ActualFamily D,w ψ*(lemma81NormalizedSegmentIntegral D 1
        (proposition71FrontActualKernel D (θ ψ) (c ψ) (proposition141Indices D) (b ψ))-
        (gaussSum (θ ψ)⁻¹ ZMod.stdAddChar/(N ψ:ℂ))*
          ∑'m:ℕ,proposition71DeltaOneDoubleTerm D (c ψ) (proposition141Indices D) (b ψ) (N ψ:ℝ) m) := by
    unfold proposition141AmbientMean proposition141GaussDeltaOneMean
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro ψ hψ
    rw [proposition141_integral_actual_front]
    unfold proposition141GaussDeltaOneTerm
    rw [←proposition141_twist_inverse]
    dsimp [N,θ,c,b,w]
    ring
  rw [heq]
  exact hbound

end ZhangLS.Spec
