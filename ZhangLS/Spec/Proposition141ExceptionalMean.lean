import ZhangLS.Spec.Proposition141FrontMean
import ZhangLS.Spec.Proposition71InfiniteExceptionalContour

/-! # Original Section14 (14.3), with actual Ψ₁ and Ψ₂

The exceptional-family theorem is instantiated at χψ, conductor Dp and the
actual 2P₄ support. Its scale gap is derived, and κ* stays arbitrary.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

theorem proposition141_exceptional_mean_little_o (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
          ‖∑ψ∈proposition21ActualPsi2Family χ,proposition141ShiftWeight D ψ.1.val β*
            proposition141Integral χ κ a ψ.2‖≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨Ne,hNe,hex⟩ := proposition71_infinite_exceptional_contour_little_o
    Bκ Ba (Real.exp 60) hBκ hBa (Real.exp_pos _) ε hε
  obtain ⟨Ng,hNg,hgeo⟩ := proposition141_uniform_front_geometry
  refine ⟨max Ne Ng,hNe.trans (le_max_left _ _),?_⟩
  intro D hlarge χ hA κ a hκ ha β hβ
  have he:Ne≤D := (le_max_left _ _).trans hlarge
  have hg := hgeo D ((le_max_right _ _).trans hlarge)
  have hL:2000≤lemma23PaperL D := by linarith [hg.1]
  let N:lemma33CharacterIndex D→ℕ := fun ψ=>D*ψ.1.val
  letI (ψ:lemma33CharacterIndex D) : NeZero (N ψ) :=
    ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne ψ.1.val)⟩
  let θ:(ψ:lemma33CharacterIndex D)→DirichletCharacter ℂ (N ψ) := fun ψ=>lemma44CharacterTwist χ ψ.2
  let w:lemma33CharacterIndex D→ℂ := fun ψ=>proposition141ShiftWeight D ψ.1.val β
  have hp (ψ:lemma33CharacterIndex D) : ψ.1.val∈lemma56PaperPrimes D := by
    rw [←proposition141_prime_windows_equal]
    exact ψ.1.property
  have hθ (ψ:lemma33CharacterIndex D) (hψ:ψ∈proposition21ActualPsi2Family χ) : (θ ψ).IsPrimitive := by
    have hmem := ((proposition21_mem_psi2 χ ψ.1 ψ.2).mp hψ).1
    exact lemma44CharacterTwist_isPrimitive χ ψ.2 hmem.2.1 (lemma44_family_coprime χ ψ.2 (by linarith) hmem)
  have hN (ψ:lemma33CharacterIndex D) (_hψ:ψ∈proposition21ActualPsi2Family χ) : N ψ≠1 := (hg.2.2 ψ.1.val (hp ψ)).1.2
  have hNP (ψ:lemma33CharacterIndex D) (_hψ:ψ∈proposition21ActualPsi2Family χ) : (N ψ:ℝ)≤2*lemma23PaperP D^2 :=
    (hg.2.2 ψ.1.val (hp ψ)).1.1
  have hX : ⌊2*lemma61PaperP4 D⌋₊≤⌊lemma23PaperP D⌋₊ := Nat.floor_mono hg.2.1
  have hgap (ψ:lemma33CharacterIndex D) (_hψ:ψ∈proposition21ActualPsi2Family χ)
      (n:ℕ) (hn:n∈Icc 1 ⌊2*lemma61PaperP4 D⌋₊) :
      ((N ψ:ℝ)*(n:ℝ))*lemma51PaperT0 D^(51/50:ℝ)<lemma23PaperP D^2 := by
    exact (hg.2.2 ψ.1.val (hp ψ)).2 n (by rwa [proposition141_indices_eq_closed_prefix])
  have hshort (n:ℕ) (hn:n∈Icc 1 ⌊2*lemma61PaperP4 D⌋₊) : ‖a n‖≤Ba := ha.1 n (mem_Icc.mp hn).1
  have hw (ψ:lemma33CharacterIndex D) (_hψ:ψ∈proposition21ActualPsi2Family χ) : ‖w ψ‖≤Real.exp 60 := by
    have hh := proposition141_prime_t0_shift_norm (p:=ψ.1.val) hL hβ (hp ψ)
    simpa only [w,proposition141ShiftWeight,Complex.ofReal_mul,Complex.ofReal_natCast] using hh
  have hb := hex D he χ hA N θ hθ hN hNP ⌊2*lemma61PaperP4 D⌋₊ hX hgap κ a hκ hshort w hw
  apply le_trans _ hb
  apply le_of_eq
  congr 1
  apply sum_congr rfl
  intro ψ hψ
  rw [proposition141_integral_infinite_front]

lemma proposition141_actual_family_partition {D:ℕ} (χ:RealPrimitiveCharacter D)
    (f:lemma33CharacterIndex D→ℂ) :
    (∑ψ∈proposition21ActualPsi1Family χ,f ψ)+(∑ψ∈proposition21ActualPsi2Family χ,f ψ)=
      ∑ψ∈lemma33ActualFamily D,f ψ := by
  have he:proposition21ActualPsi1Family χ=(lemma33ActualFamily D).filter (fun ψ=>Lemma23InPsi1 χ ψ.2) := by
    ext ψ
    simp only [proposition21ActualPsi1Family,lemma33ActualFamily,mem_filter,mem_univ,true_and]
    constructor
    · intro hh
      exact ⟨hh.1,hh⟩
    · exact fun hh=>hh.2
  rw [he]
  unfold proposition21ActualPsi2Family
  exact sum_filter_add_sum_filter_not _ _ _

/-- The original family-extension step (14.3), uniformly in the full β disk. -/
theorem proposition141_original_fourteen_three (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
          ‖proposition141ThetaTwo χ β κ a-proposition141AmbientMean χ β κ a‖≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨D₀,hD₀,hbad⟩ := proposition141_exceptional_mean_little_o Bκ Ba hBκ hBa ε hε
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ hA κ a hκ ha β hβ
  have hb := hbad D hD χ hA κ a hκ ha β hβ
  have he := proposition141_actual_family_partition χ
    (fun ψ=>proposition141ShiftWeight D ψ.1.val β*proposition141Integral χ κ a ψ.2)
  change proposition141ThetaTwo χ β κ a+
    (∑ψ∈proposition21ActualPsi2Family χ,proposition141ShiftWeight D ψ.1.val β*proposition141Integral χ κ a ψ.2)=
      proposition141AmbientMean χ β κ a at he
  rw [←he,sub_add_cancel_left,norm_neg]
  exact hb

end ZhangLS.Spec
