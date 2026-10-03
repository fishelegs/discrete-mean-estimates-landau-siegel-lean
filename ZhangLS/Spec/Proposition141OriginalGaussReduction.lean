import ZhangLS.Spec.Proposition141ExceptionalMean

/-! # Original Θ₂ reduced to its actual primitive χψ Gauss/Δ₁ mean

All analytic transformations and the actual Ψ₁→Ψ extension are attached.
The remaining work is exact arithmetic averaging/reindexing and main terms.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

theorem proposition141_actual_deltaOne_series_summable {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (κ a:ℕ→ℂ) (ψ:DirichletCharacter ℂ p)
    (hD:1<D) (hL:20000≤lemma23PaperL D) (hψ:Lemma23InPsi (D:=D) ψ)
    (hNP:((D*p:ℕ):ℝ)≤2*lemma23PaperP D^2) (hshort:2*lemma61PaperP4 D≤lemma23PaperP D)
    {Bκ Ba:ℝ} (hBκ:0≤Bκ) (hBa:0≤Ba)
    (hκ:Proposition141KappaBound Bκ κ) (ha:Proposition141AdmissibleSequence D Ba a) :
    Summable (proposition71DeltaOneDoubleTerm D (fun n=>κ n*ψ (n:ZMod p))
      (proposition141Indices D) (fun n=>a n*ψ⁻¹ (n:ZMod p)) ((D*p:ℕ):ℝ)) := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hθ := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1 (lemma44_family_coprime χ ψ (by linarith) hψ)
  have hN:D*p≠1 := by
    have hh:D≤D*p := Nat.le_mul_of_pos_right D (Nat.pos_of_ne_zero (NeZero.ne p))
    omega
  have hc (n:ℕ) (hn:0<n) : ‖κ n*ψ (n:ZMod p)‖≤Bκ*(lemma34Tau 5 n:ℝ) := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (ψ.norm_le_one _)).trans (hκ n hn)
  have hS (n:ℕ) (hn:n∈proposition141Indices D) : 0<n ∧ (n:ℝ)≤lemma23PaperP D := by
    have hh := proposition141_mem_indices D n |>.mp hn
    exact ⟨hh.1,hh.2.trans hshort⟩
  have hb (n:ℕ) (hn:n∈proposition141Indices D) : ‖a n*ψ⁻¹ (n:ZMod p)‖≤Ba := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (ψ⁻¹.norm_le_one _)).trans
      (ha.1 n (proposition141_mem_indices D n |>.mp hn).1)
  exact (proposition71_front_transform_uniform_rate hD hL hNP (lemma44CharacterTwist χ ψ) hθ hN
    hBκ hBa _ hc _ hS _ hb).1

theorem proposition141_ambient_gauss_little_o (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀χ:RealPrimitiveCharacter D,
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
          ‖proposition141AmbientMean χ β κ a-proposition141GaussDeltaOneMean χ β κ a‖≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨N,hN,hmean⟩ := proposition141_uniform_front_mean_rate
  let K := Real.exp 60*proposition71FrontErrorConstant*Bκ*Ba
  let D₀ := max N ⌈K/ε⌉₊
  refine ⟨D₀,hN.trans (le_max_left _ _),?_⟩
  intro D hlarge χ κ a hκ ha β hβ
  have hND:N≤D := (le_max_left _ _).trans hlarge
  have hDp:0<(D:ℝ) := by exact_mod_cast (show 0<D by have := hN.trans hND; omega)
  have he:K/ε≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hlarge)
  have hrate:K/(D:ℝ)≤ε := by
    apply (div_le_iff₀ hDp).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp he
  apply (hmean χ hND β hβ Bκ Ba hBκ.le hBa.le κ a hκ ha).trans
  exact mul_le_mul_of_nonneg_right hrate (by rw [proposition141_actual_prime_masses_equal]; exact lemma56_prime_mass_nonneg D)

/-- Fully faithful common-front reduction for Proposition14.1, with the
original coefficient, family, shift, conductor and threshold quantifiers. -/
theorem proposition141_original_gauss_delta_reduction (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
          ‖proposition141ThetaTwo χ β κ a-proposition141GaussDeltaOneMean χ β κ a‖≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨N₁,hN₁,hfamily⟩ := proposition141_original_fourteen_three Bκ Ba hBκ hBa (ε/2) (by positivity)
  obtain ⟨N₂,hN₂,hgauss⟩ := proposition141_ambient_gauss_little_o Bκ Ba hBκ hBa (ε/2) (by positivity)
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro D hlarge χ hA κ a hκ ha β hβ
  have h1 := hfamily D ((le_max_left _ _).trans hlarge) χ hA κ a hκ ha β hβ
  have h2 := hgauss D ((le_max_right _ _).trans hlarge) χ κ a hκ ha β hβ
  have he : proposition141ThetaTwo χ β κ a-proposition141GaussDeltaOneMean χ β κ a=
      (proposition141ThetaTwo χ β κ a-proposition141AmbientMean χ β κ a)+
      (proposition141AmbientMean χ β κ a-proposition141GaussDeltaOneMean χ β κ a) := by ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end ZhangLS.Spec
