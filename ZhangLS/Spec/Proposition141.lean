import ZhangLS.Spec.Proposition141RemainingLittleO

/-! Original Proposition14.1, assembled from the actual front, signed prime
corrections, two genuine gcd reindexings, literal character sources, actual
χ-induced main normalization, and complete small/large conductor bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex

/-- Exact source equality at the end of the Section14 arithmetic reduction. -/
theorem proposition141_actual_reciprocal_source_partition {D:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (a:ℕ→ℂ) (β:ℂ) :
    proposition141ReciprocalGcdMean χ β κ a=
      proposition141PrincipalTotal χ β κ a+proposition141MainTerm χ β κ a+
        proposition141RemainingMean χ β κ a := by
  rw [proposition141_reciprocal_fixed_gcd_mean χ hD hL hmod hB hκ a β,
    proposition141_fixed_gcd_full_character_mean χ hD hL hmod hB hκ a β,
    proposition141_full_character_mean_partition χ hD β κ a,
    proposition141_chi_induced_total_eq_main χ hD hmod β κ a]

/-- The unchanged original Proposition14.1 target, with arbitrary τ₅-bounded
κ*, bounded original closed-support a*, genuine χ under (A), and the full
complex β disk. All coefficient bounds and epsilon precede one threshold. -/
theorem proposition141_original : Proposition141Target := by
  intro Bκ Ba hBκ hBa ε hε
  have hthird:0<ε/3 := by positivity
  obtain ⟨Nf,hNf,hfront⟩ := proposition141_original_reciprocal_gcd_reduction Bκ Ba hBκ hBa (ε/3) hthird
  obtain ⟨Np,hNp,hprincipal⟩ := proposition141_uniform_principal_saving Bκ Ba hBκ hBa (ε/3) hthird
  obtain ⟨Nr,hNr,hremaining⟩ := proposition141_actual_remaining_little_o Bκ Ba hBκ hBa (ε/3) hthird
  obtain ⟨Ns,hNs,hmod⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max Nf (max Np (max Nr (max Ns ⌈Real.exp 2000⌉₊)))
  refine ⟨D₀,hNf.trans (le_max_left _ _),?_⟩
  intro D hlarge χ hA κ a hκ ha β hβ
  have hf:Nf≤D := by dsimp [D₀] at hlarge; omega
  have hp:Np≤D := by dsimp [D₀] at hlarge; omega
  have hr:Nr≤D := by dsimp [D₀] at hlarge; omega
  have hs:Ns≤D := by dsimp [D₀] at hlarge; omega
  have he:⌈Real.exp 2000⌉₊≤D := by dsimp [D₀] at hlarge; omega
  have hD:1<D := by have := hNf.trans hf; omega
  have hL:2000≤lemma23PaperL D := by
    have hex:Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast he)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos _) hex
  have h1 := hfront D hf χ hA κ a hκ ha β hβ
  have h2 := hprincipal χ hp β hβ κ a hκ ha
  have h3 := hremaining D hr χ hA κ a hκ ha β hβ
  have hid := proposition141_actual_reciprocal_source_partition χ hD hL (hmod D hs) hBκ.le hκ a β
  have hsplit : proposition141ThetaTwo χ β κ a-proposition141MainTerm χ β κ a=
      (proposition141ThetaTwo χ β κ a-proposition141ReciprocalGcdMean χ β κ a)+
        proposition141PrincipalTotal χ β κ a+proposition141RemainingMean χ β κ a := by
    rw [hid]
    ring
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3).trans_eq (by ring))

end ZhangLS.Spec
