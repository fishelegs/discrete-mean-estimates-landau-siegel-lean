import ZhangLS.Spec.Proposition26OriginalObjects
import ZhangLS.Spec.Proposition26E2Energy
import ZhangLS.Spec.Proposition26EnergyAlgebra

/-! Exact conjugate reflection of the original real-profile Dirichlet sums,
including the actual infinite Gaussian sums. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate

lemma proposition26_real_profile_series_conjugate {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (w : ℕ→ℝ) (s : ℂ) :
    conj (∑'n:ℕ,LSeries.term (lemma112Coefficient χ ψ) s n*(w n:ℂ))=
      ∑'n:ℕ,LSeries.term (lemma112Coefficient χ ψ⁻¹) (conj s) n*(w n:ℂ) := by
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term]
  have hχ : conj (χ.evalNat n)=χ.evalNat n := by
    simpa only [RealPrimitiveCharacter.evalNat] using χ.conj_eval (n:ZMod D)
  have hψ : conj (ψ (n:ZMod p))=ψ⁻¹ (n:ZMod p) := MulChar.star_apply' ψ _
  have harg : (n:ℂ).arg≠Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have hp : conj ((n:ℂ)^s)=(n:ℂ)^(conj s) := by
    simpa only [map_natCast] using (Complex.cpow_conj (n:ℂ) s harg).symm
  simp only [LSeries.term_of_ne_zero hn,lemma112Coefficient,map_mul,map_div₀,
    Complex.conj_ofReal,hχ,hψ,hp]

lemma proposition26_conj_critical {s : ℂ} (hs : s.re=1/2) : conj s=1-s := by
  apply Complex.ext <;> norm_num [hs]

lemma proposition26_J2_critical_reflection {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : s.re=1/2) :
    proposition26J2 χ ψ⁻¹ (1-s)=conj (proposition26J2 χ ψ s) := by
  symm
  unfold proposition26J2
  rw [proposition26_real_profile_series_conjugate,proposition26_conj_critical hs]

lemma proposition26_Jtilde2_critical_reflection {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : s.re=1/2) :
    lemma112JtildeTwo χ ψ⁻¹ (1-s)=conj (lemma112JtildeTwo χ ψ s) := by
  symm
  unfold lemma112JtildeTwo
  rw [proposition26_real_profile_series_conjugate,proposition26_conj_critical hs]

/-- The source's (11.6) defect is exactly its conjugated-profile form on the
critical line, not a different norm. -/
lemma proposition26_smoothed_defect_critical {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : s.re=1/2) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    proposition26SmoothedDefect χ ψ s=
      lemma112JtildeOne χ ψ s-lemma23DirichletZ (lemma44CharacterTwist χ ψ) s*
        conj (lemma112JtildeTwo χ ψ s) := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  unfold proposition26SmoothedDefect
  rw [proposition26_Jtilde2_critical_reflection χ ψ hs]

lemma proposition26_twist_Z_critical_norm {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3≤lemma23PaperL D) (hψ : Lemma23InPsi (D:=D) ψ)
    {s : ℂ} (hs : s.re=1/2) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) s‖=1 := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hd := lemma112_twist_family_data χ ψ hL hψ
  exact lemma23DirichletZ_norm_eq_one_on_critical_line _ hd.1 hd.2.2.1 hs

/-- Exact original J-defect decomposition; the twist's unit modulus is a
proved character fact, not a phase assumption. -/
theorem proposition26_actual_three_defects {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3≤lemma23PaperL D) (hψ : Lemma23InPsi (D:=D) ψ)
    {s : ℂ} (hs : s.re=1/2) :
    ‖proposition26JDefect χ ψ s‖^2 ≤
      3*(‖proposition26J1 χ ψ s-lemma112JtildeOne χ ψ s‖^2+
        ‖proposition26SmoothedDefect χ ψ s‖^2+
        ‖proposition26J2 χ ψ s-lemma112JtildeTwo χ ψ s‖^2) := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let Z := lemma23DirichletZ (lemma44CharacterTwist χ ψ) s
  let A := proposition26J1 χ ψ s-lemma112JtildeOne χ ψ s
  let B := proposition26SmoothedDefect χ ψ s
  let C := -Z*conj (proposition26J2 χ ψ s-lemma112JtildeTwo χ ψ s)
  have hZ : ‖Z‖=1 := proposition26_twist_Z_critical_norm χ ψ hL hψ hs
  have hC : ‖C‖=‖proposition26J2 χ ψ s-lemma112JtildeTwo χ ψ s‖ := by
    simp only [C,norm_mul,norm_neg,hZ,one_mul,Complex.norm_conj]
  have he : proposition26JDefect χ ψ s=A+B+C := by
    dsimp [A,B,C,Z]
    rw [proposition26_smoothed_defect_critical χ ψ hs]
    unfold proposition26JDefect
    rw [map_sub]
    ring
  rw [he]
  have h := proposition26_three_square_bound A B C
  simpa only [A,B,hC] using h

end ZhangLS.Spec

/-! Finite positive-energy calculus for the actual source weights. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition26_two_square_bound (a b : ℂ) :
    ‖a+b‖^2≤2*(‖a‖^2+‖b‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith only [h,sq_nonneg (‖a‖-‖b‖)]

lemma proposition26_energy_add {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D)→ℂ→ℂ)
    (hw : ∀ψ∈lemma81GoodFamily χ,∀ρ∈lemma81ZeroFinset D ψ.2,0≤proposition26Weight c Y ψ ρ)
    (F G : (ψ : lemma33CharacterIndex D)→ℂ→ℂ) :
    proposition26Energy χ c Y (fun ψ s => F ψ s+G ψ s) ≤
      2*(proposition26Energy χ c Y F+proposition26Energy χ c Y G) := by
  unfold proposition26Energy
  rw [←sum_add_distrib,Finset.mul_sum]
  apply sum_le_sum
  intro ψ hψ
  rw [←sum_add_distrib,Finset.mul_sum]
  apply sum_le_sum
  intro ρ hρ
  exact (mul_le_mul_of_nonneg_left (proposition26_two_square_bound (F ψ ρ) (G ψ ρ))
    (hw ψ hψ ρ hρ)).trans_eq (by ring)

lemma proposition26_energy_pointwise_constant {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D)→ℂ→ℂ)
    (hw : ∀ψ∈lemma81GoodFamily χ,∀ρ∈lemma81ZeroFinset D ψ.2,0≤proposition26Weight c Y ψ ρ)
    (F : (ψ : lemma33CharacterIndex D)→ℂ→ℂ) (T : ℝ)
    (hF : ∀ψ∈lemma81GoodFamily χ,∀ρ∈lemma81ZeroFinset D ψ.2,‖F ψ ρ‖≤T) :
    proposition26Energy χ c Y F≤T^2*proposition26Energy χ c Y (fun _ _ => 1) := by
  unfold proposition26Energy
  simp only [norm_one,one_pow,mul_one,Finset.mul_sum]
  apply sum_le_sum
  intro ψ hψ
  apply sum_le_sum
  intro ρ hρ
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hF ψ hψ ρ hρ) 2) (hw ψ hψ ρ hρ)).trans_eq (by ring)

lemma proposition26_energy_congr_on_zeros {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D)→ℂ→ℂ)
    (F G : (ψ : lemma33CharacterIndex D)→ℂ→ℂ)
    (h : ∀ψ∈lemma81GoodFamily χ,∀ρ∈lemma81ZeroFinset D ψ.2,‖F ψ ρ‖=‖G ψ ρ‖) :
    proposition26Energy χ c Y F=proposition26Energy χ c Y G := by
  unfold proposition26Energy
  apply sum_congr rfl
  intro ψ hψ
  apply sum_congr rfl
  intro ρ hρ
  rw [h ψ hψ ρ hρ]

/-- The actual defect's weighted energy decomposes into the two original
unsmoothing errors and the original L11.2 smoothed defect. Every local
critical-line, phase and positivity condition is discharged uniformly. -/
theorem proposition26_actual_defect_energy_split {c : ℝ} (hc : Lemma52CompatibleConstant c) :
    ∃N:ℕ,∀D:ℕ,N≤D → ∀χ:RealPrimitiveCharacter D,
      ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
        (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
        proposition26Energy χ c Y (fun ψ s => proposition26JDefect χ ψ.2 s) ≤
          3*(proposition26Energy χ c Y (fun ψ s => proposition26J1 χ ψ.2 s-lemma112JtildeOne χ ψ.2 s)+
            proposition26Energy χ c Y (fun ψ s => proposition26SmoothedDefect χ ψ.2 s)+
            proposition26Energy χ c Y (fun ψ s => proposition26J2 χ ψ.2 s-lemma112JtildeTwo χ ψ.2 s)) := by
  obtain ⟨Nw,hw⟩ := proposition26_actual_weight_data hc
  refine ⟨max Nw lemma23SectionFourModulusThreshold,?_⟩
  intro D hD χ Y hY
  have hDw := (le_max_left _ _).trans hD
  have hsection := (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold hsection).1
  have hdata := hw D hDw χ Y hY
  unfold proposition26Energy
  rw [←sum_add_distrib,←sum_add_distrib,Finset.mul_sum]
  apply sum_le_sum
  intro ψ hψ
  rw [←sum_add_distrib,←sum_add_distrib,Finset.mul_sum]
  apply sum_le_sum
  intro ρ hρ
  have hg := (lemma81_mem_good_family χ ψ).mp hψ
  have hp := proposition26_actual_three_defects χ ψ.2 hL hg.1 (hdata ψ hψ ρ hρ).1
  exact (mul_le_mul_of_nonneg_left hp (hdata ψ hψ ρ hρ).2.1).trans_eq (by ring)

/-- The real finite Xi3 definition agrees exactly with the literal complex
source sum once the proved original critical-line/positivity threshold holds. -/
theorem proposition26_original_Xi3_complex_identity {c : ℝ}
    (hc : Lemma52CompatibleConstant c) :
    ∃N:ℕ,∀D:ℕ,N≤D → ∀χ:RealPrimitiveCharacter D,
      ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
        (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
        (∑ψ∈lemma81GoodFamily χ,∑ρ∈lemma81ZeroFinset D ψ.2,
          lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ*
            (‖proposition26JDefect χ ψ.2 ρ‖:ℂ)*(‖proposition26H2 χ ψ.2 ρ‖:ℂ)*
              lemma81Omega D ρ)=(proposition26XiThreeStar χ c Y:ℂ) := by
  obtain ⟨N,hN⟩ := proposition26_actual_weight_data hc
  refine ⟨N,?_⟩
  intro D hD χ Y hY
  have hw := hN D hD χ Y hY
  unfold proposition26XiThreeStar
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  apply sum_congr rfl
  intro ψ hψ
  apply sum_congr rfl
  intro ρ hρ
  rw [←(hw ψ hψ ρ hρ).2.2]
  ring

end ZhangLS.Spec
