import ZhangLS.Spec.Proposition71FrontLargeTail
import ZhangLS.Spec.Proposition71TailScalarBudget
import ZhangLS.Spec.Proposition71FrontContourObjects

/-! # Paying for the full conductor and short-support weights in the large-m tail -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 3500000

lemma proposition71_short_linear_mass_bound {P B : ℝ} (hP : 0≤P) (hB : 0≤B)
    (S : Finset ℕ) (hS : ∀n∈S, 0<n ∧ (n : ℝ)≤P)
    (a : ℕ → ℂ) (ha : ∀n∈S, ‖a n‖≤B) :
    proposition71ShortLinearMass S a≤B*P^2 := by
  have hsub : S⊆Icc 1 ⌊P⌋₊ := fun n hn => mem_Icc.mpr ⟨(hS n hn).1,Nat.le_floor (hS n hn).2⟩
  have hcard : (S.card : ℝ)≤P := by
    have hh := card_le_card hsub
    simp only [Nat.card_Icc,add_tsub_cancel_right] at hh
    exact (by exact_mod_cast hh : (S.card : ℝ)≤⌊P⌋₊).trans (Nat.floor_le hP)
  unfold proposition71ShortLinearMass
  calc
    _≤∑_n∈S, B*P := sum_le_sum (fun n hn => mul_le_mul (ha n hn) (hS n hn).2 (Nat.cast_nonneg n) hB)
    _=(S.card : ℝ)*(B*P) := by simp
    _≤P*(B*P) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hB hP)
    _=_ := by ring

lemma proposition71_primitive_gauss_normalized_norm_le_one {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1) :
    ‖gaussSum θ⁻¹ ZMod.stdAddChar/(N : ℂ)‖≤1 := by
  have hi : θ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def,DirichletCharacter.conductor_inv]
    exact (DirichletCharacter.isPrimitive_def θ).mp hθ
  have hNp : 0<(N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [norm_div,proposition71_primitive_gauss_norm θ⁻¹ hi hN,Complex.norm_natCast]
  apply (div_le_one hNp).mpr
  apply (Real.sqrt_le_iff).mpr
  exact ⟨hNp.le,by nlinarith⟩

noncomputable def proposition71FrontLargeTailConstant : ℝ :=
  4*proposition71LargeDeltaTailConstant*proposition71TauFiveQuadraticMass

lemma proposition71_front_large_tail_constant_pos : 0<proposition71FrontLargeTailConstant := by
  unfold proposition71FrontLargeTailConstant
  exact mul_pos (mul_pos (by norm_num) proposition71_large_delta_tail_constant_pos)
    proposition71_tau_five_quadratic_mass_pos

/-- The true q² short-index loss and the actual Gauss factor are absorbed by
the proved Gaussian tail, yielding an absolute D⁻¹ rate. -/
theorem proposition71_front_large_tail_main_rate {D N : ℕ} [NeZero N]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hNP : (N : ℝ)≤2*lemma23PaperP D^2)
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    {Bc Ba : ℝ} (hBc : 0≤Bc) (hBa : 0≤Ba) (c : ℕ → ℂ)
    (hc : ∀m, 0<m → ‖c m‖≤Bc*(lemma34Tau 5 m : ℝ))
    (htail : ∀m : ℕ, (m : ℝ)<lemma23PaperP D^2 → c m=0)
    (S : Finset ℕ) (hS : ∀n∈S, 0<n ∧ (n : ℝ)≤lemma23PaperP D)
    (a : ℕ → ℂ) (ha : ∀n∈S, ‖a n‖≤Ba)
    (hgap : ∀n∈S, ((N : ℝ)*(n : ℝ))*lemma51PaperT0 D^(51/50 : ℝ)<lemma23PaperP D^2) :
    ‖(gaussSum θ⁻¹ ZMod.stdAddChar/(N : ℂ))*
      (∑'m, proposition71DeltaOneDoubleTerm D c S a (N : ℝ) m)‖≤
      proposition71FrontLargeTailConstant*Bc*Ba/(D : ℝ) := by
  have hNp : 0<(N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hC := proposition71_large_delta_tail_constant_pos.le
  have hM := proposition71_tau_five_quadratic_mass_pos.le
  have hshort0 := proposition71_short_linear_mass_nonneg S a
  have hshort := proposition71_short_linear_mass_bound (Real.exp_pos _).le hBa S hS a ha
  change proposition71ShortLinearMass S a≤Ba*lemma23PaperP D^2 at hshort
  have ht := (proposition71_front_large_tail_tsum_bound hD hL hNp hBc c hc htail S
    (fun n hn => (hS n hn).1) a hgap).2
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hscalar : lemma23PaperP D^6*Real.exp (-lemma23PaperL D^10/2)≤(D : ℝ)⁻¹ := by
    apply le_trans _ (proposition71_tail_scalar_budget hD hL)
    have hpow : 1≤lemma23PaperL D^72 := one_le_pow₀ hL1
    have hP0 : 0≤lemma23PaperP D^6 := pow_nonneg (Real.exp_pos (lemma23PaperL D^9)).le _
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hP0)
      (Real.exp_pos (-lemma23PaperL D^10/2)).le
    simpa only [mul_one] using hh
  rw [norm_mul]
  calc
    _≤‖∑'m, proposition71DeltaOneDoubleTerm D c S a (N : ℝ) m‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (proposition71_primitive_gauss_normalized_norm_le_one θ hθ hN)
    _≤_ := ht
    _≤(proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*
        (2*lemma23PaperP D^2)^2*Bc*(Ba*lemma23PaperP D^2))*proposition71TauFiveQuadraticMass := by gcongr
    _=(proposition71FrontLargeTailConstant*Bc*Ba)*(lemma23PaperP D^6*Real.exp (-lemma23PaperL D^10/2)) := by
      unfold proposition71FrontLargeTailConstant
      ring
    _≤(proposition71FrontLargeTailConstant*Bc*Ba)*(D : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hscalar (mul_nonneg (mul_nonneg proposition71_front_large_tail_constant_pos.le hBc) hBa)
    _=_ := by rw [div_eq_mul_inv]

/-- The original J(1) integral of the actual infinite tail is small; this is
not merely a bound for a surrogate finite series. -/
theorem proposition71_front_large_tail_contour_rate {D N : ℕ} [NeZero N]
    (hD : 1<D) (hL : 20000≤lemma23PaperL D) (hNP : (N : ℝ)≤2*lemma23PaperP D^2)
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    {Bc Ba : ℝ} (hBc : 0≤Bc) (hBa : 0≤Ba) (c : ℕ → ℂ)
    (hc : ∀m, 0<m → ‖c m‖≤Bc*(lemma34Tau 5 m : ℝ))
    (htail : ∀m : ℕ, (m : ℝ)<lemma23PaperP D^2 → c m=0)
    (S : Finset ℕ) (hS : ∀n∈S, 0<n ∧ (n : ℝ)≤lemma23PaperP D)
    (a : ℕ → ℂ) (ha : ∀n∈S, ‖a n‖≤Ba)
    (hgap : ∀n∈S, ((N : ℝ)*(n : ℝ))*lemma51PaperT0 D^(51/50 : ℝ)<lemma23PaperP D^2) :
    ‖lemma81NormalizedSegmentIntegral D 1 (proposition71FrontActualKernel D θ c S a)‖≤
      (proposition71FrontErrorConstant+proposition71FrontLargeTailConstant)*Bc*Ba/(D : ℝ) := by
  rw [proposition71_front_original_contour_exact]
  have he := (proposition71_front_transform_uniform_rate hD hL hNP θ hθ hN hBc hBa c hc S hS a ha).2
  have ht := proposition71_front_large_tail_main_rate hD (by linarith) hNP θ hθ hN hBc hBa c hc htail S hS a ha hgap
  exact (norm_le_norm_sub_add _ _).trans ((add_le_add he ht).trans_eq (by ring))

end ZhangLS.Spec
