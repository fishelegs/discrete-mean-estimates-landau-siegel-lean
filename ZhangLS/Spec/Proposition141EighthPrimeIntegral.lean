import ZhangLS.Spec.Proposition141ShiftedEstimate
import ZhangLS.Spec.Lemma54EighthActualTail

/-! # Full-frequency actual χconjθ prime integral, including complex β

The original nonprincipal 5.6 controls only the central D/2 frequencies.
The exterior uses a proved global amplitude and genuine eighth-order δ decay.
No conductor-averaged estimate is assumed or inferred here.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped ComplexConjugate

/-- The small complex shift has a uniform pointwise amplitude bound on
actual family primes. This bound is used ONLY outside cancellation estimates. -/
theorem proposition141_small_shift_power_norm {D : ℕ} (hL : 2000≤lemma23PaperL D)
    {β : ℂ} (hβ : ‖β‖<5*lemma44PaperAlpha D) {x : ℝ}
    (hxP : lemma23PaperP D≤x) (hxhi : x≤2*lemma23PaperP D) :
    ‖(x:ℂ)^β‖≤Real.exp 40 := by
  have hp := proposition141_complex_shift_parameters hL hβ
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hx := hP.trans_le hxP
  have hloglo : 2≤Real.log x := hp.1.trans (Real.log_le_log hP hxP)
  have hloghi : Real.log x≤2*Real.log (lemma23PaperP D) := by
    have hh := Real.log_le_log hx hxhi
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hP.ne'] at hh
    have hlog2 : Real.log 2≤1 := by
      simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have he : Real.log x*β.re≤40 := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self β.re) (by linarith : 0≤Real.log x)
    have h2 := mul_le_mul_of_nonneg_left hloghi (abs_nonneg β.re)
    nlinarith [hp.2.2]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx,Real.rpow_def_of_pos hx]
  exact Real.exp_le_exp.mpr he

theorem proposition141_shifted_product_prime_continuous {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N) (β : ℂ) :
    Continuous (proposition141ShiftedProductPrimeSum χ θ β) := by
  apply continuous_finsetSum
  intro p hp
  have hpp := ((lemma56_mem_paper_primes D p).mp hp).1
  apply continuous_const.mul
  exact Continuous.const_cpow (by fun_prop) (Or.inl (Nat.cast_ne_zero.mpr hpp.ne_zero))

/-- A global all-height bound, with the exp(40) shift factor explicit. -/
theorem proposition141_shifted_product_prime_global_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (hL : 2000≤lemma23PaperL D) (β : ℂ) (hβ : ‖β‖<5*lemma44PaperAlpha D) (t : ℝ) :
    ‖proposition141ShiftedProductPrimeSum χ θ β t‖≤Real.exp 40*lemma56PrimeMass D := by
  have hpwin := lemma56_paper_prime_weight_parameters hL
  unfold proposition141ShiftedProductPrimeSum
  apply (norm_sum_le _ _).trans
  calc
    (∑ p ∈ lemma56PaperPrimes D,
      ‖χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^(1+I*(t:ℂ)+β)‖)
        ≤ ∑ p ∈ lemma56PaperPrimes D, Real.exp 40*(p:ℝ) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpp,hpP,hpup⟩ := (lemma56_mem_paper_primes D p).mp hp
      have hp0 : (p:ℂ)≠0 := Nat.cast_ne_zero.mpr hpp.ne_zero
      have hpR : 0<(p:ℝ) := by exact_mod_cast hpp.pos
      have hpmax : (p:ℝ)≤2*lemma23PaperP D := by linarith [hpwin.2.2.2.1]
      have hb := proposition141_small_shift_power_norm hL hβ hpP.le hpmax
      have hc : ‖χ.chi (p:ZMod D)*conj (θ (p:ZMod N))‖≤1 := by
        rw [norm_mul,Complex.norm_conj]
        exact mul_le_one₀ (χ.chi.norm_le_one _) (norm_nonneg _) (θ.norm_le_one _)
      have hpow : ‖(p:ℂ)^(1+I*(t:ℂ))‖=(p:ℝ) := by
        rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hpR]
        simp
      rw [Complex.cpow_add _ _ hp0]
      simp only [norm_mul,hpow]
      have hh := mul_le_mul hc (mul_le_mul_of_nonneg_left hb hpR.le)
        (mul_nonneg hpR.le (norm_nonneg _)) (by norm_num : (0:ℝ)≤1)
      simpa only [norm_mul,Complex.ofReal_natCast,one_mul,mul_comm] using hh
    _ = Real.exp 40*lemma56PrimeMass D := by rw [← mul_sum]; rfl

noncomputable def proposition141ActualPrimeMellinIntegral {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N) (β : ℂ) : ℝ :=
  ∫ t : ℝ, ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖*
    ‖proposition141ShiftedProductPrimeSum χ θ β t‖

/-- The full actual δ-weighted prime integral. Both the exponential central
saving and the D⁻⁷ tail are retained before any outer divisor/character sum. -/
theorem proposition141_uniform_small_product_mellin_integral_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ {D N : ℕ} [NeZero N] (χ : RealPrimitiveCharacter D)
      (hd : D∣N) (θ : DirichletCharacter ℂ N),
      D₀≤D → NormalizedAssumptionA χ → (N:ℝ)≤lemma23PaperP D →
      θ≠1 → θ≠χ.chi.changeLevel hd → θ.conductor<D^3 →
      ∀ β : ℂ, ‖β‖<5*lemma44PaperAlpha D →
        proposition141ActualPrimeMellinIntegral χ θ β ≤
          C*lemma23PaperL D^7200*lemma56PrimeMass D*(lemma56Decay D+(D:ℝ)^(-(7:ℤ))) := by
  obtain ⟨Cc,hCc,Nc,hNc,hcentral⟩ := proposition141_uniform_small_shifted_product_prime_bound
  obtain ⟨Nr,hr⟩ := lemma56_uniform_repulsion_modulus_threshold
  let C := lemma54EighthMomentConstant*(Cc*Real.pi+256*Real.exp 40)
  have hC : 0<C := by
    dsimp [C]
    exact mul_pos lemma54_eighth_constants_pos.2.2.2 (by positivity)
  refine ⟨C,hC,max Nc Nr,hNc.trans (le_max_left _ _),?_⟩
  intro D N _ χ hd θ hDN hA hNP hθ hne hcond β hβ
  have hD2 : 2≤D := hNc.trans ((le_max_left Nc Nr).trans hDN)
  have hD : 1<D := by omega
  have hDR : 0<(D:ℝ) := by exact_mod_cast (by omega : 0<D)
  have hL := (hr D ((le_max_right Nc Nr).trans hDN)).1
  have hM := lemma56_prime_mass_nonneg D
  have hdec := (lemma56_decay_pos D).le
  have hcl : ∀t : ℝ, |t|≤(D:ℝ)/2 →
      ‖proposition141ShiftedProductPrimeSum χ θ β t‖≤Cc*lemma56PrimeMass D*lemma56Decay D := by
    intro t ht
    exact hcentral χ hd θ ((le_max_left Nc Nr).trans hDN) hA hNP hθ hne hcond β hβ t ht
  have hglobal := proposition141_shifted_product_prime_global_bound χ θ hL β hβ
  have hi := lemma54_eighth_actual_window_and_tail hD hL
    (proposition141ShiftedProductPrimeSum χ θ β)
    (proposition141_shifted_product_prime_continuous χ θ β)
    (mul_nonneg (Real.exp_nonneg _) hM)
    (mul_nonneg (mul_nonneg hCc.le hM) hdec) (show 0<(D:ℝ)/2 by positivity)
    hglobal hcl
  have htail : 2*(Real.exp 40*lemma56PrimeMass D)/((D:ℝ)/2)^7 =
      256*Real.exp 40*lemma56PrimeMass D*(D:ℝ)^(-(7:ℤ)) := by
    rw [zpow_neg,zpow_ofNat]
    field_simp
    ring
  rw [htail] at hi
  have hLp : 0≤lemma23PaperL D^7200 := by positivity
  have hK : 0≤lemma54EighthMomentConstant*lemma23PaperL D^7200 :=
    mul_nonneg lemma54_eighth_constants_pos.2.2.2.le hLp
  have hcross1 : 0≤Cc*Real.pi*((D:ℝ)^(-(7:ℤ))) := by positivity
  have hcross2 : 0≤256*Real.exp 40*lemma56Decay D := by positivity
  have hinside : Cc*lemma56PrimeMass D*lemma56Decay D*Real.pi +
      256*Real.exp 40*lemma56PrimeMass D*(D:ℝ)^(-(7:ℤ)) ≤
      (Cc*Real.pi+256*Real.exp 40)*lemma56PrimeMass D*(lemma56Decay D+(D:ℝ)^(-(7:ℤ))) := by
    nlinarith [mul_nonneg hM hcross1,mul_nonneg hM hcross2]
  have hh := mul_le_mul_of_nonneg_left hinside hK
  change proposition141ActualPrimeMellinIntegral χ θ β≤_ at hi
  apply hi.trans
  convert hh using 1 <;> dsimp [C] <;> ring

end ZhangLS.Spec
