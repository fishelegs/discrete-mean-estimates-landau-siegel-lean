import ZhangLS.Spec.Proposition141SmallConductor
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Complex shifts: actual Abel weight

A general complex β cannot be passed through cancellation by taking its norm.
Its imaginary part shifts the prime frequency; its real part is retained in
an explicitly monotone Abel weight. The existing sharp prime-log prefix
estimates can therefore be used, rather than assuming a shifted 5.6.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Real

noncomputable def proposition141ShiftedPrimeSum {q : ℕ} (D : ℕ)
    (θ : DirichletCharacter ℂ q) (β : ℂ) (τ : ℝ) : ℂ :=
  ∑ p ∈ lemma56PaperPrimes D, θ (p : ZMod q) *
    (p : ℂ) ^ (1 + I * (τ : ℂ) + β)

/-- Exact decomposition into the real Abel weight and shifted real frequency. -/
theorem proposition141_shifted_prime_weight_identity {q p : ℕ}
    (θ : DirichletCharacter ℂ q) (hp : p.Prime) (β : ℂ) (τ : ℝ) :
    θ (p : ZMod q) * (p : ℂ) ^ (1 + I*(τ : ℂ) + β) =
      ((p : ℝ)^(1+β.re) / Real.log (p : ℝ)) •
        ((p : ℂ)^(((τ+β.im : ℝ) : ℂ)*I) *
          (θ (p : ZMod q) * (Real.log (p : ℝ) : ℂ))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpR : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hlog : (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hexp : (1 + I*(τ : ℂ) + β) = ((1+β.re : ℝ) : ℂ) +
      ((τ+β.im : ℝ) : ℂ)*I := by
    apply Complex.ext <;> simp
  rw [hexp,Complex.cpow_add _ _ hp0,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_cpow hpR,Complex.ofReal_natCast]
  field_simp

/-- Genuine monotonicity of x^a/log x in the whole range needed here,
including a<1 arising from negative Re β. -/
theorem proposition141_real_shift_weight_mono {x y a : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hlog : 2 ≤ Real.log x) (ha : 1/2 ≤ a) :
    x^a / Real.log x ≤ y^a / Real.log y := by
  let f : ℝ → ℝ := fun z => z^a / Real.log z
  let f' : ℝ → ℝ := fun z => z^(a-1)*(a*Real.log z-1)/(Real.log z)^2
  have hzpos (z : ℝ) (hz : z ∈ Set.Ici x) : 0 < z := hx.trans_le hz
  have hzlog (z : ℝ) (hz : z ∈ Set.Ici x) : 2 ≤ Real.log z :=
    hlog.trans (Real.log_le_log hx hz)
  have hder (z : ℝ) (hz : z ∈ Set.Ici x) : HasDerivAt f (f' z) z := by
    have hzp := hzpos z hz
    have hzl : Real.log z ≠ 0 := by linarith [hzlog z hz]
    have hh := (Real.hasDerivAt_rpow_const (p := a) (Or.inl hzp.ne')).div
      (Real.hasDerivAt_log hzp.ne') hzl
    convert hh using 1
    dsimp [f']
    rw [Real.rpow_sub_one hzp.ne']
    field_simp
  have hmono : MonotoneOn f (Set.Ici x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici x)
    · intro z hz
      exact (hder z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hder z (interior_subset hz)).hasDerivWithinAt
    · intro z hz
      have hzl := hzlog z (interior_subset hz)
      have hz0 := hzpos z (interior_subset hz)
      have hmul : 0 ≤ a*Real.log z - 1 := by nlinarith
      dsimp [f']
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg hz0.le _) hmul) (sq_nonneg _)
  exact hmono (by simp) hxy hxy

/-- A small complex β is handled without discarding cancellation: this
finite Abel theorem retains its real exponent in the monotone weight. -/
theorem proposition141_shifted_finite_prime_budget {q m n : ℕ}
    (θ : DirichletCharacter ℂ q) (β : ℂ) (τ : ℝ) {A W : ℝ}
    (hmn : m < n) (hm : 0 < m) (hmLog : 2 ≤ Real.log (m : ℝ))
    (hβ : -(1/2 : ℝ) ≤ β.re) (hA : 0 ≤ A)
    (hc : ∀ k : ℕ, m ≤ k → k ≤ n →
      ‖lemma56SharpPrimeLogSum θ k (τ+β.im)‖ ≤ A)
    (hweight : ((n-1 : ℕ) : ℝ)^(1+β.re) / Real.log ((n-1 : ℕ) : ℝ) ≤ W) :
    ‖∑ k ∈ Ico m n, if k.Prime then θ (k : ZMod q) *
      (k : ℂ) ^ (1 + I*(τ : ℂ) + β) else 0‖ ≤ 2*A*W := by
  let w : ℕ → ℝ := fun k => (k : ℝ)^(1+β.re)/Real.log (k : ℝ)
  let c : ℕ → ℂ := fun k => if k.Prime then
    (k : ℂ)^(((τ+β.im : ℝ) : ℂ)*I) *
      (θ (k : ZMod q) * (Real.log (k : ℝ) : ℂ)) else 0
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmono : MonotoneOn w (Set.Icc m (n-1)) := by
    intro a ha b hb hab
    have hma : (m : ℝ) ≤ a := by exact_mod_cast ha.1
    apply proposition141_real_shift_weight_mono (hmR.trans_le hma) (by exact_mod_cast hab)
    · exact hmLog.trans (Real.log_le_log hmR hma)
    · linarith
  have hmw : 0 ≤ w m := by
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by linarith)
  have hc_range : ∀ k : ℕ, m ≤ k → k ≤ n → ‖∑ j ∈ range k, c j‖ ≤ A := by
    intro k hmk hkn
    simpa only [lemma56SharpPrimeLogSum,Nat.ceil_natCast] using hc k hmk hkn
  have he : (∑ k ∈ Ico m n, if k.Prime then θ (k : ZMod q) *
      (k : ℂ) ^ (1 + I*(τ : ℂ) + β) else 0) = ∑ k ∈ Ico m n, w k • c k := by
    apply sum_congr rfl
    intro k hk
    by_cases hp : k.Prime
    · simp only [hp,if_true,w,c]
      exact proposition141_shifted_prime_weight_identity θ hp β τ
    · simp [hp,c]
  rw [he]
  exact (lemma56_finite_abel_positive_budget hmn w c hmono hmw hc_range).trans
    (mul_le_mul_of_nonneg_left hweight (by positivity))

/-- Quantitative shift bounds derived from the actual |β|<5α disk. -/
theorem proposition141_complex_shift_parameters {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {β : ℂ} (hβ : ‖β‖ < 5*lemma44PaperAlpha D) :
    2 ≤ Real.log (lemma23PaperP D) ∧ ‖β‖ < 1/2 ∧
      |β.re| * Real.log (lemma23PaperP D) ≤ 20 := by
  have hL2 : (2:ℝ) ≤ lemma23PaperL D := by linarith
  have hlog : 512 ≤ Real.log (lemma23PaperP D) := by
    rw [lemma23PaperP,Real.log_exp]
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hL2 9
    norm_num at hh
    exact hh
  have hlogp : 0 < Real.log (lemma23PaperP D) := by linarith
  have hn : ‖β‖ < (5*Real.pi)/Real.log (lemma23PaperP D) := by
    convert hβ using 1 <;> simp only [lemma44PaperAlpha] <;> ring
  have hm := (lt_div_iff₀ hlogp).mp hn
  have hpi := Real.pi_le_four
  have hnorm := norm_nonneg β
  have hre := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm β) hlogp.le
  refine ⟨by linarith,?_,?_⟩
  · nlinarith
  · nlinarith

/-- Uniform endpoint bound for the real Abel weight. The fixed exp(40)
factor is carried explicitly and is independent of D and β. -/
theorem proposition141_complex_shift_weight_bound {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {β : ℂ} (hβ : ‖β‖ < 5*lemma44PaperAlpha D) {x : ℝ}
    (hxP : lemma23PaperP D ≤ x) (hxhi : x ≤ 2*lemma23PaperP D) :
    x^(1+β.re)/Real.log x ≤ 2*Real.exp 40*lemma23PaperP D := by
  have hp := proposition141_complex_shift_parameters hL hβ
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hx : 0 < x := hP.trans_le hxP
  have hloglo : 2 ≤ Real.log x := hp.1.trans (Real.log_le_log hP hxP)
  have hloghi : Real.log x ≤ 2*Real.log (lemma23PaperP D) := by
    have hh := Real.log_le_log hx hxhi
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hP.ne'] at hh
    have hlog2 : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hexp : Real.log x*β.re ≤ 40 := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self β.re) (by linarith : 0≤Real.log x)
    have h2 := mul_le_mul_of_nonneg_left hloghi (abs_nonneg β.re)
    nlinarith [hp.2.2]
  have hpow : x^(1+β.re) ≤ x*Real.exp 40 := by
    rw [Real.rpow_add hx,Real.rpow_one,Real.rpow_def_of_pos hx]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hx.le
  have hdiv : x^(1+β.re)/Real.log x ≤ x^(1+β.re) := by
    apply (div_le_iff₀ (by linarith : 0<Real.log x)).mpr
    have hh := mul_le_mul_of_nonneg_left (show (1:ℝ)≤Real.log x by linarith)
      (Real.rpow_nonneg hx.le (1+β.re))
    simpa only [mul_one] using hh
  exact hdiv.trans (hpow.trans (by nlinarith [Real.exp_pos (40:ℝ)]))

/-- The strict original prime window, for any actual summand. -/
theorem proposition141_prime_window_sum_eq (D : ℕ) (f : ℕ → ℂ) :
    (∑ p ∈ lemma56PaperPrimes D, f p) =
      ∑ n ∈ Ico (⌊lemma23PaperP D⌋₊+1) ⌈lemma56PrimeUpper D⌉₊,
        if n.Prime then f n else 0 := by
  have hP : 0 ≤ lemma23PaperP D := (Real.exp_pos _).le
  unfold lemma56PaperPrimes
  rw [sum_filter]
  have hsub : Ico (⌊lemma23PaperP D⌋₊+1) ⌈lemma56PrimeUpper D⌉₊ ⊆
      range ⌈lemma56PrimeUpper D⌉₊ := by
    intro n hn
    exact mem_range.mpr (mem_Ico.mp hn).2
  rw [← sum_subset hsub]
  · apply sum_congr rfl
    intro n hn
    have hh := mem_Ico.mp hn
    have hlo : lemma23PaperP D < (n:ℝ) := (Nat.floor_lt hP).mp (by omega)
    have hhi : (n:ℝ) < lemma56PrimeUpper D := Nat.lt_ceil.mp hh.2
    simp only [hlo,hhi,and_true]
  · intro n hn hnnot
    by_cases hw : n.Prime ∧ lemma23PaperP D < (n:ℝ) ∧ (n:ℝ) < lemma56PrimeUpper D
    · exfalso
      apply hnnot
      have hlo := (Nat.floor_lt hP).mpr hw.2.1
      exact mem_Ico.mpr ⟨by omega,Nat.lt_ceil.mpr hw.2.2⟩
    · exact if_neg hw

/-- Genuine Abel conversion of the full complex-shifted prime window. -/
theorem proposition141_actual_shifted_prime_weight_budget {D q : ℕ}
    (θ : DirichletCharacter ℂ q) (hL : 2000 ≤ lemma23PaperL D)
    (β : ℂ) (hβ : ‖β‖ < 5*lemma44PaperAlpha D) (τ : ℝ) {A : ℝ} (hA : 0≤A)
    (hc : ∀ {x : ℝ}, 1≤x → x≤2*lemma23PaperP D →
      ‖lemma56SharpPrimeLogSum θ x (τ+β.im)‖ ≤ A) :
    ‖proposition141ShiftedPrimeSum D θ β τ‖ ≤ 4*Real.exp 40*A*lemma23PaperP D := by
  let m := ⌊lemma23PaperP D⌋₊+1
  let n := ⌈lemma56PrimeUpper D⌉₊
  have hp := lemma56_paper_prime_weight_parameters hL
  have hβp := proposition141_complex_shift_parameters hL hβ
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hmP : lemma23PaperP D < (m:ℝ) := by
    dsimp [m]
    rw [Nat.cast_add,Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hm : 0<m := by dsimp [m]; omega
  have hmLog : 2 ≤ Real.log (m:ℝ) := hβp.1.trans (Real.log_le_log hP hmP.le)
  have hnmax : (n:ℝ) ≤ 2*lemma23PaperP D := hp.2.2.2.2
  have hb : -(1/2:ℝ) ≤ β.re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm β)).1
    linarith [hβp.2.1]
  unfold proposition141ShiftedPrimeSum
  rw [proposition141_prime_window_sum_eq]
  change ‖∑ k ∈ Ico m n, if k.Prime then θ (k:ZMod q)*
    (k:ℂ)^(1+I*(τ:ℂ)+β) else 0‖ ≤ _
  by_cases hmn : m<n
  · have hc' : ∀ k : ℕ, m≤k → k≤n →
        ‖lemma56SharpPrimeLogSum θ k (τ+β.im)‖ ≤ A := by
      intro k hmk hkn
      exact hc (by exact_mod_cast (by omega : 1≤k))
        ((by exact_mod_cast hkn : (k:ℝ)≤n).trans hnmax)
    have htop : m≤n-1 := by omega
    have htlo : lemma23PaperP D ≤ ((n-1:ℕ):ℝ) :=
      hmP.le.trans (by exact_mod_cast htop)
    have hthi : ((n-1:ℕ):ℝ) ≤ 2*lemma23PaperP D :=
      (by exact_mod_cast Nat.sub_le n 1 : ((n-1:ℕ):ℝ)≤n).trans hnmax
    have hh := proposition141_shifted_finite_prime_budget θ β τ hmn hm hmLog hb hA hc'
      (proposition141_complex_shift_weight_bound hL hβ htlo hthi)
    convert hh using 1 <;> ring
  · rw [Ico_eq_empty_of_le (by omega),sum_empty,norm_zero]
    positivity

/-- The D/2 central Mellin range leaves honest room for Im β. The remaining
Mellin tail is intentionally not part of this algebraic height lemma. -/
theorem proposition141_shifted_height_margin {D : ℕ} (hD : 2≤D)
    {β : ℂ} (hβ : ‖β‖ ≤ 1) {τ : ℝ} (hτ : |τ|≤(D:ℝ)/2) : |τ+β.im|≤D := by
  have him := (Complex.abs_im_le_norm β).trans hβ
  have hDp : (2:ℝ)≤D := by exact_mod_cast hD
  exact (abs_add_le τ β.im).trans (by linarith)

end ZhangLS.Spec
