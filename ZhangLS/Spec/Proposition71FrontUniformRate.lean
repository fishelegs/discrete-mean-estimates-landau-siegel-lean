import ZhangLS.Spec.Proposition71OriginalFrontTransform

/-! # An explicit uniform reciprocal-Z to Δ₁ rate

The actual conductor may be as large as 2P², covering both q=p and q=Dp.
Every short coefficient and the genuine τ₅ Dirichlet mass are paid for.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

lemma proposition71_front_kernel_polynomial {D : ℕ} (hL : 1≤lemma23PaperL D) :
    (128*Real.exp 1)*(1+(lemma23PaperCenter D).im^2)*(1+32*lemma53PaperScale D^2)≤
      (128*Real.exp 1*(1+4*Real.pi^2)*33)*lemma23PaperL D^1838 := by
  have hT : 1+(lemma23PaperCenter D).im^2≤(1+4*Real.pi^2)*lemma23PaperL D^1038 := by
    calc
      _=1+4*Real.pi^2*lemma23PaperL D^1038 := by simp only [lemma23PaperCenter]; ring
      _≤lemma23PaperL D^1038+4*Real.pi^2*lemma23PaperL D^1038 :=
        add_le_add (one_le_pow₀ hL) le_rfl
      _=_ := by ring
  have hB : 1+32*lemma53PaperScale D^2≤33*lemma23PaperL D^800 := by
    calc
      _=1+32*lemma23PaperL D^800 := by unfold lemma53PaperScale; ring
      _≤lemma23PaperL D^800+32*lemma23PaperL D^800 := add_le_add (one_le_pow₀ hL) le_rfl
      _=_ := by ring
  calc
    _≤(128*Real.exp 1)*((1+4*Real.pi^2)*lemma23PaperL D^1038)*(33*lemma23PaperL D^800) := by gcongr
    _=_ := by ring

lemma proposition71_front_scalar_budget {D : ℕ} (hD : 1<D)
    (hL : 20000≤lemma23PaperL D) :
    lemma23PaperP D^4*lemma23PaperL D^1838*Real.exp (-lemma23PaperL D^10/8)≤(D : ℝ)⁻¹ := by
  let L := lemma23PaperL D
  have hLp : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have hDp : 0<(D : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hL9 : L≤L^9 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1≤(9:ℕ))
  have hlarge : 14744*L^9≤L^10 := by
    have hh := mul_le_mul_of_nonneg_left (show 14744≤L by dsimp [L]; linarith) (pow_nonneg hLp.le 9)
    convert hh using 1 <;> ring
  have hex : 4*L^9+1838*L-L^10/8≤-L := by nlinarith only [hlarge,hL9]
  have hpoly : L^1838≤Real.exp (1838*L) := by
    have hh : L≤Real.exp L := by linarith [Real.add_one_le_exp L]
    have he := pow_le_pow_left₀ hLp.le hh 1838
    rw [←Real.exp_nat_mul] at he
    norm_num only [Nat.cast_ofNat] at he
    exact he
  calc
    _=Real.exp (4*L^9)*L^1838*Real.exp (-L^10/8) := by
      dsimp [L]
      rw [lemma23PaperP,←Real.exp_nat_mul]
      norm_num
    _≤Real.exp (4*L^9)*Real.exp (1838*L)*Real.exp (-L^10/8) := by gcongr
    _=Real.exp (4*L^9+1838*L-L^10/8) := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
    _≤Real.exp (-L) := Real.exp_le_exp.mpr hex
    _=_ := by dsimp [L,lemma23PaperL]; rw [Real.exp_neg,Real.exp_log hDp]

noncomputable def proposition71FrontErrorConstant : ℝ :=
  2*(128*Real.exp 1*(1+4*Real.pi^2)*33)*proposition71TauFiveThreeHalvesMass

lemma proposition71_front_error_constant_pos : 0<proposition71FrontErrorConstant := by
  unfold proposition71FrontErrorConstant
  exact mul_pos (by positivity) proposition71_tau_three_halves_mass_pos

/-- Uniform in both coefficient sequences and the actual primitive character,
with no dependence of the constant on D, N, or the chosen finite support. -/
theorem proposition71_front_transform_uniform_rate {D N : ℕ} [NeZero N]
    (hD : 1<D) (hL : 20000≤lemma23PaperL D)
    (hNP : (N : ℝ)≤2*lemma23PaperP D^2)
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    {Bc Ba : ℝ} (hBc : 0≤Bc) (hBa : 0≤Ba)
    (c : ℕ → ℂ) (hc : ∀n, 0<n → ‖c n‖≤Bc*(lemma34Tau 5 n : ℝ))
    (S : Finset ℕ) (hS : ∀n∈S, 0<n ∧ (n : ℝ)≤lemma23PaperP D)
    (a : ℕ → ℂ) (ha : ∀n∈S, ‖a n‖≤Ba) :
    Summable (proposition71DeltaOneDoubleTerm D c S a (N : ℝ)) ∧
      ‖proposition71FrontSegmentIntegral D θ c S a-
        (gaussSum θ⁻¹ ZMod.stdAddChar/(N : ℂ))*
          (∑' m, proposition71DeltaOneDoubleTerm D c S a (N : ℝ) m)‖≤
      proposition71FrontErrorConstant*Bc*Ba/(D : ℝ) := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hP : 1≤lemma23PaperP D := by
    unfold lemma23PaperP
    exact Real.one_le_exp (pow_nonneg (by linarith : 0≤lemma23PaperL D) _)
  have hM := proposition71_tau_three_halves_mass_pos.le
  have hshort := proposition71_short_coefficient_mass_bound hP hBa S hS a ha
  have hshort0 := proposition71_short_coefficient_mass_nonneg S a
  have hcoef : (N : ℝ)*Bc*proposition71TauFiveThreeHalvesMass*proposition71ShortCoefficientMass S a≤
      (2*lemma23PaperP D^2)*Bc*proposition71TauFiveThreeHalvesMass*(Ba*lemma23PaperP D^2) := by gcongr
  have hcoef0 : 0≤(N : ℝ)*Bc*proposition71TauFiveThreeHalvesMass*proposition71ShortCoefficientMass S a := by positivity
  have hfront := proposition71_original_front_transform hD (by linarith) θ hθ hN hBc c hc S
    (fun n hn => (hS n hn).1) a
  refine ⟨hfront.1,hfront.2.trans ?_⟩
  calc
    _≤((128*Real.exp 1*(1+4*Real.pi^2)*33)*lemma23PaperL D^1838)*
        ((2*lemma23PaperP D^2)*Bc*proposition71TauFiveThreeHalvesMass*(Ba*lemma23PaperP D^2))*
        Real.exp (-lemma23PaperL D^10/8) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (proposition71_front_kernel_polynomial hL1) hcoef hcoef0 (by positivity))
        (Real.exp_pos _).le
    _=(proposition71FrontErrorConstant*Bc*Ba)*
        (lemma23PaperP D^4*lemma23PaperL D^1838*Real.exp (-lemma23PaperL D^10/8)) := by
      unfold proposition71FrontErrorConstant
      ring
    _≤(proposition71FrontErrorConstant*Bc*Ba)*(D : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (proposition71_front_scalar_budget hD hL)
        (mul_nonneg (mul_nonneg proposition71_front_error_constant_pos.le hBc) hBa)
    _=_ := by rw [div_eq_mul_inv]

end ZhangLS.Spec
