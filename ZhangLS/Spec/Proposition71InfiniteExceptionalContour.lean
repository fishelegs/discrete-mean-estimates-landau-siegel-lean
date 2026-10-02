import ZhangLS.Spec.Proposition71FiniteExceptionalContour
import ZhangLS.Spec.Proposition71FrontHeadTail

/-! # The actual infinite-long exceptional-family contour step

The finite critical-line mean, genuine J(1) shift and literal infinite Δ₁ tail
are now attached. The only extra scale hypothesis is the actual short-support
inequality qn·t₀^(51/50)<P², to be instantiated from each original support.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

lemma proposition71_front_conductor_log_bound {D N : ℕ} [NeZero N]
    (hL : 3≤lemma23PaperL D) (hN : (N : ℝ)≤2*lemma23PaperP D^2) :
    Real.log (N : ℝ)≤3*lemma23PaperL D^9 := by
  have hNp : 0<(N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hh := Real.log_le_log hNp hN
  rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) (pow_ne_zero 2 hP.ne'),Real.log_pow,lemma23PaperP,Real.log_exp] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  nlinarith only [hh,hlog2,one_le_pow₀ (n := 9) (by linarith : 1≤lemma23PaperL D)]

/-- A proved common version of the original Ψ₂ step, not an averaged premise:
all contour, finite-series and infinite-tail transformations are attached. -/
theorem proposition71_infinite_exceptional_contour_little_o
    (Bc Ba W : ℝ) (hBc : 0<Bc) (hBa : 0<Ba) (hW : 0<W)
    (ε : ℝ) (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ (N : lemma33CharacterIndex D → ℕ) [∀ψ, NeZero (N ψ)]
        (θ : (ψ : lemma33CharacterIndex D) → DirichletCharacter ℂ (N ψ)),
      (∀ψ∈proposition21ActualPsi2Family χ, (θ ψ).IsPrimitive) →
      (∀ψ∈proposition21ActualPsi2Family χ, N ψ≠1) →
      (∀ψ∈proposition21ActualPsi2Family χ, (N ψ : ℝ)≤2*lemma23PaperP D^2) →
      ∀ (X : ℕ), X≤⌊lemma23PaperP D⌋₊ →
      (∀ψ∈proposition21ActualPsi2Family χ, ∀n∈Icc 1 X,
        ((N ψ : ℝ)*(n : ℝ))*lemma51PaperT0 D^(51/50 : ℝ)<lemma23PaperP D^2) →
      ∀ c a : ℕ → ℂ, (∀m, 0<m → ‖c m‖≤Bc*(lemma34Tau 5 m : ℝ)) →
      (∀n∈Icc 1 X, ‖a n‖≤Ba) →
      ∀ w : lemma33CharacterIndex D → ℂ, (∀ψ∈proposition21ActualPsi2Family χ, ‖w ψ‖≤W) →
      ‖∑ψ∈proposition21ActualPsi2Family χ, w ψ*lemma81NormalizedSegmentIntegral D 1
        (proposition71InfiniteFrontKernel D (θ ψ) ψ.2 X c a)‖≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨Nf,hNf,hfinite⟩ := proposition71_finite_exceptional_contour_little_o Bc Ba W hBc hBa hW
    (ε/2) (by positivity)
  let K := W*(proposition71FrontErrorConstant+proposition71FrontLargeTailConstant)*Bc*Ba
  have hK : 0<K := by
    dsimp [K]
    exact mul_pos (mul_pos (mul_pos hW (add_pos proposition71_front_error_constant_pos
      proposition71_front_large_tail_constant_pos)) hBc) hBa
  obtain ⟨Nl,hNl⟩ := exists_nat_gt (Real.exp 20000)
  obtain ⟨Nr,hNr⟩ := exists_nat_gt (2*K/ε)
  refine ⟨max Nf (max Nl Nr),hNf.trans (le_max_left _ _),?_⟩
  intro D hD χ hA N _ θ hθ hN hNP X hX hgap c a hc ha w hw
  have hDf := (le_max_left _ _).trans hD
  have hDl := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDr := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hD2 : 2≤D := hNf.trans hDf
  have hDpos : 1<D := by omega
  have hDp : 0<(D : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hDpos
  have hL : 20000≤lemma23PaperL D := by
    have hh : Real.exp 20000≤(D : ℝ) := hNl.le.trans (by exact_mod_cast hDl)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 20000) hh
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hrate : K/(D : ℝ)≤ε/2 := by
    have hh : 2*K/ε≤(D : ℝ) := hNr.le.trans (by exact_mod_cast hDr)
    have hh' := (div_le_iff₀ hε).mp hh
    apply (div_le_iff₀ hDp).mpr
    nlinarith
  let E := proposition21ActualPsi2Family χ
  let F := fun ψ : lemma33CharacterIndex D =>
    lemma81NormalizedSegmentIntegral D 1 (proposition71FiniteFrontKernel D (θ ψ) ψ.2
      ⌊lemma23PaperP D^2⌋₊ X (proposition71LongHead D c) a)
  let T := fun ψ : lemma33CharacterIndex D =>
    lemma81NormalizedSegmentIntegral D 1 (proposition71InfiniteFrontKernel D (θ ψ) ψ.2 X (proposition71LongTail D c) a)
  have hlog (ψ : lemma33CharacterIndex D) (hψ : ψ∈E) :
      Real.log (N ψ : ℝ)≤3*lemma23PaperL D^9 := proposition71_front_conductor_log_bound hL3 (hNP ψ hψ)
  have hhead : ‖∑ψ∈E, w ψ*F ψ‖≤(ε/2)*lemma33ActualPrimeMass D :=
    hfinite D hDf χ hA N θ hθ hN hlog X hX (proposition71LongHead D c) a
      (fun n hn => proposition71_long_head_majorant hBc.le c hc n (mem_Icc.mp hn).1) ha w hw
  have hcard : (E.card : ℝ)≤lemma33ActualPrimeMass D := by
    have hs : E⊆lemma33ActualFamily D := filter_subset _ _
    exact (by exact_mod_cast card_le_card hs : (E.card : ℝ)≤(lemma33ActualFamily D).card).trans
      (proposition71_actual_family_card_le_mass hL3)
  have hS (n : ℕ) (hn : n∈Icc 1 X) : 0<n ∧ (n : ℝ)≤lemma23PaperP D :=
    ⟨(mem_Icc.mp hn).1,(by exact_mod_cast ((mem_Icc.mp hn).2.trans hX) : (n : ℝ)≤⌊lemma23PaperP D⌋₊).trans
      (Nat.floor_le (Real.exp_pos _).le)⟩
  have htail (ψ : lemma33CharacterIndex D) (hψ : ψ∈E) :
      ‖T ψ‖≤(proposition71FrontErrorConstant+proposition71FrontLargeTailConstant)*Bc*Ba/(D : ℝ) := by
    have hcoeff := proposition71_twisted_coefficient_majorant (proposition71LongTail D c)
      (proposition71_long_tail_majorant hBc.le c hc) ψ.2
    have hz : ∀m : ℕ, (m : ℝ)<lemma23PaperP D^2 →
        proposition71LongTail D c m*ψ.2 (m : ZMod ψ.1.val)=0 := by
      intro m hm
      simp [proposition71LongTail,hm]
    have has (n : ℕ) (hn : n∈Icc 1 X) : ‖a n*ψ.2⁻¹ (n : ZMod ψ.1.val)‖≤Ba := by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (ψ.2⁻¹.norm_le_one _)).trans (ha n hn)
    have he : proposition71InfiniteFrontKernel D (θ ψ) ψ.2 X (proposition71LongTail D c) a=
        proposition71FrontActualKernel D (θ ψ)
          (fun m => proposition71LongTail D c m*ψ.2 (m : ZMod ψ.1.val)) (Icc 1 X)
          (fun n => a n*ψ.2⁻¹ (n : ZMod ψ.1.val)) :=
      funext (proposition71_infinite_front_eq_actual_kernel D (θ ψ) ψ.2 X (proposition71LongTail D c) a)
    dsimp [T]
    rw [he]
    exact proposition71_front_large_tail_contour_rate hDpos hL (hNP ψ hψ) (θ ψ) (hθ ψ hψ) (hN ψ hψ)
      hBc.le hBa.le _ hcoeff hz _ hS _ has (hgap ψ hψ)
  have htailmean : ‖∑ψ∈E, w ψ*T ψ‖≤(ε/2)*lemma33ActualPrimeMass D := by
    calc
      _≤∑ψ∈E, ‖w ψ*T ψ‖ := norm_sum_le _ _
      _≤∑_ψ∈E, K/(D : ℝ) := by
        apply sum_le_sum
        intro ψ hψ
        rw [norm_mul]
        exact (mul_le_mul (hw ψ hψ) (htail ψ hψ) (norm_nonneg _) hW.le).trans_eq (by dsimp [K]; ring)
      _=(K/(D : ℝ))*(E.card : ℝ) := by simp [mul_comm]
      _≤(ε/2)*(E.card : ℝ) := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg _)
      _≤_ := mul_le_mul_of_nonneg_left hcard (by positivity)
  have he : (∑ψ∈E, w ψ*lemma81NormalizedSegmentIntegral D 1
        (proposition71InfiniteFrontKernel D (θ ψ) ψ.2 X c a))=
      (∑ψ∈E, w ψ*F ψ)+(∑ψ∈E, w ψ*T ψ) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro ψ hψ
    rw [proposition71_infinite_contour_head_tail hL3 (θ ψ) (hθ ψ hψ) (hN ψ hψ) ψ.2 hBc.le X c a hc,mul_add]
  change ‖∑ψ∈E, w ψ*lemma81NormalizedSegmentIntegral D 1 (proposition71InfiniteFrontKernel D (θ ψ) ψ.2 X c a)‖≤_
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hhead htailmean).trans_eq (by ring))

end ZhangLS.Spec
