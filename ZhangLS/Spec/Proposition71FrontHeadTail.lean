import ZhangLS.Spec.Proposition71FiniteCriticalMean
import ZhangLS.Spec.Proposition71FrontLargeTailRate
import Mathlib.NumberTheory.LSeries.Linearity

/-! # Exact strict long-head / infinite-tail decomposition on original J(1)

The head is literally m<P² and the tail is literally m≥P². Their actual
character-twisted Dirichlet series, finite-prefix representations and contour
integrals are related by proved convergence and finite-sum identities.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset Set
open scoped Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable def proposition71LongHead (D : ℕ) (c : ℕ → ℂ) (m : ℕ) : ℂ :=
  if (m : ℝ)<lemma23PaperP D^2 then c m else 0

noncomputable def proposition71LongTail (D : ℕ) (c : ℕ → ℂ) (m : ℕ) : ℂ :=
  if (m : ℝ)<lemma23PaperP D^2 then 0 else c m

lemma proposition71_long_head_tail (D : ℕ) (c : ℕ → ℂ) (m : ℕ) :
    c m=proposition71LongHead D c m+proposition71LongTail D c m := by
  unfold proposition71LongHead proposition71LongTail
  split_ifs <;> simp

lemma proposition71_long_head_majorant {D : ℕ} {B : ℝ} (hB : 0≤B)
    (c : ℕ → ℂ) (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ)) (m : ℕ) (hm : 0<m) :
    ‖proposition71LongHead D c m‖≤B*(lemma34Tau 5 m : ℝ) := by
  unfold proposition71LongHead
  split_ifs
  · exact hc m hm
  · simp only [norm_zero]; positivity

lemma proposition71_long_tail_majorant {D : ℕ} {B : ℝ} (hB : 0≤B)
    (c : ℕ → ℂ) (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ)) (m : ℕ) (hm : 0<m) :
    ‖proposition71LongTail D c m‖≤B*(lemma34Tau 5 m : ℝ) := by
  unfold proposition71LongTail
  split_ifs
  · simp only [norm_zero]; positivity
  · exact hc m hm

lemma proposition71_twisted_coefficient_majorant {p : ℕ} {B : ℝ}
    (c : ℕ → ℂ) (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ))
    (ψ : DirichletCharacter ℂ p) (m : ℕ) (hm : 0<m) :
    ‖c m*ψ (m : ZMod p)‖≤B*(lemma34Tau 5 m : ℝ) := by
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (ψ.norm_le_one _)).trans (hc m hm)

lemma proposition71_long_head_series_eq_finite {p : ℕ} (D : ℕ)
    (c : ℕ → ℂ) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    LSeries (fun m => proposition71LongHead D c m*ψ (m : ZMod p)) s=
      lemma81FiniteCharacterPolynomial ⌊lemma23PaperP D^2⌋₊ (proposition71LongHead D c) ψ s := by
  rw [lemma81_finite_character_polynomial_eq_cpow_sum]
  unfold LSeries
  have hfinite : (∑' m, LSeries.term (fun m => proposition71LongHead D c m*ψ (m : ZMod p)) s m)=
      ∑m∈Icc 1 ⌊lemma23PaperP D^2⌋₊, LSeries.term (fun m => proposition71LongHead D c m*ψ (m : ZMod p)) s m := by
    apply tsum_eq_sum
    intro m hm
    by_cases hm0 : m=0
    · subst m; simp
    have hmP : ¬(m : ℝ)<lemma23PaperP D^2 := by
      intro hh
      exact hm (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hm0,Nat.le_floor hh.le⟩)
    simp [LSeries.term_of_ne_zero hm0,proposition71LongHead,hmP]
  rw [hfinite]
  apply sum_congr rfl
  intro m hm
  rw [LSeries.term_of_ne_zero (Nat.ne_zero_of_lt (mem_Icc.mp hm).1)]

lemma proposition71_long_series_head_tail {D p : ℕ} {B : ℝ} (hB : 0≤B)
    (c : ℕ → ℂ) (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ))
    (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun m => c m*ψ (m : ZMod p)) s=
      lemma81FiniteCharacterPolynomial ⌊lemma23PaperP D^2⌋₊ (proposition71LongHead D c) ψ s+
        LSeries (fun m => proposition71LongTail D c m*ψ (m : ZMod p)) s := by
  have hh := proposition71_front_coefficient_summable hB _
    (proposition71_twisted_coefficient_majorant _ (proposition71_long_head_majorant (D := D) hB c hc) ψ) hs
  have ht := proposition71_front_coefficient_summable hB _
    (proposition71_twisted_coefficient_majorant _ (proposition71_long_tail_majorant (D := D) hB c hc) ψ) hs
  have he : (fun m => c m*ψ (m : ZMod p))=
      (fun m => proposition71LongHead D c m*ψ (m : ZMod p))+
        (fun m => proposition71LongTail D c m*ψ (m : ZMod p)) := by
    funext m
    rw [proposition71_long_head_tail D c m]
    simp only [Pi.add_apply,add_mul]
  rw [he,LSeries_add hh ht,proposition71_long_head_series_eq_finite]

noncomputable def proposition71InfiniteFrontKernel {N p : ℕ} [NeZero N]
    (D : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ p)
    (X : ℕ) (c a : ℕ → ℂ) (s : ℂ) : ℂ :=
  (lemma23DirichletZ θ s)⁻¹*LSeries (fun m => c m*ψ (m : ZMod p)) s*
    lemma81FiniteCharacterPolynomial X a ψ⁻¹ (1-s)*lemma81Omega D s

lemma proposition71_infinite_front_eq_actual_kernel {N p : ℕ} [NeZero N]
    (D : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ p)
    (X : ℕ) (c a : ℕ → ℂ) (s : ℂ) :
    proposition71InfiniteFrontKernel D θ ψ X c a s=
      proposition71FrontActualKernel D θ (fun m => c m*ψ (m : ZMod p)) (Icc 1 X)
        (fun n => a n*ψ⁻¹ (n : ZMod p)) s := by
  unfold proposition71InfiniteFrontKernel proposition71FrontActualKernel
  rw [lemma81_finite_character_polynomial_eq_cpow_sum]
  congr 2
  apply sum_congr rfl
  intro n hn
  rw [show 1-s=-(s-1) by ring,Complex.cpow_neg,div_inv_eq_mul]

lemma proposition71_infinite_front_head_tail {D N p : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ p)
    {B : ℝ} (hB : 0≤B) (X : ℕ) (c a : ℕ → ℂ)
    (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ)) {s : ℂ} (hs : 1<s.re) :
    proposition71InfiniteFrontKernel D θ ψ X c a s=
      proposition71FiniteFrontKernel D θ ψ ⌊lemma23PaperP D^2⌋₊ X (proposition71LongHead D c) a s+
        proposition71InfiniteFrontKernel D θ ψ X (proposition71LongTail D c) a s := by
  unfold proposition71InfiniteFrontKernel proposition71FiniteFrontKernel
  rw [proposition71_long_series_head_tail hB c hc ψ hs]
  ring

lemma proposition71_infinite_front_differentiableAt {D N p : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (ψ : DirichletCharacter ℂ p) {B : ℝ} (hB : 0≤B) (X : ℕ) (c a : ℕ → ℂ)
    (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ)) {s : ℂ}
    (hs : 1<s.re) (ht : 0<s.im) : DifferentiableAt ℂ (proposition71InfiniteFrontKernel D θ ψ X c a) s := by
  have hz := (lemma23DirichletZ_differentiableAt_of_im_ne_zero θ ht.ne').inv
    (lemma23DirichletZ_ne_zero_of_im_pos θ hθ hN ht)
  have hc' := (proposition71_front_lseries_analytic hB _ (proposition71_twisted_coefficient_majorant c hc ψ) hs).differentiableAt
  have ha := (lemma23FiniteDirichletPolynomial_analyticAt X (fun n => a n*ψ⁻¹ (n : ZMod p)) (1-s)).differentiableAt.comp s
    (show DifferentiableAt ℂ (fun z : ℂ => 1-z) s by fun_prop)
  exact ((hz.mul hc').mul ha).mul ((lemma81_omega_differentiable D) s)

lemma proposition71_infinite_front_segment_integrable {D N p : ℕ} [NeZero N]
    (hL : 3≤lemma23PaperL D) (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (ψ : DirichletCharacter ℂ p) {B : ℝ} (hB : 0≤B) (X : ℕ) (c a : ℕ → ℂ)
    (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ)) :
    IntervalIntegrable (fun t => proposition71InfiniteFrontKernel D θ ψ X c a
      (lemma81SegmentPoint D 1 t)) volume (-(lemma23PaperL D^405)) (lemma23PaperL D^405) := by
  have hLp : 0< lemma23PaperL D := by linarith
  have hH : 0≤lemma23PaperL D^405 := pow_nonneg hLp.le _
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le (neg_le_self hH)] at ht
  have him : |(lemma81SegmentPoint D 1 t).im-(lemma23PaperCenter D).im|≤2*lemma23PaperL D^405+3 := by
    have he : (lemma81SegmentPoint D 1 t).im-(lemma23PaperCenter D).im=t := by simp [lemma81SegmentPoint]
    rw [he]
    have hh : |t|≤lemma23PaperL D^405 := abs_le.mpr ht
    linarith
  have hpos : 0<(lemma81SegmentPoint D 1 t).im := by linarith only [(lemma61_wide_height_data hL him).2.1]
  have hre : 1<(lemma81SegmentPoint D 1 t).re := by norm_num [lemma81SegmentPoint,lemma23PaperCenter]
  have hc' : ContinuousAt (fun t : ℝ => lemma81SegmentPoint D 1 t) t := by unfold lemma81SegmentPoint; fun_prop
  exact ((proposition71_infinite_front_differentiableAt θ hθ hN ψ hB X c a hc hre hpos).continuousAt.comp hc').continuousWithinAt

/-- The strict head and closed infinite tail add to the original contour
integral, with all three actual integrals proved integrable. -/
theorem proposition71_infinite_contour_head_tail {D N p : ℕ} [NeZero N]
    (hL : 3≤lemma23PaperL D) (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (ψ : DirichletCharacter ℂ p) {B : ℝ} (hB : 0≤B) (X : ℕ) (c a : ℕ → ℂ)
    (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ)) :
    lemma81NormalizedSegmentIntegral D 1 (proposition71InfiniteFrontKernel D θ ψ X c a)=
      lemma81NormalizedSegmentIntegral D 1
        (proposition71FiniteFrontKernel D θ ψ ⌊lemma23PaperP D^2⌋₊ X (proposition71LongHead D c) a)+
      lemma81NormalizedSegmentIntegral D 1 (proposition71InfiniteFrontKernel D θ ψ X (proposition71LongTail D c) a) := by
  have hp (t : ℝ) := proposition71_infinite_front_head_tail (D := D) θ ψ hB X c a hc
    (s := lemma81SegmentPoint D 1 t) (by norm_num [lemma81SegmentPoint,lemma23PaperCenter])
  have hh := proposition71_finite_front_segment_integrable hL θ hθ hN ψ ⌊lemma23PaperP D^2⌋₊ X (proposition71LongHead D c) a 1 1
  simp only [one_mul] at hh
  have ht := proposition71_infinite_front_segment_integrable hL θ hθ hN ψ hB X (proposition71LongTail D c) a
    (proposition71_long_tail_majorant (D := D) hB c hc)
  unfold lemma81NormalizedSegmentIntegral
  simp_rw [hp]
  rw [intervalIntegral.integral_add hh ht,mul_add]

end ZhangLS.Spec
