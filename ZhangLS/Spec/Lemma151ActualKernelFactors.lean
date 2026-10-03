import ZhangLS.Spec.AppendixBTailH14Assembly
import ZhangLS.Spec.AppendixBRoughKernelReplacement
import ZhangLS.Spec.Lemma151ActualFiniteSupport

/-! Actual U,V rough factors, with the strict H14 endpoint and finite-D shifts.
No arithmetic remainder is accepted as a hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex Filter
open scoped Classical ComplexConjugate

noncomputable def actual151FirstConstant (j : ℕ) : ℂ :=
  appendixBH14TerminalConstant j +
    lemma151Iota2*lemma151FullKernelConstant 0.5 (5/2) j
noncomputable def actual151SecondConstant (j : ℕ) : ℂ :=
  conj lemma151Iota3*lemma151FullKernelConstant 0.498 (3/2) j+
    conj lemma151Iota4*lemma151FullKernelConstant 0.5 (5/2) j
noncomputable def actual151MainConstant (j : ℕ) : ℂ :=
  actual151FirstConstant j*actual151SecondConstant j
noncomputable def actual151KernelError (D : ℕ) (c : ℝ) : ℝ :=
  appendixBOriginalError D c+appendixBRoughRemovalConstant*lemma23PaperL D^(-8 : ℤ)
noncomputable def actual151FirstError (D : ℕ) (c : ℝ) : ℝ :=
  (1+‖lemma151Iota2‖)*actual151KernelError D c+
    appendixBTerminalTailErrorConstant c*lemma23PaperL D^(-8 : ℤ)
noncomputable def actual151SecondError (D : ℕ) (c : ℝ) : ℝ :=
  (‖lemma151Iota3‖+‖lemma151Iota4‖)*actual151KernelError D c

noncomputable def actual151RoughFactor (D : ℕ) (β : ℂ) (w : ℕ→ℂ) (d : ℕ) : ℂ :=
  ∑ n∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,w (d*n)*lemma151Rho β n/n
noncomputable def actual151FullFactor (D : ℕ) (β : ℂ) (w : ℕ→ℂ) (d : ℕ) : ℂ :=
  ∑ n∈Icc 1 ⌊lemma23PaperP D⌋₊,w (d*n)*lemma151Rho β n/n

lemma actual151_full_factor_linear (D : ℕ) (β : ℂ) (w v : ℕ→ℂ)
    (a b : ℂ) (d : ℕ) :
    actual151FullFactor D β (fun n => a*w n+b*v n) d=
      a*actual151FullFactor D β w d+b*actual151FullFactor D β v d := by
  unfold actual151FullFactor
  simp only [mul_sum,←sum_add_distrib]
  exact sum_congr rfl (fun n _ => by ring)

lemma actual151_linear_error {x y a b u v : ℂ} {E F : ℝ}
    (hx : ‖x-u‖≤E) (hy : ‖y-v‖≤F) :
    ‖a*x+b*y-(a*u+b*v)‖≤‖a‖*E+‖b‖*F := by
  have he : a*x+b*y-(a*u+b*v)=a*(x-u)+b*(y-v) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by
    simp only [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hy (norm_nonneg _)))

/-- B.2 is applied to each concrete finite factor, including all prime powers. -/
theorem actual151_bounded_rough_removal_uniform {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ,∀ D : ℕ,D₀≤D → ∀ j : Fin 3,∀ w : ℕ→ℂ,∀ W : ℝ,
      0≤W → (∀ n,‖w n‖≤W) → ∀ d : ℕ,
      ‖actual151RoughFactor D (lemma83PaperBeta D c j) w d-
        actual151FullFactor D (lemma83PaperBeta D c j) w d‖≤
          W*(appendixBRoughRemovalConstant*lemma23PaperL D^(-8 : ℤ)) := by
  obtain ⟨N,hN⟩ := appendixB_original_B2_uniform c hc
  refine ⟨N,?_⟩
  intro D hD j w W hW hw d
  have hP := b_paperP_one_le D
  have hN1 : 1≤⌊lemma23PaperP D⌋₊ := (Nat.one_le_floor_iff _).mpr hP
  have hNP := Nat.floor_le (zero_le_one.trans hP)
  exact (appendixB_weighted_rough_removal (lemma83PaperBeta D c j)
    (Icc 1 ⌊lemma23PaperP D⌋₊) (fun _ h => h) (fun n => w (d*n)) W hW
      (fun n _ => hw _)).trans
    (mul_le_mul_of_nonneg_left (hN D hD j _ hN1 hNP) hW)

/-- The original full finite U,V factors are compared to their actual constants. -/
theorem actual151_full_factors_uniform {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ,2≤D₀ ∧ ∀ D : ℕ,D₀≤D → ∀ j : Fin 3,∀ d : ℕ,
      0<d → (d : ℝ)<lemma56PaperT D →
      ‖actual151FullFactor D (lemma83PaperBeta D c j) (lemma151First D) d-
        actual151FirstConstant (j.val+1)‖≤
        (1+‖lemma151Iota2‖)*appendixBOriginalError D c+
          appendixBTerminalTailErrorConstant c*lemma23PaperL D^(-8 : ℤ) ∧
      ‖actual151FullFactor D (lemma83PaperBeta D c j) (lemma151Second D) d-
        actual151SecondConstant (j.val+1)‖≤
        (‖lemma151Iota3‖+‖lemma151Iota4‖)*appendixBOriginalError D c := by
  obtain ⟨N,hN,hfull⟩ := appendixB_original_printed_constants_uniform hc
  obtain ⟨M,hM,hh14⟩ := appendixB_actual_h14_terminal_quantitative hc
  obtain ⟨K,hK⟩ := eventually_atTop.mp (appendixB_sharp_tail_error_eventual_power c)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp appendixB_original_cutoffs_eventually
  refine ⟨max N (max M (max K J)),hN.trans (le_max_left _ _),?_⟩
  intro D hD j d hd hdT
  have hN' : N≤D := (le_max_left _ _).trans hD
  have hMKJ : max M (max K J)≤D := (le_max_right _ _).trans hD
  have hM' : M≤D := (le_max_left _ _).trans hMKJ
  have hKJ : max K J≤D := (le_max_right _ _).trans hMKJ
  have hK' : K≤D := (le_max_left _ _).trans hKJ
  have hJ' : J≤D := (le_max_right _ _).trans hKJ
  have hcuts := (hJ D hJ').2
  have h2P : lemma151P2 D≤lemma23PaperP D := ((hcuts 1).2.2.1).le
  have h3P : lemma151P3 D≤lemma23PaperP D := ((hcuts 2).2.2.1).le
  have hsP : (lemma23PaperP D)^(1/2 : ℝ)≤lemma23PaperP D := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (b_paperP_one_le D) (by norm_num : (1/2 : ℝ)≤1)
  have h14 := (hh14 D hM' j d hd hdT).trans
    (add_le_add le_rfl (hK D hK'))
  have h2 := hfull D hN' j (1 : Fin 3) d hd hdT
  have h3 := hfull D hN' j (2 : Fin 3) d hd hdT
  have ht14 := actual151_weight_tsum_finite (b_h14_strict_support D) d hd hsP
    (lemma151Rho (lemma83PaperBeta D c j)) (fun _ => True)
  have ht2 := appendixB_kernel_tsum_finite (lemma151P2 D) (lemma23PaperP D)
    (lemma151Beta7 D) d hd h2P (lemma151Rho (lemma83PaperBeta D c j)) (fun _ => True)
  have ht3 := appendixB_kernel_tsum_finite (lemma151P3 D) (lemma23PaperP D)
    (lemma151Beta6 D) d hd h3P (lemma151Rho (lemma83PaperBeta D c j)) (fun _ => True)
  simp only [ite_true,filter_true] at ht14 ht2 ht3
  rw [ht14] at h14
  change ‖(∑' n : ℕ,lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) (d*n)*
    lemma151Rho (lemma83PaperBeta D c j) n/n)-
    lemma151FullKernelConstant 0.5 (5/2) (j.val+1)‖≤_ at h2
  change ‖(∑' n : ℕ,lemma151Kernel (lemma151P3 D) (lemma151Beta6 D) (d*n)*
    lemma151Rho (lemma83PaperBeta D c j) n/n)-
    lemma151FullKernelConstant 0.498 (3/2) (j.val+1)‖≤_ at h3
  rw [ht2] at h2
  rw [ht3] at h3
  constructor
  · have hu : lemma151First D=(fun n => 1*bH14Coefficient D n+
        lemma151Iota2*lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) n) := by
      funext n; simp only [lemma151First,bH14Coefficient,one_mul]
    rw [hu,actual151_full_factor_linear]
    have he := actual151_linear_error (a := (1 : ℂ)) (b := lemma151Iota2) h14 h2
    convert he using 1 <;>
      simp only [actual151FirstConstant,actual151FullFactor,norm_one,one_mul] <;> ring
  · have hv : lemma151Second D=(fun n =>
        conj lemma151Iota3*lemma151Kernel (lemma151P3 D) (lemma151Beta6 D) n+
        conj lemma151Iota4*lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) n) := rfl
    rw [hv,actual151_full_factor_linear]
    have he := actual151_linear_error (a := conj lemma151Iota3)
      (b := conj lemma151Iota4) h3 h2
    simpa only [actual151SecondConstant,actual151FullFactor,norm_conj,add_mul] using he

/-- One common threshold controls both actual rough factors at every positive d<T. -/
theorem actual151_rough_factors_uniform {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ,2≤D₀ ∧ ∀ D : ℕ,D₀≤D → ∀ j : Fin 3,∀ d : ℕ,
      0<d → (d : ℝ)<lemma56PaperT D →
      ‖actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151First D) d-
        actual151FirstConstant (j.val+1)‖≤actual151FirstError D c ∧
      ‖actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151Second D) d-
        actual151SecondConstant (j.val+1)‖≤actual151SecondError D c := by
  obtain ⟨N,hN,hfull⟩ := actual151_full_factors_uniform hc
  obtain ⟨M,hrem⟩ := actual151_bounded_rough_removal_uniform hc
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD j d hd hdT
  have hN' : N≤D := (le_max_left _ _).trans hD
  have hM' : M≤D := (le_max_right _ _).trans hD
  obtain ⟨h1,h2⟩ := hfull D hN' j d hd hdT
  have hr1 := hrem D hM' j (lemma151First D) (1+‖lemma151Iota2‖)
    (by positivity) (b_first_norm_bound D) d
  have hr2 := hrem D hM' j (lemma151Second D) (‖lemma151Iota3‖+‖lemma151Iota4‖)
    (by positivity) (b_second_norm_bound D) d
  constructor
  · exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add hr1 h1).trans_eq (by unfold actual151FirstError actual151KernelError; ring))
  · exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add hr2 h2).trans_eq (by unfold actual151SecondError actual151KernelError; ring))

end ZhangLS.Spec
