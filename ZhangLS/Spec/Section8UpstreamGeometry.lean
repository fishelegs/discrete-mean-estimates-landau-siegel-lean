import ZhangLS.Spec.Section8UpstreamLimits
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Section8Upstream
open Complex ZhangLS.Spec Filter Topology

/-- Exact finite-D correction caused by the original T^(-10) cutoff. -/
def delta (D : ℕ) : ℝ := 10*Real.log (lemma56PaperT D)/Real.log (lemma23PaperP D)

lemma delta_eq {D : ℕ} (hL : 0 < lemma23PaperL D) :
    delta D = 10/(lemma23PaperL D)^(79/10:ℝ) := by
  have hmul : (lemma23PaperL D)^(79/10:ℝ)*(lemma23PaperL D)^(11/10:ℝ) =
      (lemma23PaperL D)^9 := by
    rw [←Real.rpow_add hL]
    norm_num
  unfold delta lemma56PaperT lemma23PaperP
  rw [Real.log_exp,Real.log_exp,←hmul]
  have hp : (lemma23PaperL D)^(11/10:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  field_simp

lemma delta_tendsto : Tendsto delta atTop (𝓝 0) := by
  have ht := (tendsto_rpow_atTop (show (0:ℝ)<79/10 by norm_num)).comp log_D_tendsto
  have h : Tendsto (fun D : ℕ => 10/(lemma23PaperL D)^(79/10:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  apply h.congr'
  filter_upwards [log_D_tendsto.eventually_gt_atTop 0] with D hD
  exact (delta_eq hD).symm

lemma alpha_log_T_eq (D : ℕ) :
    lemma44PaperAlpha D*Real.log (lemma56PaperT D) = (Real.pi/10)*delta D := by
  unfold lemma44PaperAlpha delta
  ring

lemma alpha_log_T_tendsto :
    Tendsto (fun D : ℕ => lemma44PaperAlpha D*Real.log (lemma56PaperT D)) atTop (𝓝 0) := by
  have h := tendsto_const_nhds.mul delta_tendsto (a := Real.pi/10)
  simpa only [←alpha_log_T_eq,mul_zero] using h

lemma exact_log_P1 {D : ℕ} (hL : 0 < lemma23PaperL D) :
    Real.log (lemma84Section8P1 D)/Real.log (lemma23PaperP D)=63/125 := by
  rw [lemma84_section8_log_p1,lemma23PaperP,Real.log_exp]
  field_simp

lemma exact_log_P2 {D : ℕ} (hL : 0 < lemma23PaperL D) :
    Real.log (lemma84Section8P2 D)/Real.log (lemma23PaperP D)=1/2-delta D := by
  rw [lemma84_section8_log_p2]
  unfold delta lemma56PaperT lemma23PaperP
  rw [Real.log_exp,Real.log_exp]
  field_simp

lemma exact_log_ratio {D : ℕ} (hL : 0 < lemma23PaperL D) :
    Real.log (lemma84Section8P1 D/lemma84Section8P2 D)/Real.log (lemma23PaperP D) =
      1/250+delta D := by
  have h1 : 0 < lemma84Section8P1 D := lemma84_section8_cutoff_pos D 6
  have h2 : 0 < lemma84Section8P2 D := by simpa [lemma84Section8Cutoff] using lemma84_section8_cutoff_pos D 7
  rw [Real.log_div h1.ne' h2.ne',sub_div,exact_log_P1 hL,exact_log_P2 hL]
  ring

lemma exact_pi_normalization {D : ℕ} (hL : 0 < lemma23PaperL D) :
    (lemma44PaperAlpha D*Real.log (lemma23PaperP D))⁻¹=Real.pi⁻¹ := by
  rw [alpha_log_P hL]

/-- Orientation forced by multiplication of H1 with its conjugate. -/
lemma cross_expansion (a b c d ι : ℂ) :
    (a+ι*b)*(c+star ι*d)=a*c+ι*(b*c)+star ι*(a*d)+(ι*star ι)*(b*d) := by ring

/-- The source's Hermitian symmetrization, without assuming diagonal entries real. -/
lemma cross_symmetrization (b11 b22 b12 b21 ι : ℂ) :
    let v := b11+ι*b21+star ι*b12+(‖ι‖^2:ℝ)*b22
    v+star v = (b11+star b11) +
      ι*(b21+star b12)+star ι*(b12+star b21)+(‖ι‖^2:ℝ)*(b22+star b22) := by
  simp only [star_add,star_mul,star_star]
  have hreal : star ((‖ι‖^2:ℝ):ℂ)=((‖ι‖^2:ℝ):ℂ) := by simp
  rw [hreal]
  ring

#print axioms delta_tendsto
#print axioms exact_log_P1
#print axioms exact_log_P2
#print axioms exact_log_ratio
#print axioms cross_symmetrization
end Section8Upstream
