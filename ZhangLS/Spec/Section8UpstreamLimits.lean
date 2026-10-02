import ZhangLS.Spec.Section8UpstreamKernels
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Section8Upstream
open Complex ZhangLS.Spec Filter Topology

lemma log_D_tendsto : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))

lemma eps_eq {D : ℕ} (hL : 0 < lemma23PaperL D) (c : ℝ) :
    eps D c = c*Real.pi/(lemma23PaperL D)^8 := by
  unfold eps lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  field_simp

/-- c stays arbitrary and fixed, never set to zero or made to depend on D. -/
lemma eps_tendsto (c : ℝ) : Tendsto (fun D : ℕ => eps D c) atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop (show (8:ℕ)≠0 by norm_num)).comp log_D_tendsto
  have h : Tendsto (fun D : ℕ => c*Real.pi/(lemma23PaperL D)^8) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  apply h.congr'
  filter_upwards [log_D_tendsto.eventually_gt_atTop 0] with D hD
  exact (eps_eq hD c).symm

lemma continuous_t (j : Fin 3) : Continuous (fun e : ℝ => t e j) := by
  unfold t
  split_ifs <;> fun_prop

lemma continuous_F (j : Fin 3) (μ : ℕ) (z : ℝ) : Continuous (fun e : ℝ => F e j μ z) := by
  have ht := continuous_t j
  unfold F
  fun_prop

lemma continuous_G (j : Fin 3) (μ : ℕ) (z : ℝ) : Continuous (fun e : ℝ => G e j μ z) := by
  have ht1 := continuous_t (j+1)
  have ht2 := continuous_t (j+2)
  unfold G
  fun_prop

/-- Genuine finite-D kernels converge to the table's common normal form. -/
lemma actual_F_tendsto (c : ℝ) (j : Fin 3) (μ : ℕ) (z : ℝ) :
    Tendsto (fun D : ℕ => lemma82MainTerm D c j μ ((lemma23PaperP D)^z))
      atTop (𝓝 (F 0 j μ z)) := by
  have h := ((continuous_F j μ z).tendsto 0).comp (eps_tendsto c)
  apply h.congr'
  filter_upwards [log_D_tendsto.eventually_gt_atTop 0] with D hD
  exact (actual_F_normalized hD c j μ z).symm

lemma actual_G_tendsto (c : ℝ) (j : Fin 3) (μ : ℕ) (z : ℝ) :
    Tendsto (fun D : ℕ => lemma84MainTerm D c j μ ((lemma23PaperP D)^z))
      atTop (𝓝 (G 0 j μ z)) := by
  have h := ((continuous_G j μ z).tendsto 0).comp (eps_tendsto c)
  apply h.congr'
  filter_upwards [log_D_tendsto.eventually_gt_atTop 0] with D hD
  exact (actual_G_normalized hD c j μ z).symm

#print axioms eps_tendsto
#print axioms actual_F_tendsto
#print axioms actual_G_tendsto
end Section8Upstream
