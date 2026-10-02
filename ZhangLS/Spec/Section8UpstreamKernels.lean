import ZhangLS.Spec.Lemma82Definitions
import ZhangLS.Spec.Lemma84PaperResidue
import ZhangLS.Spec.Lemma84Section8Cutoffs
import ZhangLS.Spec.Section8NumericalObjects

/-! Algebraic audit only: finite-c′ identities retain c′ and actual upstream definitions.
No character-sum asymptotic or boundary replacement is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
noncomputable section
namespace Section8Upstream
open Complex ZhangLS.Spec

/-- The exact small parameter; c is fixed before D tends to infinity. -/
def eps (D : ℕ) (c : ℝ) : ℝ := c * lemma44PaperAlpha D * lemma23PaperL D

def t (e : ℝ) (j : Fin 3) : ℝ :=
  if j = 0 then 1-5*e else if j = 1 then 2+2*e else 3-3*e

def r (μ : ℕ) : ℝ := if μ=6 then 3/2 else 5/2

def F (e : ℝ) (j : Fin 3) (μ : ℕ) (z : ℝ) : ℂ :=
  (1 + (Real.pi:ℂ)*I*((r μ-t e j):ℝ)*z) * exp ((Real.pi:ℂ)*I*(r μ:ℝ)*z)

def G (e : ℝ) (j : Fin 3) (μ : ℕ) (z : ℝ) : ℂ :=
  let a : ℂ := t e (j+1)
  let b : ℂ := t e (j+2)
  let m : ℂ := r μ
  a*b/m^2 + (1-a*b/m^2 - (Real.pi:ℂ)*I*(a-m)*(b-m)/m*z) *
    exp (-(Real.pi:ℂ)*I*m*z)

lemma paper_beta_scaled (D : ℕ) (c : ℝ) (j : Fin 3) :
    lemma82PaperBeta D c j = I*(lemma44PaperAlpha D:ℂ)*(t (eps D c) j:ℝ) := by
  fin_cases j <;> norm_num [lemma82PaperBeta,lemma52PaperBetaOne,lemma52PaperBetaTwo,
    lemma52PaperBetaThree,lemma23PaperOffsetOne,lemma23PaperOffsetTwo,
    lemma23PaperOffsetThree,t,eps] <;> ring

lemma paper_beta_agreement (D : ℕ) (c : ℝ) (j : Fin 3) :
    lemma83PaperBeta D c j = lemma82PaperBeta D c j := rfl

lemma smoothing_scaled (D μ : ℕ) :
    lemma82SmoothingBeta D μ = I*(lemma44PaperAlpha D:ℂ)*(r μ:ℝ) := by
  unfold lemma82SmoothingBeta r
  split_ifs <;> push_cast <;> ring

lemma smoothing_agreement (D μ : ℕ) :
    lemma84SmoothingBeta D μ = lemma82SmoothingBeta D μ := rfl

lemma alpha_log_P {D : ℕ} (hL : 0 < lemma23PaperL D) :
    lemma44PaperAlpha D * Real.log (lemma23PaperP D) = Real.pi := by
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  field_simp

lemma scale_log_rpow (D : ℕ) (z : ℝ) :
    Real.log ((lemma23PaperP D)^z) = Real.log (lemma23PaperP D)*z := by
  rw [Real.log_rpow (show 0 < lemma23PaperP D from Real.exp_pos _)]
  ring

lemma exponent_scaled {D : ℕ} (hL : 0 < lemma23PaperL D) (μ : ℕ) (z : ℝ) :
    lemma82SmoothingBeta D μ * (Real.log ((lemma23PaperP D)^z):ℂ) =
      (Real.pi:ℂ)*I*(r μ:ℝ)*z := by
  rw [smoothing_scaled,scale_log_rpow]
  have h := congrArg (fun x : ℝ => (x:ℂ)) (alpha_log_P hL)
  push_cast at h ⊢
  calc
    _ = ((lemma44PaperAlpha D:ℂ)*(Real.log (lemma23PaperP D):ℂ))*I*(r μ:ℂ)*z := by ring
    _ = _ := by rw [h]

lemma actual_F_normalized {D : ℕ} (hL : 0 < lemma23PaperL D)
    (c : ℝ) (j : Fin 3) (μ : ℕ) (z : ℝ) :
    lemma82MainTerm D c j μ ((lemma23PaperP D)^z) = F (eps D c) j μ z := by
  have hx : 0 < (lemma23PaperP D)^z := Real.rpow_pos_of_pos (Real.exp_pos _) _
  unfold lemma82MainTerm F
  rw [lemma84_positive_cpow_eq_exp hx,exponent_scaled hL]
  congr 2
  rw [smoothing_scaled,paper_beta_scaled,scale_log_rpow]
  have h := congrArg (fun x : ℝ => (x:ℂ)) (alpha_log_P hL)
  push_cast at h ⊢
  calc
    _ = ((lemma44PaperAlpha D:ℂ)*(Real.log (lemma23PaperP D):ℂ))*I*((r μ:ℂ)-t (eps D c) j)*z := by ring
    _ = _ := by rw [h]

lemma G_scale (q a b m l : ℂ) (hq : q ≠ 0) (hm : m ≠ 0) :
    (q*a)*(q*b)/(q*m)^2 +
      (1-(q*a)*(q*b)/(q*m)^2-(q*a-q*m)*(q*b-q*m)/(q*m)*l)*exp (-(q*m)*l) =
    a*b/m^2+(1-a*b/m^2-(q*l)*(a-m)*(b-m)/m)*exp (-(q*l)*m) := by
  have hex : -(q*m)*l = -(q*l)*m := by ring
  rw [hex]
  field_simp

lemma actual_G_normalized {D : ℕ} (hL : 0 < lemma23PaperL D)
    (c : ℝ) (j : Fin 3) (μ : ℕ) (z : ℝ) :
    lemma84MainTerm D c j μ ((lemma23PaperP D)^z) = G (eps D c) j μ z := by
  have hx : 0 < (lemma23PaperP D)^z := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have ha : lemma44PaperAlpha D ≠ 0 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    exact div_ne_zero Real.pi_ne_zero (ne_of_gt (pow_pos hL 9))
  have hq : I*(lemma44PaperAlpha D:ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr ha)
  have hr : (r μ:ℂ) ≠ 0 := by unfold r; split_ifs <;> norm_num
  unfold lemma84MainTerm G
  simp only [paper_beta_agreement,paper_beta_scaled,smoothing_agreement,smoothing_scaled,
    lemma84_positive_cpow_eq_exp hx]
  rw [G_scale _ _ _ _ _ hq hr]
  have hscale : I*(lemma44PaperAlpha D:ℂ)*(Real.log ((lemma23PaperP D)^z):ℂ) =
      (Real.pi:ℂ)*I*z := by
    rw [scale_log_rpow]
    have h := congrArg (fun x : ℝ => (x:ℂ)) (alpha_log_P hL)
    push_cast at h ⊢
    calc
      _ = ((lemma44PaperAlpha D:ℂ)*(Real.log (lemma23PaperP D):ℂ))*I*z := by ring
      _ = _ := by rw [h]
  rw [hscale]
  congr 2 <;> ring

lemma all_F_at_zero (z : ℝ) :
    F 0 0 6 z=Section8.f16 z ∧ F 0 1 6 z=Section8.f26 z ∧
    F 0 2 6 z=Section8.f36 z ∧ F 0 0 7 z=Section8.f17 z ∧
    F 0 1 7 z=Section8.f27 z ∧ F 0 2 7 z=Section8.f37 z := by
  norm_num [F,t,r,Fin.ext_iff,Section8.f16,Section8.f26,Section8.f36,
    Section8.f17,Section8.f27,Section8.f37]
  repeat' constructor
  all_goals congr 2 <;> ring

lemma all_G_at_zero (z : ℝ) :
    G 0 0 6 z=Section8.g16 z ∧ G 0 1 6 z=Section8.g26 z ∧
    G 0 2 6 z=Section8.g36 z ∧ G 0 0 7 z=Section8.g17 z ∧
    G 0 1 7 z=Section8.g27 z ∧ G 0 2 7 z=Section8.g37 z := by
  norm_num [G,t,r,
    show (1:Fin 3)+1=2 from rfl, show (1:Fin 3)+2=0 from rfl,
    show (2:Fin 3)+1=0 from rfl, show (2:Fin 3)+2=1 from rfl,
    show ¬(2:Fin 3)=0 from by decide, show ¬(2:Fin 3)=1 from by decide,
    Section8.g16,Section8.g26,Section8.g36,
    Section8.g17,Section8.g27,Section8.g37]
  repeat' constructor
  all_goals congr 2 <;> ring

#print axioms actual_F_normalized
#print axioms actual_G_normalized
#print axioms all_F_at_zero
#print axioms all_G_at_zero
end Section8Upstream
