import ZhangLS.Spec.Proposition71GammaLineBound
import ZhangLS.Spec.AllModuliGaussParseval

/-! # Exact norms of the actual dominant reciprocal-Z kernel and parity error -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

noncomputable def proposition71DominantReciprocalZ {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  gaussSum θ⁻¹ ZMod.stdAddChar*(N : ℂ)^(s-1)*lemma53PaperThetaStar s

lemma proposition71_primitive_gauss_norm {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1) :
    ‖gaussSum θ ZMod.stdAddChar‖=Real.sqrt (N : ℝ) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  exact primitive_gauss_norm_square θ hθ hN

lemma proposition71_character_neg_one_norm {N : ℕ} (θ : DirichletCharacter ℂ N) :
    ‖θ (-1)‖=1 := by
  rcases θ.even_or_odd with h|h <;> rw [h] <;> norm_num

lemma proposition71_dominant_reciprocal_Z_norm {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    {s : ℂ} (hs : s.re=3/2) :
    ‖proposition71DominantReciprocalZ θ s‖=(N : ℝ)*‖lemma53PaperThetaStar s‖ := by
  have hi : θ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def,DirichletCharacter.conductor_inv]
    exact (DirichletCharacter.isPrimitive_def θ).mp hθ
  have hNp : 0<N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hp : ‖(N : ℂ)^(s-1)‖=Real.sqrt (N : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos hNp,Complex.sub_re,hs,Complex.one_re]
    norm_num only [show (3/2 : ℝ)-1=1/2 by norm_num]
    rw [←Real.sqrt_eq_rpow]
  unfold proposition71DominantReciprocalZ
  rw [norm_mul,norm_mul,proposition71_primitive_gauss_norm θ⁻¹ hi hN,hp,
    ←pow_two,Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The paper's exponentially small Gamma replacement error is an exact
parity term before taking its norm. -/
lemma proposition71_reciprocal_Z_error_exact {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    {s : ℂ} (hs : s.im≠0) :
    (lemma23DirichletZ θ s)⁻¹-proposition71DominantReciprocalZ θ s=
      proposition71DominantReciprocalZ θ s*θ (-1)*Complex.exp ((Real.pi : ℂ)*I*s) := by
  rw [proposition71_reciprocal_Z_exact θ hθ hN hs]
  unfold proposition71DominantReciprocalZ
  ring

theorem proposition71_reciprocal_Z_error_norm {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    {s : ℂ} (hs : s.re=3/2) (ht : s.im≠0) :
    ‖(lemma23DirichletZ θ s)⁻¹-proposition71DominantReciprocalZ θ s‖=
      (N : ℝ)*‖lemma53PaperThetaStar s‖*Real.exp (-Real.pi*s.im) := by
  rw [proposition71_reciprocal_Z_error_exact θ hθ hN ht,norm_mul,norm_mul,
    proposition71_dominant_reciprocal_Z_norm θ hθ hN hs,proposition71_character_neg_one_norm,mul_one,
    Complex.norm_exp]
  congr 2
  simp [Complex.mul_re,Complex.mul_im]

theorem proposition71_dominant_reciprocal_Z_line_bound {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1) (t : ℝ) :
    ‖proposition71DominantReciprocalZ θ ((3/2 : ℂ)+(t : ℂ)*I)‖≤4*(N : ℝ)*(1+|t|) := by
  rw [proposition71_dominant_reciprocal_Z_norm θ hθ hN (by norm_num)]
  have hb := mul_le_mul_of_nonneg_left (proposition71_theta_star_three_halves_bound t) (Nat.cast_nonneg N)
  convert hb using 1 <;> ring

end ZhangLS.Spec
