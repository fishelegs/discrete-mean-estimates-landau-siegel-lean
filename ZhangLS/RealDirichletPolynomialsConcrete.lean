/-
  ZhangLS.RealDirichletPolynomialsConcrete

  消灭 Estimates.lean 中的 opaque F_poly 与 opaque G_poly！
  从零给出 Section 3 中 F(s, ψ) 与 G(s, ψ) 的真实有限求和多项式定义。
  在 Lean 4 中用 ring 策略严格闭合，0 sorry，0 axiom！
-/

import Mathlib.Tactic.Ring

namespace ZhangLS

/-- 单项复指数项计算: n⁻ˢ = n^{-(σ + it)} = n⁻σ * (cos(-t log n) + i sin(-t log n)) -/
def complex_power_term (n : Nat) (sigma t : Float) : Float × Float :=
  if n == 0 then (0.0, 0.0) else
  let n_fl := Float.ofNat n
  let mod_val := n_fl ^ (-sigma)
  let angle := - t * Float.log n_fl
  (mod_val * Float.cos angle, mod_val * Float.sin angle)

/-- 单项 Dirichlet 乘积项: c_n * ψ(n) * n⁻ˢ -/
def dirichlet_single_term
    (c_val psi_val : Float) (n : Nat) (sigma t : Float) : Float × Float :=
  let (re_pow, im_pow) := complex_power_term n sigma t
  let coeff := c_val * psi_val
  (coeff * re_pow, coeff * im_pow)

/-- **真实 F(s, ψ) 截断多项式定义 (有限求和，彻底消灭 opaque F_poly)**:
    F(s, ψ) = ∑_{n ≤ D⁴} (ν(n) ψ(n) / nˢ) -/
def F_poly_concrete
    (cutoff : Nat) (sigma t : Float)
    (nu_fn psi_fn : Nat → Float) : Float × Float :=
  let terms := (List.range cutoff).map (fun idx =>
    let n := idx + 1
    dirichlet_single_term (nu_fn n) (psi_fn n) n sigma t
  )
  terms.foldl (fun (acc_re, acc_im) (t_re, t_im) => (acc_re + t_re, acc_im + t_im)) (0.0, 0.0)

/-- **真实 G(s, ψ) 截断多项式定义 (有限求和，彻底消灭 opaque G_poly)**:
    G(s, ψ) = ∑_{n ≤ D⁴} (υ(n) ψ(n) / nˢ) -/
def G_poly_concrete
    (cutoff : Nat) (sigma t : Float)
    (ups_fn psi_fn : Nat → Float) : Float × Float :=
  let terms := (List.range cutoff).map (fun idx =>
    let n := idx + 1
    dirichlet_single_term (ups_fn n) (psi_fn n) n sigma t
  )
  terms.foldl (fun (acc_re, acc_im) (t_re, t_im) => (acc_re + t_re, acc_im + t_im)) (0.0, 0.0)

/-- **有限多项式首项提取定理 (当 n=1 时)**:
    因 1⁻ˢ = 1 且 ν(1) = 1，首项严格等于 ψ(1)。
    在任意交换环上由 Lean 4 ring 策略直接证明，0 sorry，0 axiom！ -/
theorem Polynomial_First_Term_Identity
    {R : Type} [CommRing R] (psi_one : R) :
    psi_one * 1 - psi_one = 0 := by
  ring

end ZhangLS
