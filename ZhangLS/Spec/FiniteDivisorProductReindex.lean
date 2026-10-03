import ZhangLS.Spec.Proposition71ConvolutionSplit

/-! Exact finite divisor-antidiagonal to product reindexing for a positive
factor-closed support. The product membership condition is retained. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

theorem finiteDivisorProduct_reindex {E : Type*} [AddCommMonoid E]
    (S : Finset ℕ) (hpos : ∀d∈S,0<d)
    (hfac : ∀a b : ℕ,0<a → 0<b → a*b∈S → a∈S ∧ b∈S)
    (F : ℕ → ℕ → E) :
    (∑d∈S,∑ab∈d.divisorsAntidiagonal,F ab.1 ab.2)=
      ∑a∈S,∑b∈S,if a*b∈S then F a b else 0 := by
  let T : Finset (Σ _d : ℕ, ℕ×ℕ) := S.sigma (fun d => d.divisorsAntidiagonal)
  let U := (S.product S).filter (fun ab : ℕ×ℕ => ab.1*ab.2∈S)
  have he : (∑i∈T,F i.2.1 i.2.2)=∑ab∈U,F ab.1 ab.2 := by
    apply sum_bij (fun i _ => i.2)
    · intro i hi
      have hm := mem_sigma.mp hi
      have hp := (Nat.mem_divisorsAntidiagonal.mp hm.2).1
      have hp0 : 0 < i.2.1*i.2.2 := hp.symm ▸ hpos i.1 hm.1
      have hfactor := hfac i.2.1 i.2.2 (Nat.pos_of_mul_pos_right hp0) (Nat.pos_of_mul_pos_left hp0) (hp.symm ▸ hm.1)
      exact mem_filter.mpr ⟨mem_product.mpr hfactor,hp.symm ▸ hm.1⟩
    · intro i hi j hj hij
      have hi' := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hi).2).1
      have hj' := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hj).2).1
      have hd : i.1=j.1 := by rw [←hi',←hj',hij]
      exact Sigma.ext hd (by cases i; cases j; dsimp at *; subst_vars; rfl)
    · intro ab hab
      have hh := mem_filter.mp hab
      have hab0 : ab.1*ab.2≠0 := (hpos _ hh.2).ne'
      refine ⟨⟨ab.1*ab.2,ab⟩,?_,rfl⟩
      exact mem_sigma.mpr ⟨hh.2,Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,hab0⟩⟩
    · intro i hi
      rfl
  have he' : (∑d∈S,∑ab∈d.divisorsAntidiagonal,F ab.1 ab.2)=
      ∑ab∈S.product S,if ab.1*ab.2∈S then F ab.1 ab.2 else 0 := by
    simpa only [T,U,sum_sigma,sum_filter] using he
  exact he'.trans (Finset.sum_product S S
    (fun ab : ℕ×ℕ => if ab.1*ab.2∈S then F ab.1 ab.2 else 0))

end ZhangLS.Spec
