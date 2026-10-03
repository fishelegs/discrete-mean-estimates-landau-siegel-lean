import ZhangLS.Spec.AppendixBTailContour
import ZhangLS.Spec.AppendixBTailLeftBoundary
import ZhangLS.Spec.AppendixBTailBudgetDecay
import ZhangLS.Spec.AppendixBTailTerminalResidue
import ZhangLS.Spec.AppendixBTailSharpIntegral
import ZhangLS.Spec.AppendixBTailFarBoundary
import ZhangLS.Spec.AppendixBTailRhoBounds
import ZhangLS.Spec.AppendixBTailOriginalRange
import ZhangLS.Spec.AppendixBKernelRegressions

/-! Source and endpoint regressions for the bounded complementary-tail seam.
No complete sharp-tail asymptotic or numerical repair is asserted. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

/-- Equality is retained in the actual complementary kernel. -/
theorem appendixB_actual_complement_endpoint (D n : ℕ)
    (hn : (n : ℝ)=(lemma23PaperP D)^(1/2 : ℝ)) :
    appendixBComplementKernel (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ))
      (lemma151Beta6 D) n=lemma151Kernel (lemma151P1 D) (lemma151Beta6 D) n ∧
    bH14Coefficient D n=0 := by
  exact ⟨(appendixB_tail_includes_equality (lemma151Beta6 D) hn).1,
    (appendixB_H14_endpoint_separate D n hn).1⟩

/-- The printed e1j'' is preserved as printed; this does not identify it
with the complementary tail or with the terminal residue coefficient. -/
theorem appendixB_printed_tail_literal (j : ℕ) :
    lemma151PrintedTail j=(j : ℂ)/0.756 *
      ∫ z : ℝ in (0 : ℝ)..0.004,
        (Complex.exp (((3/2 : ℝ)*(0.504-z)*Real.pi : ℝ)*I)-
          Complex.exp (((3/4 : ℝ)*Real.pi : ℝ)*I)) := rfl

/-- The source terminal residue uses z in [.5,.504], not [0,.004]. -/
theorem appendixB_terminal_tail_literal (j : ℕ) :
    lemma151ResidueTail j=(j : ℂ)/0.756 *
      ∫ z : ℝ in (0.5 : ℝ)..0.504,
        (Complex.exp (((3/2 : ℝ)*(0.504-z)*Real.pi : ℝ)*I)-
          Complex.exp ((0.006*Real.pi : ℝ)*I)) := rfl

/-- Published terminal identity, with its sign retained. -/
theorem appendixB_terminal_tail_sign (j : ℕ) :
    lemma151ResidueTail j= -I*Real.pi*j*lemma151BStar :=
  lemma151_residue_tail_eq_neg_pi_I_bstar j

end ZhangLS.Spec
