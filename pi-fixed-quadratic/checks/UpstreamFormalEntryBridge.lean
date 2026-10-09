import FixedQuadratic.FormalEntry
import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic

namespace FixedQuadratic.UpstreamBridge

/-- Directly connects the new formal polynomial to the pinned upstream entry,
for arbitrary complex centers and log polynomials. -/
theorem entry_specialization {m : ℕ} (β : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s h : ℕ) (b a : Fin m → ℕ) :
    MvPolynomial.eval β (formalEntry (fun _ => 2*(j : ℂ)*Complex.I) G s h b a) =
      OAI.PiExponent.InterpolationMatrix.entry (fun i => 2*Complex.I*β i) G j s b h a := by
  rw [formalEntry_eval, OAI.PiExponent.InterpolationMatrix.entry_eq_binomial_product]
  have hc : ∀ i, (2*(j : ℂ)*Complex.I)*β i = (j : ℂ)*(2*Complex.I*β i) :=
    fun i => by ring
  simp only [hc]

end FixedQuadratic.UpstreamBridge

#check @FixedQuadratic.UpstreamBridge.entry_specialization
#print axioms FixedQuadratic.UpstreamBridge.entry_specialization
