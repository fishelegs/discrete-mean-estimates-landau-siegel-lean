import FixedQuadratic.MinorArithmetic
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

open OAI.PiExponent.InterpolationMatrix

noncomputable def selectedFormalMinor {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (T : Fin m → ℕ)
    (selection : Row K v0 θ w H → Column w0 w H) : MvPolynomial (Fin m) ℂ :=
  formalMinor T (fun ρ => ρ.1.val) (fun ρ => ρ.2.1 0)
    (fun ρ => (selection ρ).1 0) (fun ρ i => ρ.2.1 i.succ)
    (fun ρ i => (selection ρ).1 i.succ)

/-- Exact bridge to a selected square minor of the real upstream packet. -/
theorem minor_specialization {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (T : Fin m → ℕ) (β : Fin m → ℂ)
    (selection : Row K v0 θ w H → Column w0 w H) :
    MvPolynomial.eval β (selectedFormalMinor K w0 v0 θ w H T selection) =
      ((truncatedLogMatrix K w0 v0 θ w H (fun i => 2*Complex.I*β i) T).submatrix
        id selection).det := by
  classical
  let A : Matrix (Row K v0 θ w H) (Row K v0 θ w H) (MvPolynomial (Fin m) ℂ) :=
    fun ρ σ => formalEntry (fun _ => 2*(ρ.1.val : ℂ)*Complex.I)
      (fun i => FixedQuadratic.truncatedLog (T i)) (ρ.2.1 0) ((selection σ).1 0)
      (fun i => ρ.2.1 i.succ) (fun i => (selection σ).1 i.succ)
  change (MvPolynomial.eval β) A.det = _
  rw [(MvPolynomial.eval β).map_det A]
  congr 1
  ext ρ σ
  exact entry_specialization β (fun i => FixedQuadratic.truncatedLog (T i))
    ρ.1.val (ρ.2.1 0) ((selection σ).1 0) (fun i => ρ.2.1 i.succ)
    (fun i => (selection σ).1 i.succ)

/-- A genuine upstream nonzero selected minor supplies the nonzero formal
polynomial; geometric surjectivity is still an independent obligation. -/
theorem selectedFormalMinor_ne_zero {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (T : Fin m → ℕ) (β : Fin m → ℂ)
    (selection : Row K v0 θ w H → Column w0 w H)
    (hne : ((truncatedLogMatrix K w0 v0 θ w H (fun i => 2*Complex.I*β i) T).submatrix
      id selection).det ≠ 0) :
    selectedFormalMinor K w0 v0 θ w H T selection ≠ 0 := by
  intro hz
  apply hne
  rw [← minor_specialization, hz, map_zero]

/-- Actual legal selected columns, together with the actual minor's nonzero
matching, give the joint MN minus row rebate. No independent coordinate
upper bounds replace this budget. -/
theorem selected_weighted_rebate_budget {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (T : Fin m → ℕ)
    (selection : Row K v0 θ w H → Column w0 w H)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (hne : selectedFormalMinor K w0 v0 θ w H T selection ≠ 0) :
    (∑ i, w i * (minorDegrees (fun ρ i => (selection ρ).1 i.succ)
      (fun ρ i => ρ.2.1 i.succ) i : ℝ)) ≤
      Fintype.card (Row K v0 θ w H)*H - ∑ ρ : Row K v0 θ w H,
        ∑ i, w i*(ρ.2.1 i.succ : ℝ) := by
  classical
  have hrows : ∀ i : Fin m, (∑ ρ : Row K v0 θ w H, ρ.2.1 i.succ) ≤
      ∑ ρ : Row K v0 θ w H, (selection ρ).1 i.succ := by
    apply row_total_le_column_total _ _ _ hne
    intro ρ σ hab
    exact formalEntry_zero_of_incompatible _ _ _ _ _ _ hab
  change (∑ i, w i * (((∑ ρ : Row K v0 θ w H, (selection ρ).1 i.succ)-
    ∑ ρ : Row K v0 θ w H, ρ.2.1 i.succ : ℕ) : ℝ)) ≤ _
  rw [weighted_rebate _ _ w hrows]
  apply sub_le_sub_right
  calc
    _ ≤ ∑ _ρ : Row K v0 θ w H, H := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hc := column_weight_le hw0 hw (selection ρ)
      have hp : 0 ≤ w0*((selection ρ).1 0 : ℝ) := mul_nonneg hw0.le (by positivity)
      linarith
    _ = _ := by simp

end FixedQuadratic.UpstreamBridge

#check @FixedQuadratic.UpstreamBridge.entry_specialization
#print axioms FixedQuadratic.UpstreamBridge.entry_specialization
#check @FixedQuadratic.UpstreamBridge.selectedFormalMinor
#print axioms FixedQuadratic.UpstreamBridge.selectedFormalMinor
#check @FixedQuadratic.UpstreamBridge.minor_specialization
#print axioms FixedQuadratic.UpstreamBridge.minor_specialization
#check @FixedQuadratic.UpstreamBridge.selectedFormalMinor_ne_zero
#print axioms FixedQuadratic.UpstreamBridge.selectedFormalMinor_ne_zero
#check @FixedQuadratic.UpstreamBridge.selected_weighted_rebate_budget
#print axioms FixedQuadratic.UpstreamBridge.selected_weighted_rebate_budget
