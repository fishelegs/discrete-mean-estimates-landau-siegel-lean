import checks.UpstreamFormalEntryBridge
import FixedQuadratic.FixedFieldArithmetic
import OAI.NumberTheory.PiExponent.Approximation.MatrixCounting

namespace FixedQuadratic.UpstreamPacketArithmetic
open scoped BigOperators
open OAI.PiExponent.InterpolationMatrix FixedQuadratic.UpstreamBridge

/-- Legal packets alone give every time/column budget used by the new
arithmetic bound. The weights need not arise from rational denominators. -/
theorem legal_packet_budgets {m : ℕ} (k : ℕ) (w0 v θ H wmin : ℝ)
    (w : Fin m → ℝ) (hw0 : 0 < w0) (hv : 0 < v) (hθ : 0 < θ)
    (hwmin : 0 < wmin) (hw : ∀ i, wmin ≤ w i)
    (selection : Row k v θ w H → Column w0 w H) :
    (∑ r : Row k v θ w H, r.2.1 0 : ℕ) ≤
        (Fintype.card (Row k v θ w H) : ℝ)*H/v ∧
    (∑ r : Row k v θ w H, (selection r).1 0 : ℕ) ≤
        (Fintype.card (Row k v θ w H) : ℝ)*H/w0 ∧
    (∑ r : Row k v θ w H, ∑ i : Fin m, (selection r).1 i.succ : ℕ) ≤
        (Fintype.card (Row k v θ w H) : ℝ)*H/wmin := by
  classical
  have hwp : ∀ i, 0 < w i := fun i => hwmin.trans_le (hw i)
  have hs (r : Row k v θ w H) : (r.2.1 0 : ℝ) ≤ H/v := by
    have hr := row_weight_lt hv hθ hwp r
    have hp : 0 ≤ (∑ i, w i*(r.2.1 i.succ : ℝ))/θ :=
      div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hwp i).le (by positivity))) hθ.le
    apply (le_div_iff₀ hv).mpr
    nlinarith
  have hh (r : Row k v θ w H) : ((selection r).1 0 : ℝ) ≤ H/w0 := by
    have hc := column_weight_le hw0 hwp (selection r)
    have hp : 0 ≤ ∑ i, w i*((selection r).1 i.succ : ℝ) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hwp i).le (by positivity))
    apply (le_div_iff₀ hw0).mpr
    nlinarith
  have ha (r : Row k v θ w H) : (∑ i : Fin m, (selection r).1 i.succ : ℕ) ≤ H/wmin := by
    have hc := column_weight_le hw0 hwp (selection r)
    have hp : 0 ≤ w0*((selection r).1 0 : ℝ) := mul_nonneg hw0.le (by positivity)
    have hm : wmin*(∑ i : Fin m, ((selection r).1 i.succ : ℝ)) ≤
        ∑ i, w i*((selection r).1 i.succ : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hw i) (by positivity))
    apply (le_div_iff₀ hwmin).mpr
    push_cast
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    calc
      _ ≤ ∑ _r : Row k v θ w H, H/v := Finset.sum_le_sum (fun r _ => hs r)
      _ = _ := by simp [mul_div_assoc]
  · push_cast
    calc
      _ ≤ ∑ _r : Row k v θ w H, H/w0 := Finset.sum_le_sum (fun r _ => hh r)
      _ = _ := by simp [mul_div_assoc]
  · push_cast
    calc
      _ ≤ ∑ _r : Row k v θ w H, H/wmin := Finset.sum_le_sum (fun r _ => by
        simpa only [Nat.cast_sum] using ha r)
      _ = _ := by simp [mul_div_assoc]

/-- The actual row rebate lies between zero and theta, without approximation
or rationality hypotheses. -/
theorem legal_packet_rebate {m : ℕ} (k : ℕ) (v θ H : ℝ) (w : Fin m → ℝ)
    (hv : 0 < v) (hθ : 0 < θ) (hw : ∀ i, 0 < w i)
    (hD : 0 < (Fintype.card (Row k v θ w H) : ℝ)*H) :
    let rebate := (∑ r : Row k v θ w H, ∑ i, w i*(r.2.1 i.succ : ℝ))/
      ((Fintype.card (Row k v θ w H) : ℝ)*H)
    0 ≤ rebate ∧ rebate ≤ θ := by
  dsimp only
  have hp : 0 ≤ ∑ r : Row k v θ w H, ∑ i, w i*(r.2.1 i.succ : ℝ) :=
    Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (by positivity)))
  refine ⟨div_nonneg hp hD.le, (div_le_iff₀ hD).mpr ?_⟩
  calc
    _ ≤ ∑ _r : Row k v θ w H, θ*H := by
      apply Finset.sum_le_sum
      intro r hr
      have h := row_weight_lt hv hθ hw r
      have hs : 0 ≤ v*(r.2.1 0 : ℝ) := mul_nonneg hv.le (by positivity)
      have hb : (∑ i, w i*(r.2.1 i.succ : ℝ))/θ ≤ H := by linarith
      simpa only [mul_comm] using (div_le_iff₀ hθ).mp hb
    _ = _ := by simp; ring

noncomputable def primitiveWeights {m : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) : Fin m → ℝ :=
  fun i => (Nat.ceil (Real.log (primitiveMinpolyHeight (β i : ℝ) : ℝ)) : ℝ)

/-- The normalized fixed-field arithmetic estimate for an actual selected
upstream matrix minor. All row/time/column/degree rebate budgets are discharged
from the actual packet membership. It does not assume jet surjectivity. -/
theorem actual_selected_minor_lower {m : ℕ} (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2)
    (β : Fin m → F) (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (k : ℕ) (hk : 0 < k) (w0 v θ H wmin scale : ℝ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv : 0 < v) (hθ : 0 < θ) (hH : 0 < H)
    (hwmin : 0 < wmin) (hscale : 0 ≤ scale)
    (hw : ∀ i, wmin ≤ primitiveWeights F β i)
    (hT : ∀ i, (T i : ℝ) ≤ scale*primitiveWeights F β i/v+1)
    (selection : Row k v θ (primitiveWeights F β) H → Column w0 (primitiveWeights F β) H)
    (hne : ((truncatedLogMatrix k w0 v θ (primitiveWeights F β) H
      (fun i => 2*Complex.I*((β i : ℝ) : ℂ)) T).submatrix id selection).det ≠ 0) :
    let D := (Fintype.card (Row k v θ (primitiveWeights F β) H) : ℝ)*H
    let rebate := (∑ r : Row k v θ (primitiveWeights F β) H,
      ∑ i, primitiveWeights F β i*(r.2.1 i.succ : ℝ))/D;
    -(1-rebate)-arithmeticError scale v w0 wmin k-
      Real.log ((Fintype.card (Row k v θ (primitiveWeights F β) H)).factorial : ℝ)/D ≤
      Real.log ‖((truncatedLogMatrix k w0 v θ (primitiveWeights F β) H
        (fun i => 2*Complex.I*((β i : ℝ) : ℂ)) T).submatrix id selection).det‖/D := by
  classical
  let w := primitiveWeights F β
  let R := Row k v θ w H
  let D : ℝ := (Fintype.card R : ℝ)*H
  have hwp : ∀ i, 0 < w i := fun i => hwmin.trans_le (hw i)
  have hRow : Nonempty R := by
    refine ⟨⟨⟨0, hk⟩, ⟨fun _ => 0, ?_⟩⟩⟩
    apply (row_mem_iff hv hθ hwp _).mpr
    simpa using hH
  have hM : 0 < (Fintype.card R : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hRow
  have hD : 0 < D := mul_pos hM hH
  rcases legal_packet_budgets k w0 v θ H wmin w hw0 hv hθ hwmin hw selection with ⟨hs, hh, hα⟩
  have hneFormal : MvPolynomial.eval (fun i => ((β i : ℝ) : ℂ))
      (selectedFormalMinor k w0 v θ w H T selection) ≠ 0 := by
    rw [minor_specialization]
    exact hne
  have hnonzero := selectedFormalMinor_ne_zero k w0 v θ w H T
    (fun i => ((β i : ℝ) : ℂ)) selection hne
  have hjoint := selected_weighted_rebate_budget k w0 v θ w H T selection hw0 hwp hnonzero
  let rebate := (∑ r : R, ∑ i, w i*(r.2.1 i.succ : ℝ))/D
  have hjoint' : ∑ i, w i*(minorDegrees (fun r i => (selection r).1 i.succ)
      (fun r i => r.2.1 i.succ) i : ℝ) ≤ D*(1-rebate) := by
    have he : D*(1-rebate) = D-∑ r : R, ∑ i, w i*(r.2.1 i.succ : ℝ) := by
      dsimp [rebate]
      field_simp [hD.ne']
    rw [he]
    exact hjoint
  have hb := (legal_packet_rebate k v θ H w hv hθ hwp hD).1
  have hhLower := fixed_real_field_minor_normalized_lower F hF β hβ T k
    (fun r : R => r.1.val) (fun r => r.2.1 0) (fun r => (selection r).1 0)
    (fun r i => r.2.1 i.succ) (fun r i => (selection r).1 i.succ)
    (fun r => r.1.isLt.le) hneFormal scale v w0 wmin D rebate
    hscale hv hw0 hwmin hD hw hT hjoint' hb hs hh hα
  rw [← minor_specialization k w0 v θ w H T (fun i => ((β i : ℝ) : ℂ)) selection]
  exact hhLower

/-- Actual primitive heights can be used in the source's purely combinatorial
counting theorem; the natural input is not used as a rational denominator. -/
theorem actual_rowCount_normalized {m : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) (k : ℕ) (v θ : ℚ) (hv : 0 < v) (hθ : 0 < θ)
    (hheight : ∀ i, 2 ≤ primitiveMinpolyHeight (β i : ℝ)) :
    Filter.Tendsto (fun H : ℝ =>
      (Fintype.card (Row k (v : ℝ) (θ : ℝ) (primitiveWeights F β) H) : ℝ)/H^(m+1))
      Filter.atTop (nhds ((k : ℝ)*(θ : ℝ)^m/
        (((m+1).factorial : ℝ)*(v : ℝ)*∏ i, primitiveWeights F β i))) := by
  have he : OAI.PiExponent.MatrixArithmetic.logWeights
      (fun i => primitiveMinpolyHeight (β i : ℝ)) = primitiveWeights F β := rfl
  simpa only [OAI.PiExponent.MatrixCounting.rowCount, he] using
    OAI.PiExponent.MatrixCounting.tendsto_rowCount_normalized k v θ
      (fun i => primitiveMinpolyHeight (β i : ℝ)) hv hθ hheight

theorem actual_row_lowIndex_ratio {m : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) (k : ℕ) (v θ A : ℚ) (hv : 0 < v) (hθ : 0 < θ)
    (hA : 0 < A) (hheight : ∀ i, 2 ≤ primitiveMinpolyHeight (β i : ℝ)) :
    Filter.Tendsto (fun H : ℝ =>
      (Fintype.card (Row k (v : ℝ) (θ : ℝ) (primitiveWeights F β) H) : ℝ)/
        (H*(OAI.PiExponent.realWeightedSimplex (primitiveWeights F β) ((A : ℝ)*H)).card))
      Filter.atTop (nhds ((k : ℝ)*(θ : ℝ)^m/(((m : ℝ)+1)*(v : ℝ)*(A : ℝ)^m))) := by
  have he : OAI.PiExponent.MatrixArithmetic.logWeights
      (fun i => primitiveMinpolyHeight (β i : ℝ)) = primitiveWeights F β := rfl
  simpa only [OAI.PiExponent.MatrixCounting.rowCount,
    OAI.PiExponent.MatrixCounting.lowIndexCount, he] using
    OAI.PiExponent.MatrixCounting.tendsto_row_lowIndex_ratio k v θ A
      (fun i => primitiveMinpolyHeight (β i : ℝ)) hv hθ hA hheight

end FixedQuadratic.UpstreamPacketArithmetic
#check @FixedQuadratic.UpstreamPacketArithmetic.legal_packet_budgets
#print axioms FixedQuadratic.UpstreamPacketArithmetic.legal_packet_budgets
#check @FixedQuadratic.UpstreamPacketArithmetic.legal_packet_rebate
#print axioms FixedQuadratic.UpstreamPacketArithmetic.legal_packet_rebate
#check @FixedQuadratic.UpstreamPacketArithmetic.primitiveWeights
#print axioms FixedQuadratic.UpstreamPacketArithmetic.primitiveWeights
#check @FixedQuadratic.UpstreamPacketArithmetic.actual_selected_minor_lower
#print axioms FixedQuadratic.UpstreamPacketArithmetic.actual_selected_minor_lower
#check @FixedQuadratic.UpstreamPacketArithmetic.actual_rowCount_normalized
#print axioms FixedQuadratic.UpstreamPacketArithmetic.actual_rowCount_normalized
#check @FixedQuadratic.UpstreamPacketArithmetic.actual_row_lowIndex_ratio
#print axioms FixedQuadratic.UpstreamPacketArithmetic.actual_row_lowIndex_ratio
