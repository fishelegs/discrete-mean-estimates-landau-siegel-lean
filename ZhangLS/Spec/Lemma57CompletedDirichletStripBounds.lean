import ZhangLS.Spec.Lemma57GammaFactorGrowth

/-!
# Uniform strip bounds for completed Dirichlet L-functions

The completed Dirichlet L-function is a finite combination of completed even
and odd Hurwitz zeta functions. The even terms use weak FE pairs; the odd
terms use strong FE pairs. Both Mellin transforms are uniformly bounded on
closed vertical strips.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set
open scoped Real Topology

set_option maxHeartbeats 800000 in
/-- The Mellin transform attached to a strong functional-equation pair is
uniformly bounded on each closed vertical strip. -/
theorem StrongFEPair.exists_norm_Λ_le_on_verticalStrip
    (P : StrongFEPair ℂ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ), a ≤ σ → σ ≤ b →
      ‖P.Λ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  let g : ℝ → ℂ := P.f
  let majorant : ℝ → ℝ := fun x =>
    (x ^ (a - 1) + x ^ (b - 1)) * ‖g x‖
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    P.hf_int.aestronglyMeasurable
  have haConv : MellinConvergent g (a : ℂ) :=
    (P.hasMellin (a : ℂ)).1
  have hbConv : MellinConvergent g (b : ℂ) :=
    (P.hasMellin (b : ℂ)).1
  have haInt : IntegrableOn (fun x : ℝ => x ^ (a - 1) * ‖g x‖) (Ioi 0) :=
    (mellin_convergent_iff_norm subset_rfl measurableSet_Ioi hgmeas).mp haConv
  have hbInt : IntegrableOn (fun x : ℝ => x ^ (b - 1) * ‖g x‖) (Ioi 0) :=
    (mellin_convergent_iff_norm subset_rfl measurableSet_Ioi hgmeas).mp hbConv
  have hmajorant : IntegrableOn majorant (Ioi 0) := by
    dsimp [majorant]
    simpa only [add_mul] using haInt.add hbInt
  refine ⟨∫ x : ℝ in Ioi 0, majorant x, ?_, ?_⟩
  · apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact mul_nonneg (add_nonneg (Real.rpow_nonneg hx.le _)
      (Real.rpow_nonneg hx.le _)) (norm_nonneg _)
  · intro σ t hσa hσb
    let s : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hsConv : MellinConvergent g s := (P.hasMellin s).1
    have hsInt : IntegrableOn
        (fun x : ℝ => ‖(x : ℂ) ^ (s - 1) • g x‖) (Ioi 0) :=
      hsConv.norm
    change ‖mellin g s‖ ≤ ∫ x : ℝ in Ioi 0, majorant x
    rw [mellin]
    calc
      ‖∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) • g x‖ ≤
          ∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (s - 1) • g x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ in Ioi 0, majorant x := by
        apply MeasureTheory.integral_mono_ae hsInt hmajorant
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
        have hx0 : 0 < x := hx
        rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : (s - 1).re = σ - 1 := by simp [s]
        rw [hre]
        dsimp [majorant]
        have hpow : x ^ (σ - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
          rcases le_total x 1 with hx1 | h1x
          · exact (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)).trans
              (le_add_of_nonneg_right (Real.rpow_nonneg hx0.le _))
          · exact (Real.rpow_le_rpow_of_exponent_le h1x (by linarith)).trans
              (le_add_of_nonneg_left (Real.rpow_nonneg hx0.le _))
        exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)

/-- Every pole-corrected even Hurwitz term is uniformly bounded on the
critical strip used by the contour. -/
theorem exists_completedHurwitzZetaEven₀_norm_le_criticalStrip
    (a : UnitAddCircle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖HurwitzZeta.completedHurwitzZetaEven₀ a
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  rcases WeakFEPair.exists_norm_Λ₀_le_on_verticalStrip
      (HurwitzZeta.hurwitzEvenFEPair a)
      ((1 : ℝ) / 4) ((3 : ℝ) / 4) with ⟨C, hC, hbound⟩
  refine ⟨C / 2, by positivity, ?_⟩
  intro σ t hσ0 hσ1
  have h := hbound (σ / 2) (t / 2) (by linarith) (by linarith)
  rw [HurwitzZeta.completedHurwitzZetaEven₀]
  change ‖(HurwitzZeta.hurwitzEvenFEPair a).Λ₀
      (((σ : ℂ) + (t : ℂ) * I) / 2) / 2‖ ≤ C / 2
  rw [norm_div, norm_ofNat]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
  convert h using 1
  push_cast
  ring_nf

/-- Every completed odd Hurwitz term is uniformly bounded on the same
critical strip. -/
theorem exists_completedHurwitzZetaOdd_norm_le_criticalStrip
    (a : UnitAddCircle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖HurwitzZeta.completedHurwitzZetaOdd a
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  rcases StrongFEPair.exists_norm_Λ_le_on_verticalStrip
      (HurwitzZeta.hurwitzOddFEPair a)
      ((3 : ℝ) / 4) ((5 : ℝ) / 4) with ⟨C, hC, hbound⟩
  refine ⟨C / 2, by positivity, ?_⟩
  intro σ t hσ0 hσ1
  have h := hbound ((σ + 1) / 2) (t / 2) (by linarith) (by linarith)
  rw [HurwitzZeta.completedHurwitzZetaOdd]
  change ‖(HurwitzZeta.hurwitzOddFEPair a).Λ
      ((((σ : ℂ) + (t : ℂ) * I) + 1) / 2) / 2‖ ≤ C / 2
  rw [norm_div, norm_ofNat]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
  convert h using 1
  push_cast
  ring_nf

set_option maxHeartbeats 800000 in
/-- The completed Dirichlet L-function of any finite coefficient function is
uniformly bounded on the critical strip, after its two possible rational
pole terms have been removed. -/
theorem exists_ZMod_completedLFunction₀_norm_le_criticalStrip
    {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖ZMod.completedLFunction₀ Φ
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  classical
  have he : ∀ j : ZMod N, ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j)
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
    fun j => exists_completedHurwitzZetaEven₀_norm_le_criticalStrip _
  have ho : ∀ j : ZMod N, ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j)
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
    fun j => exists_completedHurwitzZetaOdd_norm_le_criticalStrip _
  choose Ce hCe using he
  choose Co hCo using ho
  let Me : ℝ := ∑ j : ZMod N, ‖Φ j‖ * Ce j
  let Mo : ℝ := ∑ j : ZMod N, ‖Φ j‖ * Co j
  have hMe : 0 ≤ Me := Finset.sum_nonneg fun j _ =>
    mul_nonneg (norm_nonneg _) (hCe j).1
  have hMo : 0 ≤ Mo := Finset.sum_nonneg fun j _ =>
    mul_nonneg (norm_nonneg _) (hCo j).1
  refine ⟨Me + Mo, add_nonneg hMe hMo, ?_⟩
  intro σ t hσ0 hσ1
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hn : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hnpos : (0 : ℝ) < N := by linarith
  have hpow : ‖(N : ℂ) ^ (-s)‖ ≤ 1 := by
    change ‖((N : ℝ) : ℂ) ^ (-s)‖ ≤ 1
    rw [norm_cpow_eq_rpow_re_of_pos hnpos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn (by simp [s]; linarith)
  have hEven : ‖∑ j : ZMod N,
      Φ j * HurwitzZeta.completedHurwitzZetaEven₀
        (ZMod.toAddCircle j) s‖ ≤ Me := by
    calc
      ‖∑ j : ZMod N, Φ j * HurwitzZeta.completedHurwitzZetaEven₀
          (ZMod.toAddCircle j) s‖ ≤
        ∑ j : ZMod N, ‖Φ j * HurwitzZeta.completedHurwitzZetaEven₀
          (ZMod.toAddCircle j) s‖ := norm_sum_le _ _
      _ ≤ Me := by
        dsimp [Me]
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          ((hCe j).2 σ t hσ0 hσ1) (norm_nonneg _)
  have hOdd : ‖∑ j : ZMod N,
      Φ j * HurwitzZeta.completedHurwitzZetaOdd
        (ZMod.toAddCircle j) s‖ ≤ Mo := by
    calc
      ‖∑ j : ZMod N, Φ j * HurwitzZeta.completedHurwitzZetaOdd
          (ZMod.toAddCircle j) s‖ ≤
        ∑ j : ZMod N, ‖Φ j * HurwitzZeta.completedHurwitzZetaOdd
          (ZMod.toAddCircle j) s‖ := norm_sum_le _ _
      _ ≤ Mo := by
        dsimp [Mo]
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          ((hCo j).2 σ t hσ0 hσ1) (norm_nonneg _)
  change ‖(N : ℂ) ^ (-s) * (∑ j : ZMod N,
      Φ j * HurwitzZeta.completedHurwitzZetaEven₀
        (ZMod.toAddCircle j) s) +
      (N : ℂ) ^ (-s) * (∑ j : ZMod N,
      Φ j * HurwitzZeta.completedHurwitzZetaOdd
        (ZMod.toAddCircle j) s)‖ ≤ Me + Mo
  calc
    _ ≤ ‖(N : ℂ) ^ (-s)‖ * ‖∑ j : ZMod N,
          Φ j * HurwitzZeta.completedHurwitzZetaEven₀
            (ZMod.toAddCircle j) s‖ +
        ‖(N : ℂ) ^ (-s)‖ * ‖∑ j : ZMod N,
          Φ j * HurwitzZeta.completedHurwitzZetaOdd
            (ZMod.toAddCircle j) s‖ := by
      simpa only [norm_mul] using norm_add_le
        ((N : ℂ) ^ (-s) * ∑ j : ZMod N,
          Φ j * HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s)
        ((N : ℂ) ^ (-s) * ∑ j : ZMod N,
          Φ j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s)
    _ ≤ Me + Mo := by
      have hE : ‖(N : ℂ) ^ (-s)‖ * ‖∑ j : ZMod N,
          Φ j * HurwitzZeta.completedHurwitzZetaEven₀
            (ZMod.toAddCircle j) s‖ ≤ Me := by
        calc
          _ ≤ 1 * ‖∑ j : ZMod N,
              Φ j * HurwitzZeta.completedHurwitzZetaEven₀
                (ZMod.toAddCircle j) s‖ :=
            mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
          _ ≤ Me := by simpa using hEven
      have hO : ‖(N : ℂ) ^ (-s)‖ * ‖∑ j : ZMod N,
          Φ j * HurwitzZeta.completedHurwitzZetaOdd
            (ZMod.toAddCircle j) s‖ ≤ Mo := by
        calc
          _ ≤ 1 * ‖∑ j : ZMod N,
              Φ j * HurwitzZeta.completedHurwitzZetaOdd
                (ZMod.toAddCircle j) s‖ :=
            mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
          _ ≤ Mo := by simpa using hOdd
      exact add_le_add hE hO

/-- A primitive character of modulus greater than one has a completed
Dirichlet L-function uniformly bounded on the critical strip. -/
theorem exists_completedDirichletL_norm_le_criticalStrip
    {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖DirichletCharacter.completedLFunction χ.chi
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  have hzero : χ.chi (0 : ZMod D) = 0 :=
    χ.chi.map_zero' (by omega)
  have hsum : ∑ j : ZMod D, χ.chi j = 0 :=
    χ.chi.sum_eq_zero_of_ne_one (χ.nontrivial_of_one_lt_modulus hD)
  rcases exists_ZMod_completedLFunction₀_norm_le_criticalStrip
      (fun j : ZMod D => χ.chi j) with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro σ t hσ0 hσ1
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have heq : DirichletCharacter.completedLFunction χ.chi s =
      ZMod.completedLFunction₀ (fun j : ZMod D => χ.chi j) s := by
    rw [DirichletCharacter.completedLFunction,
      ZMod.completedLFunction_eq]
    simp [hzero, hsum]
  rw [heq]
  exact hbound σ t hσ0 hσ1

end ZhangLS.Spec
