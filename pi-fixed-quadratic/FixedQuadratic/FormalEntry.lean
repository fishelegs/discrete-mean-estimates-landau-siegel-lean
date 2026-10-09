import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic
import FixedQuadratic.MinorBudget

namespace FixedQuadratic

noncomputable def timeLift {R : Type*} [CommRing R] {m : ℕ} (G : Polynomial R) :
    MvPolynomial (Fin (m+1)) R :=
  G.eval₂ MvPolynomial.C (MvPolynomial.X 0)

theorem timeLift_split {R : Type*} [CommRing R] {m : ℕ} (G : Polynomial R) :
    MvPolynomial.finSuccEquiv R m (timeLift G) = G.map MvPolynomial.C := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [timeLift, Polynomial.eval₂_add, map_add] at *
    rw [hp, hq, Polynomial.map_add]
  | monomial n a =>
    simp [timeLift, Polynomial.eval₂_monomial,
      Polynomial.map_monomial, Polynomial.C_mul_X_pow_eq_monomial, MvPolynomial.finSuccEquiv_apply]

theorem timeLift_degree {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ}
    (G : Polynomial R) (i : Fin m) : (timeLift G).degreeOf i.succ = 0 := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [timeLift, Polynomial.eval₂_add] at *
    apply Nat.eq_zero_of_le_zero
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    simpa using (max_le hp.le hq.le)
  | monomial n a =>
    simp only [timeLift, Polynomial.eval₂_monomial]
    apply Nat.eq_zero_of_le_zero
    apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
    simp [MvPolynomial.degreeOf_X_pow_of_ne, Fin.succ_ne_zero]

/-- The exact binomial-product entry, with time as the zero-th variable and
formal centers as the successor variables. No rational approximation is used. -/
noncomputable def formalEntry {R : Type*} [CommRing R] {m : ℕ}
    (c : Fin m → R) (G : Fin m → Polynomial R)
    (s h : ℕ) (b a : Fin m → ℕ) : MvPolynomial (Fin m) R :=
  MvPolynomial.C (∏ i, ((a i).choose (b i) : R)) *
    (MvPolynomial.finSuccEquiv R m
      ((1 + MvPolynomial.X 0)^h * ∏ i,
        (MvPolynomial.C (c i)*MvPolynomial.X i.succ + timeLift (G i))^(a i-b i))).coeff s

/-- Specialization is precisely formula (3.1), including the logarithm
polynomials. Choosing c_i=2*j*I gives the desired complex centers. -/
theorem formalEntry_split {R : Type*} [CommRing R] {m : ℕ}
    (c : Fin m → R) (G : Fin m → Polynomial R)
    (s h : ℕ) (b a : Fin m → ℕ) :
    formalEntry c G s h b a = MvPolynomial.C (∏ i, ((a i).choose (b i) : R)) *
      (((1+Polynomial.X)^h * ∏ i,
        (Polynomial.C (MvPolynomial.C (c i)*MvPolynomial.X i)+
          (G i).map MvPolynomial.C)^(a i-b i)).coeff s) := by
  have hC (r : R) : MvPolynomial.finSuccEquiv R m (MvPolynomial.C r) =
      Polynomial.C (MvPolynomial.C r) := by simp [MvPolynomial.finSuccEquiv_apply]
  simp [formalEntry, map_mul, map_prod, map_pow, hC, timeLift_split,
    MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]

theorem formalEntry_eval {R : Type*} [CommRing R] {m : ℕ}
    (c x : Fin m → R) (G : Fin m → Polynomial R)
    (s h : ℕ) (b a : Fin m → ℕ) :
    MvPolynomial.eval x (formalEntry c G s h b a) =
      (∏ i, ((a i).choose (b i) : R)) *
        (((1+Polynomial.X)^h * ∏ i, (Polynomial.C (c i*x i)+G i)^(a i-b i)).coeff s) := by
  classical
  unfold formalEntry
  rw [map_mul, MvPolynomial.eval_C]
  congr 1
  rw [← Polynomial.coeff_map]
  congr 1
  have hC (r : R) : MvPolynomial.finSuccEquiv R m (MvPolynomial.C r) =
      Polynomial.C (MvPolynomial.C r) := by simp [MvPolynomial.finSuccEquiv_apply]
  have hEval : (MvPolynomial.eval x).comp (MvPolynomial.C : R →+* MvPolynomial (Fin m) R) =
      RingHom.id R := by ext r; simp
  simp [map_mul, map_prod, map_pow, hC, Polynomial.map_map, hEval, Polynomial.map_id,
    Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.map_pow, MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ, timeLift_split]

theorem formalEntry_zero_of_incompatible {R : Type*} [CommRing R] {m : ℕ}
    (c : Fin m → R) (G : Fin m → Polynomial R)
    (s h : ℕ) (b a : Fin m → ℕ) (hab : ¬ ∀ i, b i ≤ a i) :
    formalEntry c G s h b a = 0 := by
  classical
  push Not at hab
  obtain ⟨i, hi⟩ := hab
  unfold formalEntry
  have hp : (∏ j, ((a j).choose (b j) : R)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt hi])
  rw [hp, map_zero, zero_mul]

theorem formalEntry_degree {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ}
    (c : Fin m → R) (G : Fin m → Polynomial R)
    (s h : ℕ) (b a : Fin m → ℕ) (i : Fin m) :
    (formalEntry c G s h b a).degreeOf i ≤ a i-b i := by
  classical
  unfold formalEntry
  apply (MvPolynomial.degreeOf_mul_le i _ _).trans
  simp only [MvPolynomial.degreeOf_C, zero_add]
  apply (MvPolynomial.degreeOf_coeff_finSuccEquiv _ i s).trans
  apply (MvPolynomial.degreeOf_mul_le i.succ _ _).trans
  have htime : ((1 + MvPolynomial.X 0 : MvPolynomial (Fin (m+1)) R)^h).degreeOf i.succ = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply (MvPolynomial.degreeOf_pow_le _ _ _).trans
    have hd : (1 + MvPolynomial.X 0 : MvPolynomial (Fin (m+1)) R).degreeOf i.succ ≤ 0 := by
      apply (MvPolynomial.degreeOf_add_le _ _ _).trans
      simp [MvPolynomial.degreeOf_X_of_ne, Fin.succ_ne_zero]
    simpa only [mul_zero] using Nat.mul_le_mul_left h hd
  rw [htime, zero_add]
  apply (MvPolynomial.degreeOf_prod_le _ Finset.univ _).trans
  calc
    _ ≤ ∑ j, (a j-b j)*(if i=j then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      apply (MvPolynomial.degreeOf_pow_le _ _ _).trans
      apply Nat.mul_le_mul_left
      apply (MvPolynomial.degreeOf_add_le _ _ _).trans
      apply max_le
      · apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
        simp [MvPolynomial.degreeOf_X, Fin.succ_inj]
      · rw [timeLift_degree]
        split_ifs <;> omega
    _ = a i-b i := by simp

/-- The generic determinant budget is now instantiated for the actual formal
entry formula, rather than leaving its entry degree/zero hypotheses open. -/
theorem formal_minor_degree {R ι : Type*} [CommRing R] [Nontrivial R]
    [Fintype ι] [DecidableEq ι] {m : ℕ}
    (c : ι → Fin m → R) (G : Fin m → Polynomial R)
    (s h : ι → ℕ) (b a : ι → Fin m → ℕ) (i : Fin m) :
    (Matrix.det (fun r k => formalEntry (c r) G (s r) (h k) (b r) (a k))).degreeOf i ≤
      (∑ k, a k i) - ∑ r, b r i := by
  apply det_degreeOf_le _ a b
  · intro r k hab
    exact formalEntry_zero_of_incompatible _ _ _ _ _ _ hab
  · intro r k j
    exact formalEntry_degree _ _ _ _ _ _ j

end FixedQuadratic
