import ZhangLS.Spec.Proposition26ChiHarmonic
import ZhangLS.Spec.Proposition71Objects

/-! Finite multiplicative samples and the literal χ-twisted coefficient
sequence used in the new Section 11 norm argument. The variation condition
is a profile condition; it does not assume an arithmetic or zero mean. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex ComplexConjugate Finset
open scoped Classical

def Proposition26VariationBound (w : ℕ→ℂ) (V : ℝ) : Prop :=
  0≤V ∧ ∀ q N : ℕ, 0<q →
    ‖w (q*((N-1)+1))‖+
      (∑ i∈range (N-1), ‖w (q*(i+2))-w (q*(i+1))‖)≤V

lemma proposition26_variation_norm_bound {w : ℕ→ℂ} {V : ℝ}
    (hw : Proposition26VariationBound w V) {n : ℕ} (hn : 0<n) : ‖w n‖≤V := by
  simpa using hw.2 n 0 hn

lemma proposition26_conjugate_variation {w : ℕ→ℂ} {V : ℝ}
    (hw : Proposition26VariationBound w V) :
    Proposition26VariationBound (fun n => conj (w n)) V := by
  refine ⟨hw.1,?_⟩
  intro q N hq
  simpa only [← map_sub,Complex.norm_conj] using hw.2 q N hq

noncomputable def proposition26TwistedCoefficient {D : ℕ}
    (χ : RealPrimitiveCharacter D) (v : ℝ) (w : ℕ→ℂ) (n : ℕ) : ℂ :=
  if n=0 then 0 else χ.evalNat n*(n:ℂ)^(-I*(v:ℂ))*w n

lemma proposition26_twisted_coefficient_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (v : ℝ) {w : ℕ→ℂ} {V : ℝ} (hw : Proposition26VariationBound w V) (n : ℕ) :
    ‖proposition26TwistedCoefficient χ v w n‖≤V := by
  by_cases hn : n=0
  · simp only [proposition26TwistedCoefficient,if_pos hn,norm_zero]
    exact hw.1
  have hnp := Nat.pos_of_ne_zero hn
  have hp : ‖(n:ℂ)^(-I*(v:ℂ))‖=1 := by
    rw [Complex.norm_natCast_cpow_of_pos hnp]
    simp
  simp only [proposition26TwistedCoefficient,if_neg hn,norm_mul,hp,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one n)).trans
    (proposition26_variation_norm_bound hw hnp)

lemma proposition26_twisted_coefficient_admissible {D : ℕ}
    (χ : RealPrimitiveCharacter D) (v : ℝ) {w : ℕ→ℂ} {V : ℝ}
    (hw : Proposition26VariationBound w V)
    (hsupport : ∀ n : ℕ, lemma81Cutoff D≤(n:ℝ) → w n=0) :
    Lemma81AdmissibleSequence D V (proposition26TwistedCoefficient χ v w) := by
  refine ⟨proposition26_twisted_coefficient_norm χ v hw,?_⟩
  intro n hn
  simp [proposition26TwistedCoefficient,hsupport n hn]

lemma proposition26_twisted_coefficient_conjugate {D : ℕ}
    (χ : RealPrimitiveCharacter D) (v : ℝ) (w : ℕ→ℂ) :
    lemma81ConjugateSequence (proposition26TwistedCoefficient χ v w) =
      proposition26TwistedCoefficient χ (-v) (fun n => conj (w n)) := by
  funext n
  by_cases hn : n=0
  · simp [lemma81ConjugateSequence,proposition26TwistedCoefficient,hn]
  have harg : (n:ℂ).arg≠Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have hp : conj ((n:ℂ)^(-I*(v:ℂ)))=(n:ℂ)^(-I*((-v:ℝ):ℂ)) := by
    have hh := (Complex.cpow_conj (n:ℂ) (-I*(v:ℂ)) harg).symm
    simp only [map_natCast] at hh
    rw [hh]
    congr 1
    simp
  have hchi : conj (χ.evalNat n)=χ.evalNat n := by
    simpa only [RealPrimitiveCharacter.evalNat] using χ.conj_eval (n:ZMod D)
  simp only [lemma81ConjugateSequence,proposition26TwistedCoefficient,if_neg hn,map_mul,hchi,hp]

lemma proposition26_sum_Icc_eq_range (f : ℕ→ℂ) (N : ℕ) :
    (∑ n∈Icc 1 N,f n)=∑ i∈range N,f (i+1) := by
  symm
  rw [range_eq_Ico,Finset.sum_Ico_add' f 0 N (c:=1)]
  simp only [Finset.Ico_add_one_right_eq_Icc,zero_add]


/-- The actual χ harmonic sum with a profile sampled on any positive
multiplicative progression qn. -/
theorem proposition26_profile_harmonic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 8≤lemma23PaperL D) {s : ℂ}
    (hs : s.re=1) (hnorm : ‖s‖≤(D:ℝ)) {w : ℕ→ℂ} {V : ℝ}
    (hw : Proposition26VariationBound w V) {q : ℕ} (hq : 0<q) (N : ℕ) :
    ‖∑ n∈Icc 1 N,w (q*n)*(χ.evalNat n*(n:ℂ)^(-s))‖ ≤
      ((14*Real.exp 16+2)*lemma23PaperL D)*V := by
  rw [proposition26_sum_Icc_eq_range]
  have hh := proposition26_chi_harmonic_variation χ hD hL hs hnorm N
    (fun i => w (q*(i+1)))
  apply hh.trans
  exact mul_le_mul_of_nonneg_left (by simpa [Nat.add_assoc] using hw.2 q N hq) (by positivity)

lemma proposition26_twisted_first_term {D : ℕ} (χ : RealPrimitiveCharacter D)
    (v : ℝ) (w : ℕ→ℂ) (β : ℂ) {q m : ℕ} (hq : 0<q) (hm : 0<m) :
    proposition26TwistedCoefficient χ v w (q*m)/(m:ℂ)^(1-β) =
      (χ.evalNat q*(q:ℂ)^(-I*(v:ℂ))) *
        (w (q*m)*(χ.evalNat m*(m:ℂ)^(-(1-β+I*(v:ℂ))))) := by
  have hmn : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have he : χ.evalNat (q*m)=χ.evalNat q*χ.evalNat m := by
    simp [RealPrimitiveCharacter.evalNat,Nat.cast_mul,map_mul]
  have hp : (m:ℂ)^(-I*(v:ℂ))/(m:ℂ)^(1-β)=
      (m:ℂ)^(-(1-β+I*(v:ℂ))) := by
    rw [← Complex.cpow_sub _ _ hmn]
    congr 1
    ring
  rw [proposition26TwistedCoefficient,if_neg (Nat.mul_ne_zero hq.ne' hm.ne'),he,Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  calc
    _ = (χ.evalNat q*(q:ℂ)^(-I*(v:ℂ)))*
        (w (q*m)*(χ.evalNat m*((m:ℂ)^(-I*(v:ℂ))/(m:ℂ)^(1-β)))) := by ring
    _ = _ := by rw [hp]

/-- The actual first arithmetic inner sum, retaining its χ(q) factor and
allowing all finite cutoffs. The only profile input is explicit variation. -/
theorem proposition26_twisted_first_inner {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 8≤lemma23PaperL D) (v : ℝ) {w : ℕ→ℂ} {V : ℝ}
    (hw : Proposition26VariationBound w V) (β : ℂ) (hβ : β.re=0)
    (hs : ‖1-β+I*(v:ℂ)‖≤(D:ℝ)) {q : ℕ} (hq : 0<q) (N : ℕ) :
    ‖∑ m∈Icc 1 N,proposition26TwistedCoefficient χ v w (q*m)/(m:ℂ)^(1-β)‖ ≤
      ‖χ.evalNat q‖*((14*Real.exp 16+2)*lemma23PaperL D)*V := by
  have he : (∑ m∈Icc 1 N,proposition26TwistedCoefficient χ v w (q*m)/(m:ℂ)^(1-β))=
      (χ.evalNat q*(q:ℂ)^(-I*(v:ℂ))) *
        (∑ i∈range N,w (q*(i+1))*(χ.evalNat (i+1)*((i+1:ℕ):ℂ)^(-(1-β+I*(v:ℂ))))) := by
    rw [proposition26_sum_Icc_eq_range,Finset.mul_sum]
    apply sum_congr rfl
    intro i hi
    exact proposition26_twisted_first_term χ v w β hq (Nat.succ_pos i)
  have hre : (1-β+I*(v:ℂ)).re=1 := by simp [hβ]
  have hh := proposition26_chi_harmonic_variation χ hD hL hre hs N
    (fun i => w (q*(i+1)))
  have hvar := hw.2 q N hq
  have hK : 0≤(14*Real.exp 16+2)*lemma23PaperL D := by positivity
  have hb : ‖∑ i∈range N,w (q*(i+1))*
      (χ.evalNat (i+1)*((i+1:ℕ):ℂ)^(-(1-β+I*(v:ℂ))))‖ ≤
        ((14*Real.exp 16+2)*lemma23PaperL D)*V := by
    exact hh.trans (mul_le_mul_of_nonneg_left (by simpa [Nat.add_assoc] using hvar) hK)
  have hp : ‖(q:ℂ)^(-I*(v:ℂ))‖=1 := by rw [Complex.norm_natCast_cpow_of_pos hq]; simp
  rw [he,norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)

end ZhangLS.Spec
