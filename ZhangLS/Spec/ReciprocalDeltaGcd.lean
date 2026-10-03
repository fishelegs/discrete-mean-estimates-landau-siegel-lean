import ZhangLS.Spec.DeltaPairGcdReindex
import ZhangLS.Spec.AdditiveReciprocity
import ZhangLS.Spec.FixedModulusGcdBridge

/-! Exact arbitrary-complementary-modulus reciprocity and positive gcd
attachment. A=1 is Section7; A=D is the unaltered Section14 source phase.
All Q=A*p scales remain in the stated Delta absolute-convergence range. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def deltaReciprocalWeight (p m N : ℕ) : ℂ :=
  if hN : 0<N then
    letI : NeZero N := ⟨hN.ne'⟩
    ZMod.stdAddChar (-(m : ZMod N)*(p : ZMod N)⁻¹)
  else 0

lemma deltaReciprocalWeight_norm (p m : ℕ) {N : ℕ} (hN : 0<N) :
    ‖deltaReciprocalWeight p m N‖=1 := by
  letI : NeZero N := ⟨hN.ne'⟩
  simp only [deltaReciprocalWeight,dif_pos hN,ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- The source reciprocal phase loses the common gcd in numerator and
modulus. The fixed complementary modulus A remains exactly. -/
theorem deltaReciprocalWeight_gcd {A p : ℕ} (hA : 0<A)
    (d l k : ℕ+) (hp : p.Coprime (A*((d : ℕ)*(k : ℕ)))) :
    deltaReciprocalWeight p ((d : ℕ)*(l : ℕ)) (A*((d : ℕ)*(k : ℕ)))=
      deltaReciprocalWeight p (l : ℕ) (A*(k : ℕ)) := by
  have hmod : A*((d : ℕ)*(k : ℕ))=(d : ℕ)*(A*(k : ℕ)) := by ring
  rw [hmod] at hp ⊢
  have hAk : 0<A*(k : ℕ) := Nat.mul_pos hA k.property
  have hdk : 0<(d : ℕ)*(A*(k : ℕ)) := Nat.mul_pos d.property hAk
  letI : NeZero (d : ℕ) := ⟨d.property.ne'⟩
  letI : NeZero (A*(k : ℕ)) := ⟨hAk.ne'⟩
  simp only [deltaReciprocalWeight,dif_pos hdk,dif_pos hAk]
  exact fixedDGcd_inverse_phase_quotient hp (l : ℕ)

noncomputable def reciprocalDeltaGcdTerm (D A p : ℕ) (S : Finset ℕ)
    (κ a : ℕ → ℂ) (d l k : ℕ+) : ℂ :=
  if ((d : ℕ)*(k : ℕ))∈S then
    (d : ℂ)⁻¹*(a ((d : ℕ)*(k : ℕ))/(k : ℂ))*
      (κ ((d : ℕ)*(l : ℕ))*deltaReciprocalWeight p (l : ℕ) (A*(k : ℕ)))*
        lemma53PaperDelta D ((l : ℝ)/(((A : ℝ)*(p : ℝ))*(k : ℝ)))
  else 0

lemma reciprocalDelta_gcd_term_eq {D A p : ℕ} (hA : 0<A) (S : Finset ℕ)
    (κ a : ℕ → ℂ) (hp : ∀n∈S, p.Coprime (A*n)) (d l k : ℕ+) :
    deltaPairGcdTerm D ((A : ℝ)*(p : ℝ)) S κ a
      (fun m n => deltaReciprocalWeight p m (A*n)) d l k=
        reciprocalDeltaGcdTerm D A p S κ a d l k := by
  unfold deltaPairGcdTerm reciprocalDeltaGcdTerm
  split_ifs with hn
  · dsimp only
    rw [deltaReciprocalWeight_gcd hA d l k (hp _ hn)]
  · rfl

/-- Termwise source DeltaOne reciprocity. No condition is imposed on m. -/
theorem reciprocalDelta_source_term {D A p n : ℕ} [NeZero p]
    (hA : 0<A) (hn : 0<n) (hp : (A*n).Coprime p) (κ : ℕ → ℂ) (m : ℕ+) :
    κ (m : ℕ)*lemma53PaperDeltaOne D ((m : ℝ)/(((A : ℝ)*(p : ℝ))*(n : ℝ)))*
      ZMod.stdAddChar ((m : ZMod p)*((A*n : ℕ) : ZMod p)⁻¹)=
    κ (m : ℕ)*deltaReciprocalWeight p (m : ℕ) (A*n)*
      lemma53PaperDelta D ((m : ℝ)/(((A : ℝ)*(p : ℝ))*(n : ℝ))) := by
  have hAn : 0<A*n := Nat.mul_pos hA hn
  letI : NeZero (A*n) := ⟨hAn.ne'⟩
  have hr := additiveReciprocity_delta (D := D) hp (m : ℕ)
  have hscale : (((A*n : ℕ) : ℝ)*(p : ℝ))=((A : ℝ)*(p : ℝ))*(n : ℝ) := by push_cast; ring
  rw [hscale] at hr
  simp only [deltaReciprocalWeight,dif_pos hAn]
  calc
    _=κ (m : ℕ)*(lemma53PaperDeltaOne D ((m : ℝ)/(((A : ℝ)*(p : ℝ))*(n : ℝ)))*
      ZMod.stdAddChar ((m : ZMod p)*((A*n : ℕ) : ZMod p)⁻¹)) := by ring
    _=_ := by rw [hr]; ring

/-- The actual reciprocal gcd series converges jointly before the d,k,l
sum is formed. This is uniform in arbitrary short coefficients a. -/
theorem reciprocalDelta_gcd_summable {D A p : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hA : 0<A) (hp0 : 0<p)
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (κ a : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀m : ℕ, 0<m → ‖κ m‖≤B*(lemma34Tau 5 m : ℝ))
    (hp : ∀n∈S, p.Coprime (A*n))
    (hq : ∀n∈S, 1≤((A : ℝ)*(p : ℝ))*n ∧
      ((A : ℝ)*(p : ℝ))*n≤lemma23PaperP D^10) :
    Summable (fun i : positiveGcdIndex => reciprocalDeltaGcdTerm D A p S κ a i.1 i.2.val.1 i.2.val.2) := by
  have hQ : 0<(A : ℝ)*(p : ℝ) := mul_pos (by exact_mod_cast hA) (by exact_mod_cast hp0)
  have hs := deltaPair_gcd_summable hD hL hQ S hS κ a
    (fun m n => deltaReciprocalWeight p m (A*n)) hB hκ
    (fun n hn m hm => (deltaReciprocalWeight_norm p m (Nat.mul_pos hA (hS n hn))).le) hq
  exact hs.congr (fun i => reciprocalDelta_gcd_term_eq hA S κ a hp _ _ _)

/-- The original DeltaOne additive source equals the full literal gcd mean,
with exact A, p, d, k factors and all positive long indices. -/
theorem reciprocalDelta_source_gcd_tsum {D A p : ℕ} [NeZero p]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : 0<A)
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (κ a : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀m : ℕ, 0<m → ‖κ m‖≤B*(lemma34Tau 5 m : ℝ))
    (hp : ∀n∈S, p.Coprime (A*n))
    (hq : ∀n∈S, 1≤((A : ℝ)*(p : ℝ))*n ∧
      ((A : ℝ)*(p : ℝ))*n≤lemma23PaperP D^10) :
    (∑n∈S, (a n/(n : ℂ))*(∑'m : ℕ+,
      κ (m : ℕ)*lemma53PaperDeltaOne D ((m : ℝ)/(((A : ℝ)*(p : ℝ))*(n : ℝ)))*
        ZMod.stdAddChar ((m : ZMod p)*((A*n : ℕ) : ZMod p)⁻¹)))=
      ∑'d : ℕ+, ∑'k : ℕ+, ∑'l : ℕ+,
        if Nat.Coprime (l : ℕ) (k : ℕ) then reciprocalDeltaGcdTerm D A p S κ a d l k else 0 := by
  have hQ : 0<(A : ℝ)*(p : ℝ) := mul_pos (by exact_mod_cast hA)
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p))
  have hsource : (∑n∈S, (a n/(n : ℂ))*(∑'m : ℕ+,
      κ (m : ℕ)*lemma53PaperDeltaOne D ((m : ℝ)/(((A : ℝ)*(p : ℝ))*(n : ℝ)))*
        ZMod.stdAddChar ((m : ZMod p)*((A*n : ℕ) : ZMod p)⁻¹)))=
      ∑n∈S, (a n/(n : ℂ))*(∑'m : ℕ+, κ (m : ℕ)*deltaReciprocalWeight p (m : ℕ) (A*n)*
        lemma53PaperDelta D ((m : ℝ)/(((A : ℝ)*(p : ℝ))*n))) := by
    apply sum_congr rfl
    intro n hn
    congr 1
    apply tsum_congr
    exact fun m => reciprocalDelta_source_term hA (hS n hn) (hp n hn).symm κ m
  rw [hsource,deltaPair_gcd_nested_tsum hD hL hQ S hS κ a
    (fun m n => deltaReciprocalWeight p m (A*n)) hB hκ
    (fun n hn m hm => (deltaReciprocalWeight_norm p m (Nat.mul_pos hA (hS n hn))).le) hq]
  apply tsum_congr
  intro d
  apply tsum_congr
  intro k
  apply tsum_congr
  intro l
  simp only [reciprocalDelta_gcd_term_eq hA S κ a hp]

end ZhangLS.Spec
