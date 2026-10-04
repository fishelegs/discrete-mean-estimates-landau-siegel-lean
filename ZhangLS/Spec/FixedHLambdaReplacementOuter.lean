import ZhangLS.Spec.FixedHLambdaReplacement
import ZhangLS.Spec.Lemma32LocalL
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Actual character/totient weights and the literal L'(1,χ)²/B² scalar.
The replacement alone uses harmonic mass; it needs no arithmetic asymptotic. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHLambdaReplacement
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def outerSum {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ)
    (j : Fin 3) (K : ℝ → ℂ) : ℂ :=
  (LDerivAtOne χ)^2 / (Real.log (lemma23PaperP D):ℂ)^2 *
    ∑ n ∈ Icc 1 ⌊Real.exp ((201/400:ℝ)*Real.log (lemma23PaperP D))⌋₊,
      (‖χ.evalNat n‖:ℂ) * lemma83Lambda (lemma83PaperBeta D c) n
        (1-lemma83PaperBeta D c j) / (n.totient:ℂ) *
        K (Real.log n / Real.log (lemma23PaperP D))

noncomputable def baselineOuterSum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (K : ℝ → ℂ) : ℂ :=
  (LDerivAtOne χ)^2 / (Real.log (lemma23PaperP D):ℂ)^2 *
    ∑ n ∈ Icc 1 ⌊Real.exp ((201/400:ℝ)*Real.log (lemma23PaperP D))⌋₊,
      (‖χ.evalNat n‖:ℂ) * (n.totient:ℂ) / (n:ℂ)^2 *
        K (Real.log n / Real.log (lemma23PaperP D))

lemma compact_norm_bound {K : ℝ → ℂ} {M : ℝ} (hM : 0≤M)
    (hs : Function.support K⊆Icc (251/500:ℝ) (201/400:ℝ))
    (hK : ∀ t∈Icc (251/500:ℝ) (201/400:ℝ), ‖K t‖≤M) (t : ℝ) : ‖K t‖≤M := by
  by_cases ht : K t=0
  · simpa [ht] using hM
  · exact hK t (hs ht)

lemma cutoff_log {B : ℝ} {n : ℕ}
    (hn : n∈Finset.Icc 1 ⌊Real.exp ((201/400:ℝ)*B)⌋₊) :
    0<n ∧ Real.log n≤(201/400:ℝ)*B := by
  have hi := Finset.mem_Icc.mp hn
  refine ⟨hi.1,?_⟩
  have hnr : (n:ℝ)≤Real.exp ((201/400:ℝ)*B) :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mp hi.2
  simpa only [Real.log_exp] using Real.log_le_log (Nat.cast_pos.mpr hi.1) hnr

lemma cutoff_harmonic {B : ℝ} (hB : 1≤B) :
    (harmonic ⌊Real.exp ((201/400:ℝ)*B)⌋₊:ℝ)≤2*B := by
  have he : 1≤Real.exp ((201/400:ℝ)*B) := Real.one_le_exp_iff.mpr (by positivity)
  have hh := harmonic_floor_le_one_add_log _ he
  rw [Real.log_exp] at hh
  linarith

/-- Local cancellation is justified by the actual positive totient, including n=1. -/
lemma weighted_factor_error {A : ℂ} {n : ℕ} (hn : 0<n) {e : ℝ} (he : 0≤e)
    (h : ‖A-(((n.totient:ℝ)/(n:ℝ))^2:ℂ)‖≤((n.totient:ℝ)/(n:ℝ))^2*e) :
    ‖A/(n.totient:ℂ)-(n.totient:ℂ)/(n:ℂ)^2‖≤e*(n:ℝ)⁻¹ := by
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  have hp : 0<(n.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hpC : (n.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr hn).ne'
  have hx : A/(n.totient:ℂ)-(n.totient:ℂ)/(n:ℂ)^2 =
      (A-(((n.totient:ℝ)/(n:ℝ))^2:ℂ))/(n.totient:ℂ) := by
    push_cast
    field_simp
  rw [hx,norm_div,Complex.norm_natCast]
  calc
    _ ≤ (((n.totient:ℝ)/(n:ℝ))^2*e)/(n.totient:ℝ) :=
      div_le_div_of_nonneg_right h hp.le
    _ = ((n.totient:ℝ)/(n:ℝ)^2)*e := by field_simp
    _ ≤ ((n:ℝ)/(n:ℝ)^2)*e :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by exact_mod_cast Nat.totient_le n) (sq_nonneg _)) he
    _ = _ := by field_simp

lemma finite_weighted_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (A : ℕ → ℂ) (K : ℝ → ℂ) {B M e : ℝ} (hB : 1≤B) (hM : 0≤M) (he : 0≤e)
    (hK : ∀ t, ‖K t‖≤M)
    (hA : ∀ n∈Finset.Icc 1 ⌊Real.exp ((201/400:ℝ)*B)⌋₊,
      ‖A n-(((n.totient:ℝ)/(n:ℝ))^2:ℂ)‖≤((n.totient:ℝ)/(n:ℝ))^2*e) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊Real.exp ((201/400:ℝ)*B)⌋₊,
      (‖χ.evalNat n‖:ℂ)*A n/(n.totient:ℂ)*K (Real.log n/B)) -
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((201/400:ℝ)*B)⌋₊,
      (‖χ.evalNat n‖:ℂ)*(n.totient:ℂ)/(n:ℂ)^2*K (Real.log n/B)‖≤M*e*(2*B) := by
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((201/400:ℝ)*B)⌋₊, M*e*(n:ℝ)⁻¹ := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n hn
      have hn0 := (cutoff_log hn).1
      have hw := weighted_factor_error hn0 he (hA n hn)
      have hx : (‖χ.evalNat n‖:ℂ)*A n/(n.totient:ℂ)*K (Real.log n/B) -
          (‖χ.evalNat n‖:ℂ)*(n.totient:ℂ)/(n:ℂ)^2*K (Real.log n/B) =
          (‖χ.evalNat n‖:ℂ)*(A n/(n.totient:ℂ)-(n.totient:ℂ)/(n:ℂ)^2)*K (Real.log n/B) := by ring
      rw [hx,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      have hh := mul_le_mul
        (mul_le_mul (χ.evalNat_norm_le_one n) hw (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
        (hK (Real.log n/B)) (norm_nonneg _) (by positivity : 0≤1*(e*(n:ℝ)⁻¹))
      simpa [mul_comm,mul_left_comm,mul_assoc] using hh
    _ = M*e*(harmonic ⌊Real.exp ((201/400:ℝ)*B)⌋₊:ℝ) := by
      rw [←mul_sum,harmonic_eq_sum_Icc,Rat.cast_sum]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (cutoff_harmonic hB) (mul_nonneg hM he)

lemma scalar_bound {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D)
    (hL : 2≤lemma23PaperL D) {B : ℝ} (hB : 0<B) :
    ‖(LDerivAtOne χ)^2/(B:ℂ)^2‖≤(16*Real.exp 1)^2*lemma23PaperL D^4/B^2 := by
  have hd : ‖LDerivAtOne χ‖≤16*Real.exp 1*lemma23PaperL D^2 :=
    lemma32_actual_first_derivative_bound χ hD hL (s := 1) (by simp; positivity)
  rw [norm_div,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hh := pow_le_pow_left₀ (norm_nonneg _) hd 2
  convert hh using 1
  ring

/-- The complete actual weighted replacement at the original scalar
normalization, uniformly over every bounded compact K in the fixed-h window.
No assumption (A), prime exclusion or arithmetic norm envelope is needed. -/
theorem outer_error_uniform (c M : ℝ) (hc : 0<c) (hM : 0≤M) :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D≥D₀,
      ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 3, ∀ K : ℝ → ℂ,
      Function.support K⊆Set.Icc (251/500:ℝ) (201/400:ℝ) →
      (∀ t∈Set.Icc (251/500:ℝ) (201/400:ℝ), ‖K t‖≤M) →
      ‖outerSum χ c j K-baselineOuterSum χ K‖≤
        C*lemma23PaperL D^4*(1+Real.log (Real.log (lemma23PaperP D)))^2 /
          (Real.log (lemma23PaperP D))^2 := by
  obtain ⟨Cerr,hCerr,Derr,_,herr⟩ := paper_absolute_error_uniform c hc
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2≤D ∧ Derr≤D ∧ 100≤lemma23PaperL D from by
    filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop Derr,
      ht.eventually_ge_atTop 100] with D h2 hDerr hL
    exact ⟨h2,hDerr,hL⟩)
  refine ⟨2*(16*Real.exp 1)^2*Cerr*(M+1),by positivity,D₀,(hD₀ D₀ le_rfl).1,?_⟩
  intro D hD χ j K hs hK
  have hd := hD₀ D hD
  have hL : 100≤lemma23PaperL D := hd.2.2
  let B := Real.log (lemma23PaperP D)
  have hBp : 0<B := by dsimp [B,lemma23PaperP]; rw [Real.log_exp]; positivity
  have hB1 : 1≤B := by
    dsimp [B,lemma23PaperP]
    rw [Real.log_exp]
    exact one_le_pow₀ (by linarith only [hd.2.2] : 1≤lemma23PaperL D)
  let e := Cerr*(1+Real.log B)^2/B
  have he : 0≤e := by dsimp [e]; positivity
  have hKall : ∀ t, ‖K t‖≤M+1 := fun t =>
    (compact_norm_bound hM hs hK t).trans (by linarith)
  have hA : ∀ n∈Finset.Icc 1 ⌊Real.exp ((201/400:ℝ)*B)⌋₊,
      ‖lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j)-
        (((n.totient:ℝ)/(n:ℝ))^2:ℂ)‖≤((n.totient:ℝ)/(n:ℝ))^2*e := by
    intro n hn
    have hn' := cutoff_log hn
    exact herr D hd.2.1 j n hn'.1 hn'.2
  have hf := finite_weighted_error χ
    (fun n => lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j))
    K hB1 (by positivity : 0≤M+1) he hKall hA
  have hscalar := scalar_bound χ (by omega) (by linarith only [hd.2.2]) hBp
  unfold outerSum baselineOuterSum
  rw [←mul_sub,norm_mul]
  calc
    _ ≤ ((16*Real.exp 1)^2*lemma23PaperL D^4/B^2)*((M+1)*e*(2*B)) :=
      mul_le_mul hscalar hf (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [e,B]; field_simp

end ZhangLS.Spec.FixedHLambdaReplacement
