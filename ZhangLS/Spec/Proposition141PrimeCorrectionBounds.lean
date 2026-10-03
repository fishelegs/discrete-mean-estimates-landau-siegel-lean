import ZhangLS.Spec.Proposition141PrimeCorrectionSeries

/-! Both literal front Gauss corrections through the complete short n sum. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141PrimeSmallCorrection (D p:ℕ) (κ a:ℕ→ℂ) : ℂ :=
  ∑n∈proposition141Indices D,(a n/(n:ℂ))*
    ∑'m:ℕ,proposition141DeltaOneTerm D κ (fun m=>1-proposition141PrimePhase D p n m)
      1 ((D:ℝ)*(p:ℝ)*(n:ℝ)) m

noncomputable def proposition141PrimeDivisibleCorrection (D p:ℕ) (κ a:ℕ→ℂ) : ℂ :=
  ∑n∈proposition141Indices D,(a n/(n:ℂ))*
    ∑'j:ℕ,proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)) j

lemma proposition141_tau_five_prime {p:ℕ} (hp:p.Prime) : lemma34Tau 5 p=5 := by
  simpa using lemma34_tau_prime_power hp 4 1

lemma proposition141_prime_correction_scales {D p n:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) (hn:n∈proposition141Indices D) :
    1≤(D:ℝ)*(n:ℝ) ∧ (D:ℝ)*(n:ℝ)≤lemma23PaperP D^10 ∧
      1≤(D:ℝ)*(p:ℝ)*(n:ℝ) ∧ (D:ℝ)*(p:ℝ)*(n:ℝ)≤lemma23PaperP D^10 := by
  have hs := proposition141_principal_support_scales hD hL hmod (by simp : D=1*D)
    (by norm_num : 0<(1:ℕ)) hp hn
  have hp1:(1:ℝ)≤p := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.pos
  have hn1:(1:ℝ)≤n := by exact_mod_cast ((proposition141_mem_indices D n).mp hn).1
  have hD1:(1:ℝ)≤D := by exact_mod_cast (by omega : 1≤D)
  refine ⟨?_,?_,hs.2.1,hs.2.2.1⟩
  · nlinarith
  · have hh:(D:ℝ)*(n:ℝ)≤(D:ℝ)*(p:ℝ)*(n:ℝ) := by nlinarith
    exact hh.trans hs.2.2.1

/-- Genuine convergence of both source series, not a formal manipulation of tsums. -/
theorem proposition141_prime_correction_summable {D p n:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) (hn:n∈proposition141Indices D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ) :
    Summable (proposition141DeltaOneTerm D κ (fun m=>1-proposition141PrimePhase D p n m)
      1 ((D:ℝ)*(p:ℝ)*(n:ℝ))) ∧
    Summable (proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ))) := by
  have hs := proposition141_prime_correction_scales hD hL hmod hp hn
  have hpp := ((lemma56_mem_paper_primes D p).mp hp).1
  exact ⟨(proposition141_actual_deltaOne_weighted_sum hD hL hB hκ (by norm_num : (0:ℝ)≤2)
    (fun m _=>proposition141_prime_correction_weight_norm D p n m) (by norm_num : 0<(1:ℕ)) hs.2.2.1 hs.2.2.2).1,
    (proposition141_actual_deltaOne_weighted_sum hD hL hB hκ (by norm_num : (0:ℝ)≤1)
    (fun m _=>by simp) hpp.pos hs.1 hs.2.1).1⟩

/-- The literal +1 and p−1 correction, summed against actual a*(n)/n. -/
theorem proposition141_prime_small_correction_bound {D p:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) {Bκ Ba:ℝ} (hBκ:0≤Bκ) (hBa:0≤Ba)
    {κ a:ℕ→ℂ} (hκ:Proposition141KappaBound Bκ κ) (ha:Proposition141AdmissibleSequence D Ba a) :
    ‖proposition141PrimeSmallCorrection D p κ a‖≤
      2*tauDeltaAbsoluteConstant*Bκ*Ba*(D:ℝ)*(p:ℝ)*
        (proposition141Indices D).card*lemma23PaperL D^575 := by
  have hc := tauDelta_absolute_constant_pos.le
  have hpoint (n:ℕ) (hn:n∈proposition141Indices D) :
      ‖(a n/(n:ℂ))*(∑'m:ℕ,proposition141DeltaOneTerm D κ
        (fun m=>1-proposition141PrimePhase D p n m) 1 ((D:ℝ)*(p:ℝ)*(n:ℝ)) m)‖≤
      2*tauDeltaAbsoluteConstant*Bκ*Ba*(D:ℝ)*(p:ℝ)*lemma23PaperL D^575 := by
    have hs := proposition141_prime_correction_scales hD hL hmod hp hn
    have hnp := ((proposition141_mem_indices D n).mp hn).1
    have hnR:0<(n:ℝ) := by exact_mod_cast hnp
    have hb := (proposition141_actual_deltaOne_weighted_sum hD hL hBκ hκ (by norm_num : (0:ℝ)≤2)
      (fun m _=>proposition141_prime_correction_weight_norm D p n m)
      (by norm_num : 0<(1:ℕ)) hs.2.2.1 hs.2.2.2).2
    have ht:lemma34Tau 5 1=1 := (lemma34_tau_multiplicative 5).map_one
    rw [ht,Nat.cast_one,mul_one] at hb
    rw [norm_mul,norm_div,Complex.norm_natCast]
    calc
      _≤(Ba/(n:ℝ))*(2*tauDeltaAbsoluteConstant*Bκ*((D:ℝ)*(p:ℝ)*(n:ℝ))*lemma23PaperL D^575) := by
        gcongr
        exact ha.1 n hnp
      _=_ := by field_simp <;> ring
  unfold proposition141PrimeSmallCorrection
  apply ((norm_sum_le _ _).trans (sum_le_sum hpoint)).trans_eq
  simp only [sum_const,nsmul_eq_mul]
  ring

/-- Replacing m by p*j pays τ₅(p)=5 and removes p from the genuine scale. -/
theorem proposition141_prime_divisible_correction_bound {D p:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) {Bκ Ba:ℝ} (hBκ:0≤Bκ) (hBa:0≤Ba)
    {κ a:ℕ→ℂ} (hκ:Proposition141KappaBound Bκ κ) (ha:Proposition141AdmissibleSequence D Ba a) :
    ‖proposition141PrimeDivisibleCorrection D p κ a‖≤
      5*tauDeltaAbsoluteConstant*Bκ*Ba*(D:ℝ)*
        (proposition141Indices D).card*lemma23PaperL D^575 := by
  have hc := tauDelta_absolute_constant_pos.le
  have hpp := ((lemma56_mem_paper_primes D p).mp hp).1
  have hpoint (n:ℕ) (hn:n∈proposition141Indices D) :
      ‖(a n/(n:ℂ))*(∑'j:ℕ,proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)) j)‖≤
      5*tauDeltaAbsoluteConstant*Bκ*Ba*(D:ℝ)*lemma23PaperL D^575 := by
    have hs := proposition141_prime_correction_scales hD hL hmod hp hn
    have hnp := ((proposition141_mem_indices D n).mp hn).1
    have hnR:0<(n:ℝ) := by exact_mod_cast hnp
    have hb := (proposition141_actual_deltaOne_weighted_sum (w:=fun _=>1) hD hL hBκ hκ (by norm_num : (0:ℝ)≤1)
      (fun m _=>by simp) hpp.pos hs.1 hs.2.1).2
    rw [proposition141_tau_five_prime hpp,Nat.cast_ofNat,one_mul] at hb
    rw [norm_mul,norm_div,Complex.norm_natCast]
    calc
      _≤(Ba/(n:ℝ))*(tauDeltaAbsoluteConstant*Bκ*5*((D:ℝ)*(n:ℝ))*lemma23PaperL D^575) := by
        gcongr
        exact ha.1 n hnp
      _=_ := by field_simp <;> ring
  unfold proposition141PrimeDivisibleCorrection
  apply ((norm_sum_le _ _).trans (sum_le_sum hpoint)).trans_eq
  simp only [sum_const,nsmul_eq_mul]
  ring

end ZhangLS.Spec
