import ZhangLS.Spec.AppendixBRoughRhoEuler
import ZhangLS.Spec.AppendixBRoughReplacementB1
import ZhangLS.Spec.Lemma83

/-! Appendix B.2: an exact finite union bound followed by the genuine uniform
absolute Euler-product estimate. The original q<D^4 and n<P endpoints are kept. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- Removing the entire p-part retains every prime power. -/
theorem appendixB_prime_multiple_mass (β : ℂ) {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ n∈(Icc 1 N).filter (fun n => p∣n),appendixBRhoMass β n)≤
      (‖lemma151Rho β p‖/((p : ℝ)-1))*(∑ m∈Icc 1 N,appendixBRhoMass β m) := by
  let A := (Icc 1 N).filter (fun n => p∣n)
  let pairOf : ℕ→ℕ×ℕ := fun n => (n.factorization p-1,n/p^(n.factorization p))
  let weight : ℕ×ℕ→ℝ := fun a => appendixBRhoMass β (p^(a.1+1))*appendixBRhoMass β a.2
  have hpos (n) (hn : n∈A) : 0<n := (mem_Icc.mp (mem_filter.mp hn).1).1
  have he (n) (hn : n∈A) : 1≤n.factorization p :=
    (hp.dvd_iff_one_le_factorization (hpos n hn).ne').mp (mem_filter.mp hn).2
  have hprod (n) (hn : n∈A) : p^((pairOf n).1+1)*(pairOf n).2=n := by
    dsimp [pairOf]
    rw [Nat.sub_add_cancel (he n hn)]
    exact Nat.ordProj_mul_ordCompl_eq_self n p
  have hinj : Set.InjOn pairOf A := by
    intro n hn m hm hnm
    rw [←hprod n hn,←hprod m hm,hnm]
  have hsub : A.image pairOf ⊆ range N ×ˢ Icc 1 N := by
    intro a ha
    obtain ⟨n,hn,rfl⟩ := mem_image.mp ha
    have hnN := (mem_Icc.mp (mem_filter.mp hn).1).2
    refine mem_product.mpr ⟨mem_range.mpr ?_,mem_Icc.mpr ⟨?_,?_⟩⟩
    · exact lt_of_le_of_lt (Nat.sub_le _ _) ((Nat.factorization_lt p (hpos n hn).ne').trans_le hnN)
    · exact Nat.ordCompl_pos p (hpos n hn).ne'
    · exact (Nat.ordCompl_le n p).trans hnN
  have hweight (n) (hn : n∈A) : appendixBRhoMass β n=weight (pairOf n) := by
    have hc := (Nat.coprime_ordCompl hp (hpos n hn).ne').pow_left ((pairOf n).1+1)
    change appendixBRhoMass β n=
      appendixBRhoMass β (p^((pairOf n).1+1))*appendixBRhoMass β (n/p^(n.factorization p))
    rw [←appendixB_rho_mass_mul β hc,hprod n hn]
  have hnonneg : ∀ a,0≤weight a := fun a =>
    mul_nonneg (appendixB_rho_mass_nonneg β _) (appendixB_rho_mass_nonneg β _)
  have htail : (∑ k∈range N,appendixBRhoMass β (p^(k+1)))≤‖lemma151Rho β p‖/((p : ℝ)-1) := by
    rw [←(appendixB_rho_local_tail β hp).2]
    exact (appendixB_rho_local_tail β hp).1.sum_le_tsum _
      (fun n _ => appendixB_rho_mass_nonneg β _)
  calc
    _ = ∑ a∈A.image pairOf,weight a := by rw [sum_image hinj]; exact sum_congr rfl hweight
    _ ≤ ∑ a∈range N ×ˢ Icc 1 N,weight a :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; exact hnonneg _)
    _ = (∑ k∈range N,appendixBRhoMass β (p^(k+1)))*
        (∑ m∈Icc 1 N,appendixBRhoMass β m) := by
      dsimp only [weight]
      rw [Finset.sum_product' (range N) (Icc 1 N)
        (fun k m : ℕ => appendixBRhoMass β (p^(k+1))*appendixBRhoMass β m),←sum_mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right htail (sum_nonneg (fun n _ => appendixB_rho_mass_nonneg β n))

/-- Failure of original Q-coprimality is witnessed by a prime strictly below D^4. -/
lemma appendixB_nonrough_small_prime {D n : ℕ} (hn : ¬n.Coprime (lemma151Q D)) :
    ∃ p∈(range (D^4)).filter Nat.Prime,p∣n := by
  by_contra! h
  apply hn
  unfold lemma151Q
  apply Nat.Coprime.prod_right
  intro p hp
  exact ((mem_filter.mp hp).2.coprime_iff_not_dvd.mpr (h p hp)).symm

/-- Finite union bound, with exact prime-power local tails. -/
theorem appendixB_nonrough_mass_finite (β : ℂ) (D N : ℕ) :
    (∑ n∈(Icc 1 N).filter (fun n => ¬n.Coprime (lemma151Q D)),appendixBRhoMass β n)≤
      (∑ p∈(range (D^4)).filter Nat.Prime,‖lemma151Rho β p‖/((p : ℝ)-1))*
        (∑ n∈Icc 1 N,appendixBRhoMass β n) := by
  have hind (p n : ℕ) : 0≤(if p∣n then appendixBRhoMass β n else 0) := by
    split_ifs <;> first | exact appendixB_rho_mass_nonneg β n | exact le_rfl
  calc
    _ ≤ ∑ n∈Icc 1 N,∑ p∈(range (D^4)).filter Nat.Prime,
        if p∣n then appendixBRhoMass β n else 0 := by
      rw [sum_filter]
      apply sum_le_sum
      intro n hn
      by_cases h : n.Coprime (lemma151Q D)
      · rw [if_neg (not_not_intro h)]
        exact sum_nonneg (fun p _ => hind p n)
      · rw [if_pos h]
        obtain ⟨p,hp,hpn⟩ := appendixB_nonrough_small_prime h
        calc
          _ = (if p∣n then appendixBRhoMass β n else 0) := by simp [hpn]
          _ ≤ _ := single_le_sum (fun p _ => hind p n) hp
    _ = ∑ p∈(range (D^4)).filter Nat.Prime,
        ∑ n∈(Icc 1 N).filter (fun n => p∣n),appendixBRhoMass β n := by
      rw [sum_comm]; simp only [sum_filter]
    _ ≤ ∑ p∈(range (D^4)).filter Nat.Prime,
        (‖lemma151Rho β p‖/((p : ℝ)-1))*(∑ n∈Icc 1 N,appendixBRhoMass β n) :=
      sum_le_sum (fun p hp => appendixB_prime_multiple_mass β (mem_filter.mp hp).2 N)
    _ = _ := (sum_mul _ _ _).symm

/-- Explicit B.2 before specializing finite-D parameters. -/
theorem appendixB_nonrough_mass_exp_bound {β : ℂ} (hβ : β.re=0) (D N : ℕ) :
    (∑ n∈(Icc 1 N).filter (fun n => ¬n.Coprime (lemma151Q D)),appendixBRhoMass β n)≤
      (2*‖β‖*Real.log 4*(2+4*lemma23PaperL D))*
        Real.exp (2*‖β‖*Real.log 4*(2+Real.log (N : ℝ))) := by
  have hsmall : (∑ p∈(range (D^4)).filter Nat.Prime,
      ‖lemma151Rho β p‖/((p : ℝ)-1))≤2*‖β‖*Real.log 4*(2+4*lemma23PaperL D) := by
    calc
      _ ≤ ∑ p∈(range (D^4)).filter Nat.Prime,2*‖β‖*Real.log (p : ℝ)/(p : ℝ) :=
        sum_le_sum (fun p hp => appendixB_rho_local_excess hβ (mem_filter.mp hp).2)
      _ = 2*‖β‖*(∑ p∈(range (D^4)).filter Nat.Prime,Real.log (p : ℝ)/(p : ℝ)) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ 2*‖β‖*(Real.log 4*(2+Real.log (D^4 : ℕ))) :=
        mul_le_mul_of_nonneg_left (appendixB_prime_log_mass_strict (D^4)) (by positivity)
      _ = _ := by rw [Nat.cast_pow,Real.log_pow]; unfold lemma23PaperL; ring
  have hsmall0 : 0≤2*‖β‖*Real.log 4*(2+4*lemma23PaperL D) :=
    (sum_nonneg (fun p hp => by
      have hp1 : (1 : ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
      positivity)).trans hsmall
  exact (appendixB_nonrough_mass_finite β D N).trans
    (mul_le_mul hsmall (appendixB_rho_mass_exp_bound hβ N)
      (sum_nonneg (fun n _ => appendixB_rho_mass_nonneg β n)) hsmall0)

noncomputable def appendixBRhoGlobalConstant : ℝ := Real.exp (18*Real.pi*Real.log 4)
noncomputable def appendixBRoughRemovalConstant : ℝ :=
  36*Real.pi*Real.log 4*appendixBRhoGlobalConstant

lemma appendixB_rho_global_constant_pos : 0<appendixBRhoGlobalConstant := Real.exp_pos _
lemma appendixB_rough_removal_constant_pos : 0<appendixBRoughRemovalConstant := by
  unfold appendixBRoughRemovalConstant
  positivity [Real.pi_pos,appendixB_rho_global_constant_pos]

/-- The true alpha/log(P) identity; this makes the Euler product uniformly bounded. -/
lemma appendixB_replacement_alpha_scale {D : ℕ} (hL : 0<lemma23PaperL D) :
    lemma44PaperAlpha D*lemma23PaperL D^9=Real.pi := by
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  exact div_mul_cancel₀ _ (pow_ne_zero _ hL.ne')

/-- The original scale gives a uniform pointwise rho norm, with all finite-D
shift corrections retained through the actual beta norm hypothesis. -/
theorem appendixB_original_rho_norm {D n : ℕ} {β : ℂ}
    (hL : 0<lemma23PaperL D) (hn : 0<n) (hnP : (n : ℝ)≤lemma23PaperP D)
    (hβre : β.re=0) (hβ : ‖β‖≤3*lemma44PaperAlpha D) :
    ‖lemma151Rho β n‖≤Real.exp (3*Real.pi) := by
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP; rw [Real.log_exp]; positivity [Real.pi_pos]
  have hlog : Real.log (n : ℝ)≤lemma23PaperL D^9 := by
    simpa only [lemma23PaperP,Real.log_exp] using
      Real.log_le_log (Nat.cast_pos.mpr hn) hnP
  have hnonneg := Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ)≤n)
  apply (appendixB_rho_norm_exp_log hβre hn.ne').trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (3*lemma44PaperAlpha D)*lemma23PaperL D^9 :=
      mul_le_mul hβ hlog hnonneg (by positivity)
    _ = _ := by rw [mul_assoc,appendixB_replacement_alpha_scale hL]

lemma appendixB_original_mass_exponent {D N : ℕ} {β : ℂ}
    (hL : 1≤lemma23PaperL D) (hN : 1≤N) (hNP : (N : ℝ)≤lemma23PaperP D)
    (hβ : ‖β‖≤3*lemma44PaperAlpha D) :
    2*‖β‖*Real.log 4*(2+Real.log (N : ℝ))≤18*Real.pi*Real.log 4 := by
  have hl : 0<lemma23PaperL D := by linarith
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP; rw [Real.log_exp]; positivity [Real.pi_pos]
  have hlogN : Real.log (N : ℝ)≤lemma23PaperL D^9 := by
    simpa only [lemma23PaperP,Real.log_exp] using Real.log_le_log (Nat.cast_pos.mpr (by omega : 0<N)) hNP
  have hNlog : 0≤Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hpow := one_le_pow₀ hL (n := 9)
  have hid := appendixB_replacement_alpha_scale hl
  have hsmall : ‖β‖*(2+Real.log (N : ℝ))≤9*Real.pi := by
    calc
      _ ≤ (3*lemma44PaperAlpha D)*(3*lemma23PaperL D^9) :=
        mul_le_mul hβ (by linarith) (by linarith) (by positivity)
      _ = _ := by nlinarith only [hid]
  have hlog4 : 0≤Real.log 4 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hsmall hlog4]

/-- Global absolute rho mass is uniformly bounded up to the closed P endpoint. -/
theorem appendixB_original_rho_mass {D N : ℕ} {β : ℂ}
    (hL : 1≤lemma23PaperL D) (hN : 1≤N) (hNP : (N : ℝ)≤lemma23PaperP D)
    (hβre : β.re=0) (hβ : ‖β‖≤3*lemma44PaperAlpha D) :
    (∑ n∈Icc 1 N,appendixBRhoMass β n)≤appendixBRhoGlobalConstant :=
  (appendixB_rho_mass_exp_bound hβre N).trans
    (Real.exp_le_exp.mpr (appendixB_original_mass_exponent hL hN hNP hβ))

/-- The required original L^-8 rate, with no discarded prime, prime power,
ramification condition, or guessed limiting shift. -/
theorem appendixB_original_B2_explicit {D N : ℕ} {β : ℂ}
    (hL : 1≤lemma23PaperL D) (hN : 1≤N) (hNP : (N : ℝ)≤lemma23PaperP D)
    (hβre : β.re=0) (hβ : ‖β‖≤3*lemma44PaperAlpha D) :
    (∑ n∈(Icc 1 N).filter (fun n => ¬n.Coprime (lemma151Q D)),appendixBRhoMass β n)≤
      appendixBRoughRemovalConstant*lemma23PaperL D^(-8 : ℤ) := by
  have hl : 0<lemma23PaperL D := by linarith
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP; rw [Real.log_exp]; positivity [Real.pi_pos]
  have hscale : lemma44PaperAlpha D*lemma23PaperL D=Real.pi*lemma23PaperL D^(-8 : ℤ) := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    simp only [zpow_neg,zpow_ofNat]
    field_simp [hl.ne']
    <;> ring
  have hlocal : 2*‖β‖*Real.log 4*(2+4*lemma23PaperL D)≤
      36*Real.pi*Real.log 4*lemma23PaperL D^(-8 : ℤ) := by
    have hh : ‖β‖*(2+4*lemma23PaperL D)≤18*(lemma44PaperAlpha D*lemma23PaperL D) := by
      calc
        _ ≤ (3*lemma44PaperAlpha D)*(6*lemma23PaperL D) :=
          mul_le_mul hβ (by linarith) (by positivity) (by positivity)
        _ = _ := by ring
    rw [hscale] at hh
    nlinarith only [mul_le_mul_of_nonneg_right hh (by positivity : 0≤Real.log 4)]
  have he := Real.exp_le_exp.mpr (appendixB_original_mass_exponent hL hN hNP hβ)
  calc
    _ ≤ (2*‖β‖*Real.log 4*(2+4*lemma23PaperL D))*
        Real.exp (2*‖β‖*Real.log 4*(2+Real.log (N : ℝ))) :=
      appendixB_nonrough_mass_exp_bound hβre D N
    _ ≤ (36*Real.pi*Real.log 4*lemma23PaperL D^(-8 : ℤ))*appendixBRhoGlobalConstant :=
      mul_le_mul hlocal he (Real.exp_pos _).le (by positivity [Real.pi_pos])
    _ = _ := by unfold appendixBRoughRemovalConstant; ring

/-- Original finite-D shifts, uniformly in j=1,2,3 after a threshold depending
only on the fixed source c. This is B.2 and does not invoke assumption (A). -/
theorem appendixB_original_B2_uniform (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, ∀ D : ℕ,D₀≤D → ∀ j : Fin 3, ∀ N : ℕ,1≤N →
      (N : ℝ)≤lemma23PaperP D →
      (∑ n∈(Icc 1 N).filter (fun n => ¬n.Coprime (lemma151Q D)),
        appendixBRhoMass (lemma83PaperBeta D c j) n)≤
      appendixBRoughRemovalConstant*lemma23PaperL D^(-8 : ℤ) := by
  obtain ⟨M,hM,hsmall⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨K,hK⟩ := lemma31_exponential_absorption_threshold
  refine ⟨max M K,?_⟩
  intro D hD j N hN hNP
  have hh := hK D ((le_max_right _ _).trans hD)
  exact appendixB_original_B2_explicit (by linarith [hh.2.1]) hN hNP
    (lemma83_beta_re D c j) (lemma83_paper_beta_norm hh.2.1 hc
      (hsmall D ((le_max_left _ _).trans hD)) j)

end ZhangLS.Spec
