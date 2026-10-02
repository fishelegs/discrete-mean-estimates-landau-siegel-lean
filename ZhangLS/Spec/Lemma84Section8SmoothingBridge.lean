import ZhangLS.Spec.Lemma84Section8BoundaryObligations
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

/-- Exactly the paper's κ₁/κ₂ coefficients, with μ choosing (P₁,β₆) or (P₂,β₇).
Only positive integer arguments are used by the actual arithmetic sums. -/
noncomputable def lemma84Section8Kappa (D μ n : ℕ) : ℂ :=
  if (n:ℝ)<lemma84Section8Cutoff D μ then
    ((1-Real.log n/Real.log (lemma84Section8Cutoff D μ):ℝ):ℂ)*
      ((lemma84Section8Cutoff D μ/n:ℝ):ℂ)^(lemma82SmoothingBeta D μ)
  else 0

/-- The logarithmic normalization is exact, with the true source coefficient. -/
theorem lemma84_section8_kappa_normalization {D μ n m : ℕ}
    (hn : 0<n) (hm : 0<m) (hQ : 1<lemma84Section8Cutoff D μ)
    (hnm : ((n*m:ℕ):ℝ)<lemma84Section8Cutoff D μ) :
    lemma84Section8Kappa D μ (n*m)=
      (((lemma84Section8Cutoff D μ/n)/m:ℝ):ℂ)^(lemma82SmoothingBeta D μ)*
        (Real.log ((lemma84Section8Cutoff D μ/n)/m):ℂ)/
          (Real.log (lemma84Section8Cutoff D μ):ℂ) := by
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hn
  have hm0 : 0<(m:ℝ) := by exact_mod_cast hm
  have hQ0 : 0<lemma84Section8Cutoff D μ := by linarith
  have hlog : Real.log (lemma84Section8Cutoff D μ)≠0 := (Real.log_pos hQ).ne'
  have he : (lemma84Section8Cutoff D μ/n)/m=lemma84Section8Cutoff D μ/(n*m:ℕ) := by
    push_cast
    ring
  rw [lemma84Section8Kappa,if_pos hnm,he,
    Real.log_div hQ0.ne' (by exact_mod_cast (Nat.mul_pos hn hm).ne')]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hlog]
  <;> ring

/-- Our normalized first factor is literally the source κ inner sum, not an
arbitrary function assumed to have the right envelope. -/
theorem lemma84_section8_first_smoothing_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ n : ℕ) (hn : 0<n)
    (hQ : 1<lemma84Section8Cutoff D μ) (hnQ : (n:ℝ)<lemma84Section8Cutoff D μ) :
    lemma84Section8First χ c j μ n=
      ∑ m∈lemma82StrictCutoff (lemma84Section8Cutoff D μ/n),
        χ.evalNat m/(m:ℂ)^(1-lemma82PaperBeta D c j)*lemma84Section8Kappa D μ (n*m) := by
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hn
  have hx0 : 0≤lemma84Section8Cutoff D μ/n := by positivity [lemma84_section8_cutoff_pos D μ]
  rw [lemma84Section8First,if_pos hnQ,lemma82ShiftedSum,sum_div]
  apply sum_congr rfl
  intro m hm
  have hh := (lemma82_mem_strictCutoff hx0 m).mp hm
  have hnm : ((n*m:ℕ):ℝ)<lemma84Section8Cutoff D μ := by
    have hh' := (lt_div_iff₀ hn0).mp hh.2
    push_cast
    nlinarith only [hh']
  rw [lemma84_section8_kappa_normalization hn hh.1 hQ hnm]
  ring

/-- The second normalized factor uses the negative smoothing shift exactly. -/
theorem lemma84_section8_smoothing_beta_same (D μ : ℕ) :
    lemma84SmoothingBeta D μ=lemma82SmoothingBeta D μ := rfl

theorem lemma84_section8_paper_beta_same (D : ℕ) (c : ℝ) (j : Fin 3) :
    lemma82PaperBeta D c j=lemma83PaperBeta D c j := rfl

lemma lemma84_section8_conj_smoothing (D μ : ℕ) :
    star (lemma82SmoothingBeta D μ)=-lemma84SmoothingBeta D μ := by
  unfold lemma82SmoothingBeta lemma84SmoothingBeta
  split_ifs <;> apply Complex.ext <;> simp <;> ring

lemma lemma84_section8_conj_smoothing_power (D μ : ℕ) {x : ℝ} (hx : 0<x) :
    star ((x:ℂ)^(lemma82SmoothingBeta D μ))=(x:ℂ)^(-lemma84SmoothingBeta D μ) := by
  have ha : (x:ℂ).arg≠Real.pi := by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  have hh := (Complex.cpow_conj (x:ℂ) (lemma82SmoothingBeta D μ) ha).symm
  simpa only [Complex.conj_ofReal,show (starRingEnd ℂ) (lemma82SmoothingBeta D μ)=
    -lemma84SmoothingBeta D μ from lemma84_section8_conj_smoothing D μ] using hh

/-- The actual ξ factor is precisely the conjugate-source-κ inner sum. -/
theorem lemma84_section8_second_smoothing_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (hd : 0<d) (hr : 0<r)
    (hQ : 1<lemma84Section8Cutoff D μ) (hnQ : ((d*r:ℕ):ℝ)<lemma84Section8Cutoff D μ) :
    lemma84Section8Second χ c j μ d r=
      ∑ n∈lemma84StrictCutoff (lemma84Section8Cutoff D μ/(d*r:ℕ)),
        χ.evalNat n*star (lemma84Section8Kappa D μ (d*r*n))*
          lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ) := by
  have hdr : 0<d*r := Nat.mul_pos hd hr
  have hdr0 : 0<((d*r:ℕ):ℝ) := by exact_mod_cast hdr
  have hx0 : 0<lemma84Section8Cutoff D μ/(d*r:ℕ) :=
    div_pos (lemma84_section8_cutoff_pos D μ) hdr0
  rw [lemma84Section8Second,if_pos hnQ,lemma84XiSum,sum_div]
  apply sum_congr rfl
  intro n hn
  have hh := (lemma84_mem_strictCutoff hx0.le n).mp hn
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hh.1
  have hprod : ((d*r*n:ℕ):ℝ)<lemma84Section8Cutoff D μ := by
    have hh' := (lt_div_iff₀ hdr0).mp hh.2
    simpa only [Nat.cast_mul,mul_comm,mul_left_comm,mul_assoc] using hh'
  rw [lemma84_section8_kappa_normalization hdr hh.1 hQ hprod]
  simp only [map_div₀,map_mul,Complex.star_def,Complex.conj_ofReal]
  rw [show (starRingEnd ℂ) ((((lemma84Section8Cutoff D μ/(d*r:ℕ))/n:ℝ):ℂ)^
      (lemma82SmoothingBeta D μ))=
      (((lemma84Section8Cutoff D μ/(d*r:ℕ))/n:ℝ):ℂ)^(-lemma84SmoothingBeta D μ) from
    lemma84_section8_conj_smoothing_power D μ (div_pos hx0 hn0)]
  ring

lemma lemma84_section8_small_strict_cutoff {x : ℝ} (hx : 0≤x) (hx1 : x≤1) :
    lemma82StrictCutoff x=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hh := (lemma82_mem_strictCutoff hx n).mp hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hh.1
  linarith

noncomputable def lemma84Section8FirstSource {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ n : ℕ) : ℂ :=
  ∑ m∈lemma82StrictCutoff (lemma84Section8Cutoff D μ/n),
    χ.evalNat m/(m:ℂ)^(1-lemma82PaperBeta D c j)*lemma84Section8Kappa D μ (n*m)

noncomputable def lemma84Section8SecondSource {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) : ℂ :=
  ∑ n∈lemma84StrictCutoff (lemma84Section8Cutoff D μ/(d*r:ℕ)),
    χ.evalNat n*star (lemma84Section8Kappa D μ (d*r*n))*
      lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ)

theorem lemma84_section8_first_source_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ n : ℕ) (hn : 0<n) (hQ : 1<lemma84Section8Cutoff D μ) :
    lemma84Section8First χ c j μ n=lemma84Section8FirstSource χ c j μ n := by
  by_cases hnQ : (n:ℝ)<lemma84Section8Cutoff D μ
  · exact lemma84_section8_first_smoothing_exact χ c j μ n hn hQ hnQ
  · have hx : 0≤lemma84Section8Cutoff D μ/n := by positivity [lemma84_section8_cutoff_pos D μ]
    have hx1 : lemma84Section8Cutoff D μ/n≤1 := (div_le_one (by exact_mod_cast hn)).mpr (le_of_not_gt hnQ)
    rw [lemma84Section8FirstSource,lemma84_section8_small_strict_cutoff hx hx1,sum_empty]
    exact lemma84_section8_first_zero_at_cutoff χ c j μ n (le_of_not_gt hnQ)

theorem lemma84_section8_second_source_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (hd : 0<d) (hr : 0<r)
    (hQ : 1<lemma84Section8Cutoff D μ) :
    lemma84Section8Second χ c j μ d r=lemma84Section8SecondSource χ c j μ d r := by
  by_cases hnQ : ((d*r:ℕ):ℝ)<lemma84Section8Cutoff D μ
  · exact lemma84_section8_second_smoothing_exact χ c j μ d r hd hr hQ hnQ
  · have hn : 0<d*r := Nat.mul_pos hd hr
    have hx : 0≤lemma84Section8Cutoff D μ/(d*r:ℕ) := by positivity [lemma84_section8_cutoff_pos D μ]
    have hx1 : lemma84Section8Cutoff D μ/(d*r:ℕ)≤1 := (div_le_one (by exact_mod_cast hn)).mpr (le_of_not_gt hnQ)
    have hempty : lemma84StrictCutoff (lemma84Section8Cutoff D μ/(d*r:ℕ))=∅ :=
      lemma84_section8_small_strict_cutoff hx hx1
    rw [lemma84Section8SecondSource,hempty,sum_empty]
    exact lemma84_section8_second_zero_at_cutoff χ c j μ d r (le_of_not_gt hnQ)

/-- The actual κ,κ-bar version of the Section 8 S_j display. Each finite cutoff
is exactly the support of its source coefficient for positive indices. -/
noncomputable def lemma84Section8SourceSum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) : ℂ :=
  ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
    (lemma84Section8FirstSource χ c j 6 (a.1*a.2)+
      lemma84Section8Iota*lemma84Section8FirstSource χ c j 7 (a.1*a.2))*
    (lemma84Section8SecondSource χ c j 6 a.1 a.2+
      star lemma84Section8Iota*lemma84Section8SecondSource χ c j 7 a.1 a.2)

/-- Exact normalization of the full original smoothed-coefficient expression. -/
theorem lemma84_section8_raw_source_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (h6 : 1<lemma84Section8Cutoff D 6)
    (h7 : 1<lemma84Section8Cutoff D 7) :
    lemma84Section8Raw χ c j=lemma84Section8SourceSum χ c j := by
  unfold lemma84Section8Raw lemma84Section8SourceSum
  apply sum_congr rfl
  intro a ha
  obtain ⟨hd,hr,_⟩ := (lemma84_section8_pairs_exact D a.1 a.2).mp ha
  rw [lemma84Section8FirstCombined,
    lemma84_section8_first_source_exact χ c j 6 _ (Nat.mul_pos hd hr) h6,
    lemma84_section8_first_source_exact χ c j 7 _ (Nat.mul_pos hd hr) h7,
    lemma84_section8_second_source_exact χ c j 6 _ _ hd hr h6,
    lemma84_section8_second_source_exact χ c j 7 _ _ hd hr h7]

/-- Final actual-source version, with no assumed weighted-error or normalization
bridge. The sole unprocessed change is the explicitly defined boundary term. -/
theorem lemma84_section8_source_repaired_interior_little_o :
    ∀ c : ℝ, 0<c → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ j : Fin 3,
          ‖lemma84Section8SourceSum χ c j-lemma84Section8Hybrid χ c j‖≤ε*lemma44PaperAlpha D := by
  intro c hc ε hε
  obtain ⟨Di,hDi,hi⟩ := lemma84_section8_repaired_interior_little_o c hc ε hε
  obtain ⟨Dq,hDq⟩ := eventually_atTop.mp lemma84_section8_cutoffs_eventually
  refine ⟨max Di Dq,le_trans hDi (le_max_left _ _),?_⟩
  intro D hD χ hA j
  have hq := hDq D (le_trans (le_max_right _ _) hD)
  rw [←lemma84_section8_raw_source_exact χ c j (hq.2.2 6).1 (hq.2.2 7).1]
  exact hi D (le_trans (le_max_left _ _) hD) χ hA j

/-- The actual source weight |χ(d)| |μ(r)χ(r)| is the coefficient used above. -/
theorem lemma84_section8_original_weight_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) :
    lemma84Section8Weight χ c j d r=
      (((‖χ.evalNat d‖*‖(ArithmeticFunction.moebius r:ℂ)*χ.evalNat r‖):ℝ):ℂ)*
        lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j)/
          ((d:ℂ)*(r:ℂ)*(Nat.totient r:ℂ)) := by
  have hm : χ.evalNat (d*r)=χ.evalNat d*χ.evalNat r := by
    simp only [RealPrimitiveCharacter.evalNat,Nat.cast_mul,map_mul]
  rw [lemma84Section8Weight,hm,norm_mul,norm_mul,Complex.norm_intCast]
  push_cast
  ring

end ZhangLS.Spec
