import ZhangLS.Spec.QuotientSourceRate
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

-- Expanded ORIGINAL source, complete original weights, and FULL infinite-l sigma.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ)
    {Ba : ℝ} {a : ℕ→ℂ} (ha : Proposition141AdmissibleSequence D Ba a)
    (hD : 1<D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
      (∑D₁∈D.divisors, ∑'d : ℕ+, ∑'k : ℕ+,
        ∑i : primitiveConductorFamilyIndex ((D/D₁)*(k:ℕ)),
          if (k:ℕ).Coprime D₁ ∧ 1 < i.1.val ∧
            (∀hDN : D∣(D/D₁)*(k:ℕ),
              i.2.val.changeLevel (Nat.mem_divisors.mp i.1.property).1 ≠ χ.chi.changeLevel hDN) then
            ‖a ((d:ℕ)*(k:ℕ))‖ *
              (Real.sqrt (i.1.val:ℝ)/((d:ℕ)*(k:ℕ)*(((D/D₁)*(k:ℕ)).totient:ℝ))) *
              ‖∑'l : ℕ, proposition141SigmaTerm χ i.2.val β κ D₁ d ((D/D₁)*(k:ℕ)/i.1.val) l‖
          else 0) ≤
    ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
      (∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
        ∑r∈proposition141SourceSmallModuli D D₁ (D/D₁) d h a,
          ‖a (d*(r*h/(D/D₁)))‖*((D/D₁:ℕ):ℝ)*
            ((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
            ∑θ∈proposition141SmallPrimitiveFamily χ h r,
              ‖∑'l : ℕ, proposition141SigmaTerm χ θ β κ D₁ d h l‖)+
    ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
      (∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
        ∑j∈range (proposition141DyadicBlockCount D),
          ∑r∈proposition141SourceLargeModuli D₁ (D/D₁) d h (proposition141DyadicScale D j) a,
            ‖a (d*(h*r/(D/D₁)))‖*((D/D₁:ℕ):ℝ)*
              ((d:ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
              ∑θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive),
                ‖∑'l : ℕ, proposition141SigmaTerm χ θ β κ D₁ d h l‖) :=
  quotientSource_original_normalized_le_complete_conductor χ β κ ha hD hmod

-- Expanded exact quotient source has both original exclusions, with no gcd(h,r) assumption.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ)
    {Ba : ℝ} {a : ℕ→ℂ} (ha : Proposition141AdmissibleSequence D Ba a)
    (hD : 1<D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
      (∑D₁∈D.divisors, ∑'d : ℕ+, ∑'r : ℕ+,
        ∑'h : {h : ℕ+ // D/D₁∣(r:ℕ)*(h:ℕ)},
          ∑θ : {θ : DirichletCharacter ℂ (r:ℕ) // θ.IsPrimitive},
            if ((r:ℕ)*(h.val:ℕ)/(D/D₁)).Coprime D₁ ∧ 1<(r:ℕ) ∧
              (∀hDN : D∣(r:ℕ)*(h.val:ℕ),
                θ.val.changeLevel ((r:ℕ).dvd_mul_right (h.val:ℕ)) ≠ χ.chi.changeLevel hDN) then
              ‖a ((d:ℕ)*((r:ℕ)*(h.val:ℕ)/(D/D₁)))‖ *
                (((D/D₁:ℕ):ℝ)/((d:ℕ)*(h.val:ℕ)*(((r:ℕ)*(h.val:ℕ)).totient:ℝ)*Real.sqrt (r:ℝ))) *
                ‖∑'l : ℕ, proposition141SigmaTerm χ θ.val β κ D₁ d h.val l‖
            else 0) ≤ proposition141CompleteConductorMajorant χ β κ a :=
  quotientSource_normalized_target_le_complete_conductor χ β κ ha hD hmod

-- Simultaneously noncoprime r,h and noncoprime D₁,D₂ remain allowed by exact source data.
example : 12=2*6 ∧ 6∣3*6 ∧ (3*6/6).Coprime 2 ∧
    ¬(3:ℕ).Coprime 6 ∧ ¬(2:ℕ).Coprime 6 := by norm_num

example (d : ℕ) : Real.sqrt (3:ℝ)/((d:ℝ)*3*(Nat.totient 18:ℝ)) =
    (6:ℝ)/((d:ℝ)*6*(Nat.totient 18:ℝ)*Real.sqrt (3:ℝ)) := by
  simpa using quotientConductor_weight (D₂:=6) (d:=d) (k:=3) (r:=3) (h:=6)
    (by norm_num) (by norm_num) (by norm_num)

-- Original coefficient support is closed at 2P₄, also after transport.
example {D D₂ : ℕ} (hD₂ : 0<D₂) (i : quotientConductorTarget D₂)
    (hboundary : (((i.1:ℕ)*(i.2.1.val:ℕ)/D₂:ℕ):ℝ)=2*lemma61PaperP4 D) :
    i∈quotientConductorTargetBox D D₂ hD₂ := by
  apply (quotientConductor_mem_targetBox hD₂ i).mpr
  rw [proposition141_mem_indices]
  exact ⟨(quotientConductor_backward hD₂ i.1.property i.2.1.val.property i.2.1.property).1,hboundary.le⟩

-- D³ itself belongs to the large, half-open cover, rather than being lost.
example {D : ℕ} (hD : 2≤D) (hupper : ((D^3:ℕ):ℝ)≤lemma23PaperP D) :
    ∃j∈range (proposition141DyadicBlockCount D),
      D^3∈primitiveDyadicModuli (proposition141DyadicScale D j) := by
  apply proposition141_dyadic_cover hD (one_lt_pow₀ (by omega : 1<D) (by norm_num : (3:ℕ)≠0)) _ hupper
  norm_num [Real.rpow_ofNat]

example {D D₁ D₂ h r : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ)
    (θ : DirichletCharacter ℂ r) : quotientSourceFlatTerm χ β κ a D₁ D₂ 0 h r θ=0 := by
  simp [quotientSourceFlatTerm]

example {D D₁ D₂ d h : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ)
    (θ : DirichletCharacter ℂ 1) : quotientSourceFlatTerm χ β κ a D₁ D₂ d h 1 θ=0 := by
  simp [quotientSourceFlatTerm]

example {D D₁ D₂ d h r : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ)
    (θ : DirichletCharacter ℂ r) (hDN : D∣r*h)
    (hexcluded : θ.changeLevel (r.dvd_mul_right h)=χ.chi.changeLevel hDN) :
    quotientSourceFlatTerm χ β κ a D₁ D₂ d h r θ=0 := by
  unfold quotientSourceFlatTerm
  split_ifs with hp
  · exact False.elim (hp.2.2.2.2 hDN hexcluded)
  · rfl

-- Original Bκ,Ba,epsilon → D₀ → D,χ,κ,a,complex β quantifier order.
example (Bκ Ba : ℝ) (hBκ : 0<Bκ) (hBa : 0<Ba) (ε : ℝ) (hε : 0<ε) :
    ∃D₀ : ℕ,2≤D₀ ∧ ∀D : ℕ,D₀≤D → ∀χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀κ a : ℕ→ℂ,Proposition141KappaBound Bκ κ →
        Proposition141AdmissibleSequence D Ba a → ∀β : ℂ,‖β‖<5*lemma44PaperAlpha D →
        ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
          (∑D₁∈D.divisors,∑'d : ℕ+,∑'k : ℕ+,
            ∑i : primitiveConductorFamilyIndex ((D/D₁)*(k:ℕ)),
              quotientConductorSourceTerm χ β κ a D₁ (D/D₁) (d:ℕ) ⟨k,i⟩) ≤
            ε*lemma33ActualPrimeMass D :=
  quotientSource_normalized_little_o Bκ Ba hBκ hBa ε hε

end ZhangLS.Spec
