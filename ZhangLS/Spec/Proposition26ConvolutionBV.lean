import ZhangLS.Spec.Proposition26ProfileBV

/-! Exact finite Dirichlet-convolution reindexing and the resulting χ/BV
inner bound. This module takes only the algebraic ξ=1*b identity; it leaves
the finite absolute b-harmonic mass explicitly on the right. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition26_finite_product_reindex (N : ℕ) (F : ℕ→ℕ→ℂ) :
    (∑ n∈Icc 1 N, ∑ ab∈n.divisorsAntidiagonal,F ab.1 ab.2)=
      ∑ k∈Icc 1 N, ∑ l∈Icc 1 (N/k),F k l := by
  rw [Finset.sum_sigma',Finset.sum_sigma']
  apply sum_bij (fun x _ => ⟨x.2.1,x.2.2⟩)
  · intro x hx
    obtain ⟨hn,hab⟩ := mem_sigma.mp hx
    obtain ⟨hp,hne⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    have hn0 : 0<x.1 := (mem_Icc.mp hn).1
    have ha : 0<x.2.1 := Nat.pos_of_ne_zero (by intro hz; rw [hz,zero_mul] at hp; omega)
    have hb : 0<x.2.2 := Nat.pos_of_ne_zero (by intro hz; rw [hz,mul_zero] at hp; omega)
    have hnN := (mem_Icc.mp hn).2
    refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨ha,?_⟩,mem_Icc.mpr ⟨hb,?_⟩⟩
    · exact (Nat.le_mul_of_pos_right _ hb).trans (hp ▸ hnN)
    · exact (Nat.le_div_iff_mul_le ha).mpr (by simpa only [Nat.mul_comm,hp] using hnN)
  · intro x hx y hy hxy
    obtain ⟨hn,hxpair⟩ := mem_sigma.mp hx
    obtain ⟨hm,hypair⟩ := mem_sigma.mp hy
    have ha : x.2.1=y.2.1 := congrArg Sigma.fst hxy
    have hb : x.2.2=y.2.2 := by
      have hh := Sigma.mk.inj_iff.mp hxy
      exact eq_of_heq hh.2
    have hpair : x.2=y.2 := Prod.ext ha hb
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp hxpair).1
    have hyprod := (Nat.mem_divisorsAntidiagonal.mp hypair).1
    have hfirst : x.1=y.1 := by rw [←hxprod,←hyprod,hpair]
    exact Sigma.ext hfirst (heq_of_eq hpair)
  · intro y hy
    obtain ⟨hk,hl⟩ := mem_sigma.mp hy
    obtain ⟨hk0,hkN⟩ := mem_Icc.mp hk
    obtain ⟨hl0,hlN⟩ := mem_Icc.mp hl
    have hprod : y.1*y.2≤N := by
      have h := (Nat.le_div_iff_mul_le hk0).mp hlN
      simpa only [Nat.mul_comm] using h
    refine ⟨⟨y.1*y.2,(y.1,y.2)⟩,mem_sigma.mpr
      ⟨mem_Icc.mpr ⟨Nat.mul_pos hk0 hl0,hprod⟩,
        Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,(Nat.mul_pos hk0 hl0).ne'⟩⟩,?_⟩
    rfl
  · intro x hx
    rfl

lemma proposition26_character_cpow_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (k l : ℕ) :
    χ.evalNat (k*l)*((k*l:ℕ):ℂ)^(-s)=
      (χ.evalNat k*(k:ℂ)^(-s))*(χ.evalNat l*(l:ℂ)^(-s)) := by
  have he : χ.evalNat (k*l)=χ.evalNat k*χ.evalNat l := by
    simp [RealPrimitiveCharacter.evalNat,Nat.cast_mul,map_mul]
  rw [he,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  ring

/-- Exact finite reindexing, before taking absolute values. -/
theorem proposition26_convolution_profile_identity {D : ℕ}
    (χ : RealPrimitiveCharacter D) (s : ℂ) (w b ξ : ℕ→ℂ) (q N : ℕ)
    (hξ : ∀n:ℕ,0<n → ξ n=∑ab∈n.divisorsAntidiagonal,b ab.1) :
    (∑ n∈Icc 1 N,ξ n*(χ.evalNat n*(n:ℂ)^(-s))*w (q*n))=
      ∑ k∈Icc 1 N,(b k*(χ.evalNat k*(k:ℂ)^(-s)))*
        (∑ l∈Icc 1 (N/k),w ((q*k)*l)*(χ.evalNat l*(l:ℂ)^(-s))) := by
  have hexpand : (∑ n∈Icc 1 N,ξ n*(χ.evalNat n*(n:ℂ)^(-s))*w (q*n))=
      ∑ n∈Icc 1 N, ∑ab∈n.divisorsAntidiagonal,
        (b ab.1*(χ.evalNat ab.1*(ab.1:ℂ)^(-s)))*
          (w ((q*ab.1)*ab.2)*(χ.evalNat ab.2*(ab.2:ℂ)^(-s))) := by
    apply sum_congr rfl
    intro n hn
    rw [hξ n (mem_Icc.mp hn).1,Finset.sum_mul,Finset.sum_mul]
    apply sum_congr rfl
    intro ab hab
    have hp := (Nat.mem_divisorsAntidiagonal.mp hab).1
    rw [←hp,proposition26_character_cpow_mul]
    simp only [Nat.mul_assoc]
    ring
  rw [hexpand,proposition26_finite_product_reindex N
    (fun k l => (b k*(χ.evalNat k*(k:ℂ)^(-s)))*
      (w ((q*k)*l)*(χ.evalNat l*(l:ℂ)^(-s))))]
  apply sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

/-- An actual χ-weighted convolution sum is bounded by the finite b-harmonic
mass. This is the arithmetic input to the second Section 7 inner sum. -/
theorem proposition26_convolution_profile_norm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1<D) (hL : 8≤lemma23PaperL D)
    {s : ℂ} (hs : s.re=1) (hnorm : ‖s‖≤(D:ℝ))
    {w : ℕ→ℂ} {V : ℝ} (hw : Proposition26VariationBound w V)
    (b ξ : ℕ→ℂ) {q : ℕ} (hq : 0<q) (N : ℕ)
    (hξ : ∀n:ℕ,0<n → ξ n=∑ab∈n.divisorsAntidiagonal,b ab.1) :
    ‖∑ n∈Icc 1 N,ξ n*(χ.evalNat n*(n:ℂ)^(-s))*w (q*n)‖ ≤
      (((14*Real.exp 16+2)*lemma23PaperL D)*V)*
        (∑ k∈Icc 1 N,‖b k‖/(k:ℝ)) := by
  rw [proposition26_convolution_profile_identity χ s w b ξ q N hξ]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro k hk
  have hkp : 0<k := (mem_Icc.mp hk).1
  have hinner := proposition26_profile_harmonic χ hD hL hs hnorm hw
    (Nat.mul_pos hq hkp) (N/k)
  have hterm : ‖χ.evalNat k*(k:ℂ)^(-s)‖≤(k:ℝ)⁻¹ := by
    rw [norm_mul,Complex.norm_natCast_cpow_of_pos hkp,Complex.neg_re,hs,Real.rpow_neg_one]
    exact mul_le_of_le_one_left (by positivity) (χ.evalNat_norm_le_one k)
  rw [norm_mul,norm_mul]
  have hcoef : ‖b k‖*‖χ.evalNat k*(k:ℂ)^(-s)‖≤‖b k‖*(k:ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left hterm (norm_nonneg (b k))
  exact (mul_le_mul hcoef hinner (norm_nonneg _)
    (mul_nonneg (norm_nonneg (b k)) (inv_nonneg.mpr (Nat.cast_nonneg k)))).trans_eq (by ring)

end ZhangLS.Spec
