import ZhangLS.Spec.Lemma34WeightedConvolution

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset

noncomputable def squareNuHarmonicMass (f : ArithmeticFunction ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, f n * (n : ℝ)⁻¹

noncomputable def squareNuHarmonicTail (f : ArithmeticFunction ℝ) (A : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => A < (n : ℝ)), f n * (n : ℝ)⁻¹

lemma squareNu_convolution_nonneg (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f*g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg (fun d hd => mul_nonneg (hf _) (hg _))

lemma squareNu_pow_nonneg (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (r n : ℕ) : 0 ≤ (f^r) n := by
  induction r generalizing n with
  | zero => simp [ArithmeticFunction.one_apply]; split_ifs <;> positivity
  | succ r ih =>
    rw [pow_succ]
    exact squareNu_convolution_nonneg _ _ ih hf n

lemma squareNu_mass_nonneg (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    0 ≤ squareNuHarmonicMass f N :=
  sum_nonneg (fun n hn => mul_nonneg (hf _) (by positivity))

lemma squareNu_tail_nonneg (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n) (A : ℝ) (N : ℕ) :
    0 ≤ squareNuHarmonicTail f A N :=
  sum_nonneg (fun n hn => mul_nonneg (hf _) (by positivity))

/-- Reindex the actual finite Dirichlet convolution, keeping every positive pair. -/
lemma squareNu_convolution_sum_le (f g : ArithmeticFunction ℝ) (N : ℕ)
    (S : Finset ℕ) (hS : S ⊆ Icc 1 N) (W : ℕ → ℕ → ℝ)
    (hW : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, 0 ≤ W a b)
    (hbound : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a*b ∈ S →
      (f a * (a:ℝ)⁻¹) * (g b * (b:ℝ)⁻¹) ≤ W a b) :
    (∑ n ∈ S, (f*g) n * (n:ℝ)⁻¹) ≤
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, W a b := by
  classical
  let T : Finset (Σ n : ℕ, ℕ × ℕ) := S.sigma fun n => n.divisorsAntidiagonal
  let pairOf (x : Σ n : ℕ, ℕ × ℕ) : ℕ × ℕ := x.2
  have hpair_inj : Set.InjOn pairOf T := by
    intro x hx y hy hxy
    rcases x with ⟨nx, px⟩
    rcases y with ⟨ny, py⟩
    simp only [pairOf] at hxy
    have hpx := (mem_sigma.mp hx).2
    have hpy := (mem_sigma.mp hy).2
    have hnx : px.1 * px.2 = nx := (Nat.mem_divisorsAntidiagonal.mp hpx).1
    have hny : py.1 * py.2 = ny := (Nat.mem_divisorsAntidiagonal.mp hpy).1
    have he : nx = ny := by rw [← hnx, ← hny, hxy]
    exact Sigma.ext he (heq_of_eq hxy)
  have hpair_mem (x : Σ n : ℕ, ℕ × ℕ) (hx : x ∈ T) :
      x.2.1 ∈ Icc 1 N ∧ x.2.2 ∈ Icc 1 N := by
    have hn := mem_Icc.mp (hS (mem_sigma.mp hx).1)
    have hp := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hx).2).1
    have ha : 0 < x.2.1 := by nlinarith
    have hb : 0 < x.2.2 := by nlinarith
    exact ⟨mem_Icc.mpr ⟨ha, (Nat.le_mul_of_pos_right _ hb).trans (hp ▸ hn.2)⟩,
      mem_Icc.mpr ⟨hb, (Nat.le_mul_of_pos_left _ ha).trans (hp ▸ hn.2)⟩⟩
  have himage : T.image pairOf ⊆ Icc 1 N ×ˢ Icc 1 N := by
    intro p hp
    rcases mem_image.mp hp with ⟨x, hx, rfl⟩
    exact mem_product.mpr (hpair_mem x hx)
  calc
    _ = ∑ x ∈ T, (f x.2.1 * g x.2.2) * (x.1:ℝ)⁻¹ := by
      simp only [ArithmeticFunction.mul_apply, sum_mul]
      exact (sum_sigma S (fun n => n.divisorsAntidiagonal)
        (fun x : Σ n : ℕ, ℕ × ℕ => f x.2.1 * g x.2.2 * (x.1:ℝ)⁻¹)).symm
    _ ≤ ∑ x ∈ T, W x.2.1 x.2.2 := by
      apply sum_le_sum
      intro x hx
      have hp := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hx).2).1
      have hs : x.2.1*x.2.2 ∈ S := hp ▸ (mem_sigma.mp hx).1
      have hh := hbound _ (hpair_mem x hx).1 _ (hpair_mem x hx).2 hs
      rw [← hp, Nat.cast_mul, mul_inv]
      convert hh using 1 <;> ring
    _ = ∑ p ∈ T.image pairOf, W p.1 p.2 := by
      exact (sum_image (f := fun p : ℕ × ℕ => W p.1 p.2) hpair_inj).symm
    _ ≤ ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, W p.1 p.2 :=
      sum_le_sum_of_subset_of_nonneg himage (fun p hp _ =>
        hW p.1 (mem_product.mp hp).1 p.2 (mem_product.mp hp).2)
    _ = _ := sum_product' _ _ _

lemma squareNu_mass_mul_le (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    squareNuHarmonicMass (f*g) N ≤
      squareNuHarmonicMass f N * squareNuHarmonicMass g N := by
  unfold squareNuHarmonicMass
  rw [sum_mul_sum]
  apply squareNu_convolution_sum_le f g N (Icc 1 N) (fun _ h => h)
  · intro a ha b hb
    exact mul_nonneg (mul_nonneg (hf _) (by positivity))
      (mul_nonneg (hg _) (by positivity))
  · intro a ha b hb hab
    exact le_rfl

lemma squareNu_tail_mul_le (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (N : ℕ) :
    squareNuHarmonicTail (f*g) (A*B) N ≤
      squareNuHarmonicTail f A N * squareNuHarmonicMass g N +
      squareNuHarmonicMass f N * squareNuHarmonicTail g B N := by
  classical
  unfold squareNuHarmonicTail squareNuHarmonicMass
  simp only [sum_filter]
  rw [sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  simp only [← sum_add_distrib]
  change (∑ n ∈ Icc 1 N, if A*B < (n:ℝ) then (f*g) n*(n:ℝ)⁻¹ else 0) ≤ _
  rw [← sum_filter]
  apply squareNu_convolution_sum_le f g N _ (filter_subset _ _)
  · intro a ha b hb
    have ha0 : 0 ≤ f a := hf a
    have hb0 : 0 ≤ g b := hg b
    split_ifs <;> positivity
  · intro a ha b hb hab
    have hab' : A*B < (a:ℝ)*(b:ℝ) := by
      simpa only [Nat.cast_mul] using (mem_filter.mp hab).2
    have ha0 : 0 ≤ f a*(a:ℝ)⁻¹ := mul_nonneg (hf _) (by positivity)
    have hb0 : 0 ≤ g b*(b:ℝ)⁻¹ := mul_nonneg (hg _) (by positivity)
    have split : A < (a:ℝ) ∨ B < (b:ℝ) := by
      by_contra h
      push_neg at h
      exact (not_lt_of_ge (mul_le_mul h.1 h.2 (by positivity) hA)) hab'
    rcases split with ha' | hb'
    · simp only [ha', ite_true]
      exact le_add_of_nonneg_right (mul_nonneg ha0 (by split_ifs <;> positivity))
    · simp only [hb', ite_true]
      exact le_add_of_nonneg_left (mul_nonneg (by split_ifs <;> positivity) hb0)

lemma squareNu_tail_antitone (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (A B : ℝ) (hAB : A ≤ B) (N : ℕ) :
    squareNuHarmonicTail f B N ≤ squareNuHarmonicTail f A N := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact mem_filter.mpr ⟨(mem_filter.mp hn).1, hAB.trans_lt (mem_filter.mp hn).2⟩
  · intro n hn hnot
    exact mul_nonneg (hf _) (by positivity)

lemma squareNu_mass_pow_le (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (N r : ℕ) (H : ℝ) (hH : 0 ≤ H) (hbound : squareNuHarmonicMass f N ≤ H) :
    squareNuHarmonicMass (f^r) N ≤ H^r := by
  induction r with
  | zero =>
    simp only [pow_zero, squareNuHarmonicMass, ArithmeticFunction.one_apply]
    by_cases hN : 1 ≤ N <;> simp [hN]
  | succ r ih =>
    rw [pow_succ]
    exact (squareNu_mass_mul_le _ _ (squareNu_pow_nonneg f hf r) hf N).trans
      (by simpa only [pow_succ] using
        mul_le_mul ih hbound (squareNu_mass_nonneg f hf N) (pow_nonneg hH r))

/-- The finite union bound pays once for each possible large factor. -/
lemma squareNu_tail_pow_succ_le (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (N r : ℕ) (A H T : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hMass : squareNuHarmonicMass f N ≤ H) (hTail : squareNuHarmonicTail f A N ≤ T) :
    squareNuHarmonicTail (f^(r+1)) (A^(r+1)) N ≤ (r+1:ℕ)*T*H^r := by
  induction r with
  | zero => simpa using hTail
  | succ r ih =>
    rw [show r+1+1=r+2 by omega, pow_succ (f) (r+1), pow_succ A (r+1)]
    have hb := squareNu_tail_mul_le (f^(r+1)) f (squareNu_pow_nonneg f hf _) hf
      (A^(r+1)) A (pow_nonneg hA _) hA N
    have hp := squareNu_mass_pow_le f hf N (r+1) H hH hMass
    have hm0 := squareNu_mass_nonneg f hf N
    have ht0 := squareNu_tail_nonneg f hf A N
    have h1 := mul_le_mul ih hMass hm0 (by positivity : 0 ≤ (r+1:ℕ)*T*H^r)
    have h2 := mul_le_mul hp hTail ht0 (pow_nonneg hH _)
    calc
      _ ≤ _ := hb
      _ ≤ ((r+1:ℕ)*T*H^r)*H + H^(r+1)*T := add_le_add h1 h2
      _ = _ := by push_cast; rw [pow_succ]; ring

lemma squareNu_tail_pow_le (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (N r : ℕ) (hr : 0 < r) (A H T : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hMass : squareNuHarmonicMass f N ≤ H) (hTail : squareNuHarmonicTail f A N ≤ T) :
    squareNuHarmonicTail (f^r) (A^r) N ≤ (r:ℝ)*T*H^(r-1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simpa using squareNu_tail_pow_succ_le f hf N s A H T hA hH hT hMass hTail

/-- The numerical margin is strict even at q=9: 18*(21/20)=18.9<19. -/
lemma squareNu_threshold_power_le (D : ℝ) (hD : 1 ≤ D) (r : ℕ) (hr : r ≤ 18) :
    (D^(21/20:ℝ))^r ≤ D^19 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ D),
    ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hD
  have hrR : (r:ℝ) ≤ 18 := by exact_mod_cast hr
  norm_num
  nlinarith

/-- Full strict tail, with both the large convolution and square-supported ranges retained. -/
lemma squareNu_square_assembly_le (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (D : ℝ) (hD : 1 ≤ D)
    (r N : ℕ) (hr : 0 < r) (hr18 : r ≤ 18) (H T M E : ℝ)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hMass : squareNuHarmonicMass f N ≤ H)
    (hTail : squareNuHarmonicTail f (D^(21/20:ℝ)) N ≤ T)
    (hgMass : squareNuHarmonicMass g N ≤ M)
    (hgTail : squareNuHarmonicTail g D N ≤ E) :
    squareNuHarmonicTail (f^r*g) (D^20) N ≤
      (r:ℝ)*T*H^(r-1)*M + H^r*E := by
  have hfPow := squareNu_pow_nonneg f hf r
  have hlarge := (squareNu_tail_antitone (f^r) hfPow _ _
    (squareNu_threshold_power_le D hD r hr18) N).trans
    (squareNu_tail_pow_le f hf N r hr _ H T (by positivity) hH hT hMass hTail)
  have hpow := squareNu_mass_pow_le f hf N r H hH hMass
  have ht := squareNu_tail_mul_le (f^r) g hfPow hg (D^19) D (by positivity) (by linarith) N
  have hid : D^19*D=D^20 := by ring
  rw [hid] at ht
  exact ht.trans (add_le_add
    (mul_le_mul hlarge hgMass (squareNu_mass_nonneg g hg N) (by positivity))
    (mul_le_mul hpow hgTail (squareNu_tail_nonneg g hg D N) (pow_nonneg hH _)))

end ZhangLS.Spec
