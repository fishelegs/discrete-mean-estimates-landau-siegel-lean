import ZhangLS.Spec.Lemma83Definitions

/-! # The exact gcd decomposition (7.17)

The coefficient identity is proved for arbitrary arithmetic functions, by a
bijection of actual divisor pairs, not as an assumed analytic transformation.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def proposition71SplitPairs (d l : ℕ) : Finset ((ℕ×ℕ)×(ℕ×ℕ)) :=
  (d.divisorsAntidiagonal ×ˢ l.divisorsAntidiagonal).filter
    (fun x => x.2.1.Coprime x.1.2)

lemma proposition71_split_mem {d l : ℕ} {x : (ℕ×ℕ)×(ℕ×ℕ)}
    (hx : x ∈ proposition71SplitPairs d l) :
    x.1.1*x.1.2=d ∧ d≠0 ∧ x.2.1*x.2.2=l ∧ l≠0 ∧ x.2.1.Coprime x.1.2 := by
  simpa only [proposition71SplitPairs,mem_filter,mem_product,
    Nat.mem_divisorsAntidiagonal,and_assoc] using hx

lemma proposition71_split_gcd {d l : ℕ} {x : (ℕ×ℕ)×(ℕ×ℕ)}
    (hx : x ∈ proposition71SplitPairs d l) :
    Nat.gcd (x.1.1*x.2.1) d = x.1.1 := by
  have h := proposition71_split_mem hx
  rw [←h.1,Nat.gcd_mul_left,h.2.2.2.2.gcd_eq_one,mul_one]

/-- The divisor-pair map in (7.17) is injective, with its first coordinate
recovered by gcd. -/
theorem proposition71_split_injective {d l : ℕ}
    {x y : (ℕ×ℕ)×(ℕ×ℕ)}
    (hx : x ∈ proposition71SplitPairs d l) (hy : y ∈ proposition71SplitPairs d l)
    (he : (x.1.1*x.2.1,x.1.2*x.2.2) = (y.1.1*y.2.1,y.1.2*y.2.2)) : x=y := by
  have hx' := proposition71_split_mem hx
  have hy' := proposition71_split_mem hy
  have h1 : x.1.1=y.1.1 := by
    rw [←proposition71_split_gcd hx,←proposition71_split_gcd hy,(Prod.mk.inj he).1]
  have hxn : x.1.1 ≠ 0 := by intro hz; simp [hz] at hx'; tauto
  have h2 : x.1.2=y.1.2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hxn)
    rw [hx'.1,h1,hy'.1]
  have h3 : x.2.1=y.2.1 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hxn)
    simpa only [h1] using (Prod.mk.inj he).1
  have hxn2 : x.1.2 ≠ 0 := by intro hz; simp [hz] at hx'; tauto
  have h4 : x.2.2=y.2.2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hxn2)
    simpa only [h2] using (Prod.mk.inj he).2
  exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)

/-- Every divisor pair of dl has the unique gcd decomposition used in (7.17). -/
theorem proposition71_split_surjective {d l : ℕ} (hd : d≠0) (hl : l≠0)
    {a b : ℕ} (hab : a*b=d*l) :
    ∃ x ∈ proposition71SplitPairs d l,
      (x.1.1*x.2.1,x.1.2*x.2.2) = (a,b) := by
  let g := Nat.gcd a d
  have hg : 0<g := Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hd)
  have hag : g*(a/g)=a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a d)
  have hdg : g*(d/g)=d := Nat.mul_div_cancel' (Nat.gcd_dvd_right a d)
  have hcop : (a/g).Coprime (d/g) :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right (Nat.pos_of_ne_zero hd)
  have he : (a/g)*b = (d/g)*l := by
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [←mul_assoc,hag,←mul_assoc,hdg,hab]
  have hdiv : d/g ∣ b := hcop.symm.dvd_of_dvd_mul_left
    (he ▸ Nat.dvd_mul_right (d/g) l)
  obtain ⟨v,hv⟩ := hdiv
  have hdgp : 0<d/g := Nat.div_pos (Nat.gcd_le_right a (Nat.pos_of_ne_zero hd)) hg
  have hlv : (a/g)*v=l := by
    apply Nat.eq_of_mul_eq_mul_left hdgp
    calc
      (d/g)*((a/g)*v) = (a/g)*((d/g)*v) := by ring
      _ = (a/g)*b := by rw [←hv]
      _ = (d/g)*l := he
  refine ⟨((g,d/g),(a/g,v)),?_,?_⟩
  · simp only [proposition71SplitPairs,mem_filter,mem_product,Nat.mem_divisorsAntidiagonal]
    exact ⟨⟨⟨hdg,hd⟩,⟨hlv,hl⟩⟩,hcop⟩
  · exact Prod.ext hag hv.symm

/-- The actual finite divisor-pair summation identity (7.17). -/
theorem proposition71_divisor_pair_split {d l : ℕ} (hd : d≠0) (hl : l≠0)
    (F : ℕ → ℕ → ℂ) :
    (∑ ab ∈ (d*l).divisorsAntidiagonal, F ab.1 ab.2) =
      ∑ dd ∈ d.divisorsAntidiagonal,
        ∑ ll ∈ l.divisorsAntidiagonal.filter (fun ll => ll.1.Coprime dd.2),
          F (dd.1*ll.1) (dd.2*ll.2) := by
  have hb : (∑ x ∈ proposition71SplitPairs d l, F (x.1.1*x.2.1) (x.1.2*x.2.2)) =
      ∑ ab ∈ (d*l).divisorsAntidiagonal, F ab.1 ab.2 := by
    apply sum_bij (fun x _ => (x.1.1*x.2.1,x.1.2*x.2.2))
    · intro x hx
      have h := proposition71_split_mem hx
      apply Nat.mem_divisorsAntidiagonal.mpr
      constructor
      · calc
          _ = (x.1.1*x.1.2)*(x.2.1*x.2.2) := by ring
          _ = d*l := by rw [h.1,h.2.2.1]
      · exact Nat.mul_ne_zero hd hl
    · intro x hx y hy he
      exact proposition71_split_injective hx hy he
    · intro ab hab
      obtain ⟨x,hx,he⟩ := proposition71_split_surjective hd hl (Nat.mem_divisorsAntidiagonal.mp hab).1
      exact ⟨x,hx,by simpa only [Prod.mk.eta] using he⟩
    · intro x hx
      rfl
  rw [←hb,proposition71SplitPairs,sum_filter,sum_product]
  apply sum_congr rfl
  intro dd hdd
  rw [sum_filter]

/-- Applied to the genuine κ and arbitrary coefficient sequence, this is
precisely the convolution decomposition displayed in (7.17). -/
theorem proposition71_kappa_convolution_split (β : Fin 3 → ℂ)
    (a : ArithmeticFunction ℂ) {d l : ℕ} (hd : d≠0) (hl : l≠0) :
    (lemma83Kappa β * a) (d*l) =
      ∑ dd ∈ d.divisorsAntidiagonal,
        ∑ ll ∈ l.divisorsAntidiagonal.filter (fun ll => ll.1.Coprime dd.2),
          lemma83Kappa β (dd.1*ll.1) * a (dd.2*ll.2) := by
  rw [ArithmeticFunction.mul_apply]
  exact proposition71_divisor_pair_split hd hl (fun m n => lemma83Kappa β m*a n)

end ZhangLS.Spec
