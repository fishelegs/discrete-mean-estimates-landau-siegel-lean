import ZhangLS.Spec.AppendixBTailSharpFiniteIntegral
import ZhangLS.Spec.AppendixBTailFiniteUnsmoothing

/-! Exact splitting of the actual Gaussian rho series into n<=N and n>N,
with the proved infinite-tail estimate. No infinite z/sum exchange is used. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical

noncomputable def appendixBFiniteGaussianSourceSlice (D : ℕ) (β γ : ℂ)
    (l₁ N : ℕ) (z : ℝ) : ℂ :=
  ∑ n∈Finset.Icc 1 N, appendixBRhoMonomialCoefficient (lemma151P1 D/(l₁ : ℝ)) β γ n*
    ((zhangGaussianWeight D (Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ)/n)-
      zhangGaussianWeight D (Real.exp (0.5*lemma23PaperL D^9)/(l₁ : ℝ)/n) : ℝ) : ℂ)

lemma appendixB_source_gaussian_eq_rho_series {D : ℕ} (hD : 1<D) (z : ℝ)
    {β γ : ℂ} (hβre : β.re=0) (hγ : γ.re=0) {l₁ : ℕ} (hl : 0<l₁) :
    appendixBSourceGaussianSlice D (lemma23PaperL D^9) z β γ l₁=
      ∑' n : ℕ, appendixBRhoMonomialCoefficient (lemma151P1 D/(l₁ : ℝ)) β γ n*
        ((zhangGaussianWeight D (Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ)/n)-
          zhangGaussianWeight D (Real.exp (0.5*lemma23PaperL D^9)/(l₁ : ℝ)/n) : ℝ) : ℂ) := by
  rw [appendixB_source_gaussian_slice_eq_sum hD (lemma23PaperL D^9) z hβre hγ hl]
  simp only [appendixBRhoMonomialCoefficient,lemma151P1,appendixB_paper_power_exp]

lemma appendixB_rho_gaussian_finite_split {D : ℕ} (hD : 1<D)
    (hL : 3≤lemma23PaperL D) {X x : ℝ} (hX : 0<X) (hx : 0<x)
    (hlog : Real.log x≤2*lemma23PaperL D^9) (N : ℕ) (hcut : 2*x≤(N : ℝ))
    {β γ : ℂ} (hβre : β.re=0) (hβ : ‖β‖≤1) (hγ : γ.re=0) :
    Summable (fun n : ℕ => appendixBRhoMonomialCoefficient X β γ n*
      (zhangGaussianWeight D (x/n) : ℂ)) ∧
    ‖(∑' n : ℕ, appendixBRhoMonomialCoefficient X β γ n*(zhangGaussianWeight D (x/n) : ℂ))-
      ∑ n∈Finset.Icc 1 N, appendixBRhoMonomialCoefficient X β γ n*(zhangGaussianWeight D (x/n) : ℂ)‖≤
      lemma44InverseSquareMass*Real.exp (-(lemma23PaperL D^10)) := by
  let S := Finset.Icc 1 N
  let f := fun n : ℕ => appendixBRhoMonomialCoefficient X β γ n*(zhangGaussianWeight D (x/n) : ℂ)
  let short := fun n : ℕ => if n∈S then f n else 0
  let tail := fun n : ℕ => if N<n then f n else 0
  have hshort : Summable short := summable_of_ne_finset_zero (s := S) (by intro n hn; simp [short,hn])
  have ht := appendixB_actual_rho_far_gaussian hD hL hX hx hlog N hcut hβre hβ hγ
  have htail : Summable tail := ht.1
  have hpoint (n : ℕ) : f n=short n+tail n := by
    by_cases hn : n=0
    · simp [hn,f,short,tail,S,appendixBRhoMonomialCoefficient]
    have hnpos : 0<n := Nat.pos_of_ne_zero hn
    by_cases hN : n≤N
    · simp [short,tail,S,Finset.mem_Icc,hn,hnpos,hN,not_lt.mpr hN]
    · simp [short,tail,S,Finset.mem_Icc,hnpos,hN,Nat.lt_of_not_ge hN]
  have hsumshort : (∑' n : ℕ, short n)=∑ n∈S, f n := by
    rw [tsum_eq_sum (s := S) (by intro n hn; simp [short,hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [short,hn])
  have hsum : (∑' n : ℕ, f n)=(∑ n∈S, f n)+∑' n : ℕ, tail n := by
    calc
      (∑' n : ℕ, f n) = (∑' n : ℕ, (short n+tail n)) := tsum_congr hpoint
      _ = _ := by rw [hshort.tsum_add htail,hsumshort]
  refine ⟨(hshort.add htail).congr (fun n => (hpoint n).symm),?_⟩
  change ‖(∑' n : ℕ, f n)-(∑ n∈S, f n)‖≤_
  rw [hsum,add_sub_cancel_left]
  exact ht.2

/-- Full actual Gaussian source minus its finite n<=N part. Both infinite
Gaussian tails are controlled; N need not avoid an integer endpoint. -/
theorem appendixB_source_gaussian_finite_error {D : ℕ} (hD : 1<D)
    (hL : 3≤lemma23PaperL D) {z : ℝ} (hz : 0.5≤z)
    {β γ : ℂ} (hβre : β.re=0) (hβ : ‖β‖≤1) (hγ : γ.re=0)
    {l₁ : ℕ} (hl : 0<l₁) (N : ℕ)
    (hcut : 2*(Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ))≤(N : ℝ))
    (hlog : Real.log (Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ))≤2*lemma23PaperL D^9) :
    ‖appendixBSourceGaussianSlice D (lemma23PaperL D^9) z β γ l₁-
      appendixBFiniteGaussianSourceSlice D β γ l₁ N z‖≤
      2*lemma44InverseSquareMass*Real.exp (-(lemma23PaperL D^10)) := by
  let x := Real.exp (0.5*lemma23PaperL D^9)/(l₁ : ℝ)
  let y := Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ)
  let X := lemma151P1 D/(l₁ : ℝ)
  let a := appendixBRhoMonomialCoefficient X β γ
  let fx := fun n : ℕ => a n*(zhangGaussianWeight D (x/n) : ℂ)
  let fy := fun n : ℕ => a n*(zhangGaussianWeight D (y/n) : ℂ)
  have hLp : 0<lemma23PaperL D := by linarith
  have hP1 : 0<lemma151P1 D := by
    unfold lemma151P1
    exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hXp : 0<X := div_pos hP1 (Nat.cast_pos.mpr hl)
  have hx : 0<x := div_pos (Real.exp_pos _) (Nat.cast_pos.mpr hl)
  have hxy : x≤y := by
    dsimp [x,y]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hz (pow_nonneg hLp.le 9)
  have hy : 0<y := hx.trans_le hxy
  have hcutx : 2*x≤(N : ℝ) := (mul_le_mul_of_nonneg_left hxy (by norm_num)).trans hcut
  have hlogx : Real.log x≤2*lemma23PaperL D^9 := (Real.log_le_log hx hxy).trans hlog
  have hsx := appendixB_rho_gaussian_finite_split hD hL hXp hx hlogx N hcutx hβre hβ hγ
  have hsy := appendixB_rho_gaussian_finite_split hD hL hXp hy hlog N hcut hβre hβ hγ
  have he : appendixBSourceGaussianSlice D (lemma23PaperL D^9) z β γ l₁-
      appendixBFiniteGaussianSourceSlice D β γ l₁ N z=
      ((∑' n : ℕ, fy n)-(∑ n∈Finset.Icc 1 N, fy n))-
        ((∑' n : ℕ, fx n)-(∑ n∈Finset.Icc 1 N, fx n)) := by
    rw [appendixB_source_gaussian_eq_rho_series hD z hβre hγ hl]
    unfold appendixBFiniteGaussianSourceSlice
    simp_rw [Complex.ofReal_sub,mul_sub]
    rw [hsy.1.tsum_sub hsx.1,Finset.sum_sub_distrib]
    dsimp [fy,fx,a,X,y,x]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hsy.2 hsx.2).trans_eq (by ring))

end ZhangLS.Spec
