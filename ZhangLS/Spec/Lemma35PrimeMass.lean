import ZhangLS.Spec.Lemma35Mean
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma35_prime_windows_eq (D : ℕ) : lemma33PrimeWindow D = lemma56PaperPrimes D := by
  ext p
  rw [lemma33_mem_prime_window,lemma56_mem_paper_primes]
  rfl

lemma lemma35_actual_prime_mass_eq (D : ℕ) : lemma33ActualPrimeMass D = lemma56PrimeMass D := by
  unfold lemma33ActualPrimeMass lemma56PrimeMass lemma33PrimeIndex
  calc
    _ = ∑ p ∈ lemma33PrimeWindow D, (p : ℝ) :=
      (Finset.sum_subtype (lemma33PrimeWindow D) (fun _ => Iff.rfl) (fun p : ℕ => (p : ℝ))).symm
    _ = _ := by rw [lemma35_prime_windows_eq]

lemma lemma35_prime_mass_scale_of_lower {D : ℕ} (hL : 0 < lemma23PaperL D)
    (hm : (1/4 : ℝ)*lemma23PaperP D^2/lemma23PaperL D^77 ≤ lemma33ActualPrimeMass D) :
    lemma23PaperP D^2 ≤ 4*lemma33ActualPrimeMass D*lemma23PaperL D^77 := by
  have he := (div_le_iff₀ (pow_pos hL 77)).mp hm
  nlinarith

lemma lemma35_mean_scale_identity (L : ℝ) (hL : 0 < L) :
    L^77*L^(-2011 : ℤ) = L^(-1934 : ℤ) := by
  simpa only [Int.reduceAdd,zpow_ofNat] using (zpow_add₀ (ne_of_gt hL) (77 : ℤ) (-2011 : ℤ)).symm

end ZhangLS.Spec
