import ZhangLS.Spec.Proposition71CoprimeKappaSeries
import ZhangLS.Spec.Proposition71SupportedCoprimeSplit
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_coprime_index_summable {m : ℕ} (f : ℕ → ℂ) {s : ℂ}
    (hs : LSeriesSummable (fun n => if n.Coprime m then f n else 0) s) :
    Summable (fun n : Proposition71CoprimeIndex m => f n.val/(n.val : ℂ)^s) := by
  have hh : Summable (fun n : Proposition71CoprimeIndex m =>
      LSeries.term (fun n => if n.Coprime m then f n else 0) s n.val) :=
    hs.subtype (fun n => n ≠ 0 ∧ n.Coprime m)
  apply hh.congr
  intro n
  rw [LSeries.term_of_ne_zero n.property.1, if_pos n.property.2]

lemma proposition71_coprime_index_tsum (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    (∑' n : Proposition71CoprimeIndex m, f n.val/(n.val : ℂ)^s)=
      LSeries (fun n => if n.Coprime m then f n else 0) s := by
  rw [show (∑' n : Proposition71CoprimeIndex m, f n.val/(n.val : ℂ)^s)=
    ∑' n : ℕ, {n : ℕ | n ≠ 0 ∧ n.Coprime m}.indicator (fun n => f n/(n : ℂ)^s) n from
      _root_.tsum_subtype {n : ℕ | n ≠ 0 ∧ n.Coprime m} (fun n => f n/(n : ℂ)^s)]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n; simp
  · by_cases hc : n.Coprime m
    · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | n ≠ 0 ∧ n.Coprime m} from ⟨hn,hc⟩),
        LSeries.term_of_ne_zero hn,if_pos hc]
    · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | n ≠ 0 ∧ n.Coprime m} from fun h => hc h.2),
        LSeries.term_of_ne_zero hn,if_neg hc,zero_div]

lemma proposition71_shifted_kappa_term_factor (β : Fin 3 → ℂ)
    {d m : ℕ} (h : Lemma83SupportedIndex d m)
    (r : Proposition71CoprimeIndex (d*m)) (s : ℂ) :
    lemma83Kappa β (d*(h.val*r.val))/((h.val*r.val : ℕ) : ℂ)^s =
      (lemma83Kappa β (d*h.val)/(h.val : ℂ)^s)*
        (lemma83Kappa β r.val/(r.val : ℂ)^s) := by
  have hrd : r.val.Coprime d := r.property.2.of_dvd_right (dvd_mul_right d m)
  have hhr := proposition71_supported_coprime h.property.1 h.property.2.1 hrd
  have hcop : (d*h.val).Coprime r.val := hrd.symm.mul_left hhr
  rw [←Nat.mul_assoc,(lemma83_kappa_multiplicative β).map_mul_of_coprime hcop,
    Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  ring

/-- Absolutely convergent shifted coprime factorization, without dividing by
κ(d), and with no coprimality restriction on d and m. -/
theorem proposition71_shifted_coprime_kappa_hasSum (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re = 0) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : Proposition71CoprimeIndex m => lemma83Kappa β (d*n.val)/(n.val : ℂ)^s)
      (lemma83ModifiedKappa β d m s * lemma83Lambda β (d*m) s *
        (riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s)) := by
  let F := fun h : Lemma83SupportedIndex d m => lemma83Kappa β (d*h.val)/(h.val : ℂ)^s
  let G := fun r : Proposition71CoprimeIndex (d*m) => lemma83Kappa β r.val/(r.val : ℂ)^s
  have hF : Summable F := (lemma83_modified_kappa_hasSum β hβ d m hd s (by linarith)).summable
  have hG : Summable G := proposition71_coprime_index_summable _
    (proposition71_coprime_kappa_summable β hβ (d*m) hs)
  have hFG : Summable (fun x : Lemma83SupportedIndex d m × Proposition71CoprimeIndex (d*m) =>
      F x.1*G x.2) := summable_mul_of_summable_norm hF.norm hG.norm
  have hh := hF.hasSum.mul hG.hasSum hFG
  have hGeq : (∑' r, G r)=lemma83Lambda β (d*m) s *
      (riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s) := by
    rw [proposition71_coprime_index_tsum (d*m) (fun n => lemma83Kappa β n) s]
    exact proposition71_coprime_kappa_LSeries β hβ (mul_ne_zero hd hm) hs
  rw [hGeq,show (∑' h, F h)=lemma83ModifiedKappa β d m s from rfl,←mul_assoc] at hh
  apply ((proposition71SupportedCoprimeEquiv d m hd).hasSum_iff).mp
  convert hh using 1
  funext x
  exact proposition71_shifted_kappa_term_factor β x.1 x.2 s

lemma proposition71_shifted_coprime_kappa_summable (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re = 0) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => if n.Coprime m then lemma83Kappa β (d*n) else 0) s := by
  have hh := (proposition71_shifted_coprime_kappa_hasSum β hβ hd hm hs).summable
  have hi : Summable ({n : ℕ | n ≠ 0 ∧ n.Coprime m}.indicator
      (fun n => lemma83Kappa β (d*n)/(n : ℂ)^s)) := summable_subtype_iff_indicator.mp hh
  apply hi.congr
  intro n
  by_cases hn : n=0
  · subst n; simp
  · by_cases hc : n.Coprime m
    · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | n ≠ 0 ∧ n.Coprime m} from ⟨hn,hc⟩),
        LSeries.term_of_ne_zero hn,if_pos hc]
    · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | n ≠ 0 ∧ n.Coprime m} from fun h => hc h.2),
        LSeries.term_of_ne_zero hn,if_neg hc,zero_div]

/-- The literal source (7.19) Dirichlet series, with every finite-prime factor. -/
theorem proposition71_shifted_coprime_kappa_LSeries (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re = 0) {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => if n.Coprime m then lemma83Kappa β (d*n) else 0) s =
      lemma83ModifiedKappa β d m s * lemma83Lambda β (d*m) s *
        (riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s) := by
  rw [←proposition71_coprime_index_tsum m (fun n => lemma83Kappa β (d*n)) s]
  exact (proposition71_shifted_coprime_kappa_hasSum β hβ hd hm hs).tsum_eq

end ZhangLS.Spec
