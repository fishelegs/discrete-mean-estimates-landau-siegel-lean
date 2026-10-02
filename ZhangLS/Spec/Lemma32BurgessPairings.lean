import ZhangLS.Spec.Lemma32BurgessFourthMoment
import Mathlib.Data.Fin.VecNotation
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

def lemma32QuarticPairing (H : ℕ) (j : Fin 3) (ab : Fin H × Fin H) : Fin 4 → Fin H :=
  if j=0 then ![ab.1,ab.1,ab.2,ab.2]
  else if j=1 then ![ab.1,ab.2,ab.1,ab.2]
  else ![ab.1,ab.2,ab.2,ab.1]

noncomputable def lemma32DegenerateQuarticTuples (H : ℕ) : Finset (Fin 4 → Fin H) :=
  (Finset.univ.image (lemma32QuarticPairing H 0)) ∪
    (Finset.univ.image (lemma32QuarticPairing H 1)) ∪
    (Finset.univ.image (lemma32QuarticPairing H 2))

lemma lemma32_quartic_pairing_image_card (H : ℕ) (j : Fin 3) :
    (Finset.univ.image (lemma32QuarticPairing H j)).card ≤ H^2 := by
  calc
    _ ≤ (Finset.univ : Finset (Fin H × Fin H)).card := Finset.card_image_le
    _ = _ := by simp [pow_two]

lemma lemma32_degenerate_quartic_tuples_card (H : ℕ) :
    (lemma32DegenerateQuarticTuples H).card ≤ 3*H^2 := by
  unfold lemma32DegenerateQuarticTuples
  have h0 := lemma32_quartic_pairing_image_card H 0
  have h1 := lemma32_quartic_pairing_image_card H 1
  have h2 := lemma32_quartic_pairing_image_card H 2
  calc
    _ ≤ ((Finset.univ.image (lemma32QuarticPairing H 0)) ∪
      (Finset.univ.image (lemma32QuarticPairing H 1))).card+
      (Finset.univ.image (lemma32QuarticPairing H 2)).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image (lemma32QuarticPairing H 0)).card+
      (Finset.univ.image (lemma32QuarticPairing H 1)).card)+
      (Finset.univ.image (lemma32QuarticPairing H 2)).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := by omega

end ZhangLS.Spec
