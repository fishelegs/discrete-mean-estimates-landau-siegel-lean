import ZhangLS.Spec.Lemma32FiniteActualCurvePoints
import Mathlib.Algebra.Group.Prod
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32ProductCharacterLeft {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar (R × S) ℂ) : MulChar R ℂ where
  toFun a := χ (a,1)
  map_one' := χ.map_one'
  map_mul' a b := by simpa using (map_mul χ (a,1) (b,1))
  map_nonunit' a ha := χ.map_nonunit (by
    intro h
    exact ha (h.map (MonoidHom.fst R S)))

noncomputable def lemma32ProductCharacterRight {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar (R × S) ℂ) : MulChar S ℂ where
  toFun b := χ (1,b)
  map_one' := χ.map_one'
  map_mul' a b := by simpa using (map_mul χ (1,a) (1,b))
  map_nonunit' b hb := χ.map_nonunit (by
    intro h
    exact hb (h.map (MonoidHom.snd R S)))

lemma lemma32_product_character_factorization {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar (R × S) ℂ) (a : R) (b : S) :
    χ (a,b)=lemma32ProductCharacterLeft χ a*lemma32ProductCharacterRight χ b := by
  change χ (a,b)=χ (a,1)*χ (1,b)
  rw [← map_mul]
  simp

lemma lemma32_product_character_finite_sum {R S : Type*}
    [CommMonoid R] [CommMonoid S] [Fintype R] [Fintype S]
    (χ : MulChar (R × S) ℂ) (f : R → R) (g : S → S) :
    (∑ x : R × S, χ (f x.1,g x.2)) =
      (∑ a : R, lemma32ProductCharacterLeft χ (f a))*
        (∑ b : S, lemma32ProductCharacterRight χ (g b)) := by
  simp_rw [lemma32_product_character_factorization]
  rw [Fintype.sum_prod_type,Finset.sum_mul_sum]

end ZhangLS.Spec
