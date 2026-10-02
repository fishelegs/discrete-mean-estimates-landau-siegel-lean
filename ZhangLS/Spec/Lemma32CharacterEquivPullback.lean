import ZhangLS.Spec.Lemma32ProductQuadraticCharacter
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32CharacterEquivPullback {R S : Type*}
    [CommMonoid R] [CommMonoid S] (e : R ≃* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun a := χ (e a)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul]
  map_nonunit' a ha := χ.map_nonunit (by
    intro h
    have h' := h.map e.symm.toMonoidHom
    exact ha (by simpa using h'))

lemma lemma32_character_equiv_pullback_quadratic {R S : Type*}
    [CommMonoid R] [CommMonoid S] (e : R ≃* S) (χ : MulChar S ℂ) (hq : χ^2=1) :
    (lemma32CharacterEquivPullback e χ)^2=1 := by
  apply MulChar.ext
  intro a
  rw [MulChar.pow_apply_coe,MulChar.one_apply_coe]
  change χ (e (a : R))^2=1
  let u : Sˣ := Units.map e.toMonoidHom a
  have he := congrArg (fun ξ : MulChar S ℂ => ξ (u : S)) hq
  simpa only [MulChar.pow_apply_coe,MulChar.one_apply_coe,Units.coe_map,
    MulEquiv.coe_toMonoidHom] using he

lemma lemma32_character_equiv_pullback_nontrivial {R S : Type*}
    [CommMonoid R] [CommMonoid S] (e : R ≃* S) (χ : MulChar S ℂ) (hn : χ ≠ 1) :
    lemma32CharacterEquivPullback e χ ≠ 1 := by
  intro he
  apply hn
  apply MulChar.ext
  intro a
  let u : Rˣ := Units.map e.symm.toMonoidHom a
  have h := congrArg (fun ξ : MulChar R ℂ => ξ (u : R)) he
  change lemma32CharacterEquivPullback e χ (u : R) = (1 : MulChar R ℂ) (u : R) at h
  rw [MulChar.one_apply_coe] at h ⊢
  simpa [lemma32CharacterEquivPullback,u] using h

lemma lemma32_quartic_character_sum_ring_equiv {R S : Type*}
    [CommRing R] [CommRing S] [Fintype R] [Fintype S]
    (e : R ≃+* S) (χ : MulChar R ℂ) (a b c d : R) :
    (∑ x : R, χ (lemma32QuarticRootProduct a b c d x)) =
      ∑ y : S, lemma32CharacterEquivPullback e.symm.toMulEquiv χ
        (lemma32QuarticRootProduct (e a) (e b) (e c) (e d) y) := by
  apply Fintype.sum_equiv e.toEquiv
  intro x
  change χ (lemma32QuarticRootProduct a b c d x) =
    χ (e.symm (lemma32QuarticRootProduct (e a) (e b) (e c) (e d) (e x)))
  have hp : e (lemma32QuarticRootProduct a b c d x) =
      lemma32QuarticRootProduct (e a) (e b) (e c) (e d) (e x) := by
    simp only [lemma32QuarticRootProduct,map_mul,map_add]
  rw [← hp,e.symm_apply_apply]

end ZhangLS.Spec
