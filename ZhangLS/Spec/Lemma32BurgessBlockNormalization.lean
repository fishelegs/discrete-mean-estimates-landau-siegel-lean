import ZhangLS.Spec.Lemma32BurgessNormalization
set_option autoImplicit false
namespace ZhangLS.Spec

lemma lemma32_burgess_block_normalization_fourth {A B U V T N L Q W : ℝ}
    (hA : 0<A) (hB : 0<B) (hV : 0<V) (hT0 : 0≤T) (hN0 : 0≤N)
    (hL : 0≤L) (hW : 0≤W) (hU : A/(2*V)≤U)
    (hT : T^4≤(A*N)^2*(3*A*N*L)*Q) (hQ : Q≤W*B^3)
    (hN : N≤2048*A*B) : (T/(U*B))^4≤98304*V^4*N^2*L*W := by
  have hn := lemma32_burgess_normalization_fourth hA hB hV hT0 hU hT
  have hp := (le_div_iff₀ (mul_pos hA (pow_pos hB 4))).mp hn
  have hcoef : (0 : ℝ)≤48*V^4*N^3*L :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hV.le 4))
      (pow_nonneg hN0 3)) hL
  have hq := mul_le_mul_of_nonneg_left hQ hcoef
  have hc : ((T/(U*B))^4*(A*B))*B^3≤(48*V^4*N^3*L*W)*B^3 := by
    have hh := hp.trans hq
    convert hh using 1 <;> ring
  have hf := (mul_le_mul_iff_left₀ (pow_pos hB 3)).mp hc
  have hcoef2 : (0 : ℝ)≤48*V^4*N^2*L*W :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hV.le 4))
      (sq_nonneg N)) hL) hW
  have hscale := mul_le_mul_of_nonneg_left hN hcoef2
  have hfinal : (T/(U*B))^4*(A*B)≤(98304*V^4*N^2*L*W)*(A*B) := by
    calc
      _ ≤ 48*V^4*N^3*L*W := hf
      _ = (48*V^4*N^2*L*W)*N := by ring
      _ ≤ (48*V^4*N^2*L*W)*(2048*A*B) := hscale
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (mul_pos hA hB)).mp hfinal

end ZhangLS.Spec
