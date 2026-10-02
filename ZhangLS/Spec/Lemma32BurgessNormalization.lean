import ZhangLS.Spec.Lemma32ActualBurgessParameters
set_option autoImplicit false
namespace ZhangLS.Spec

lemma lemma32_burgess_normalization_fourth {A B U V T N L Q : ℝ}
    (hA : 0<A) (hB : 0<B) (hV : 0<V) (hT0 : 0≤T)
    (hU : A/(2*V)≤U) (hT : T^4≤(A*N)^2*(3*A*N*L)*Q) :
    (T/(U*B))^4≤48*V^4*N^3*L*Q/(A*B^4) := by
  have hUpos : 0<U := (div_pos hA (mul_pos (by norm_num) hV)).trans_le hU
  have hAU : A/U≤2*V := by
    apply (div_le_iff₀ hUpos).mpr
    have hh := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) hV)).mp hU
    nlinarith
  have hr0 : 0≤T/(U*B) := div_nonneg hT0 (mul_pos hUpos hB).le
  have he : (T/(U*B))*(A*B)=(A/U)*T := by
    field_simp <;> ring
  have hr : (T/(U*B))*(A*B)≤2*V*T := by
    rw [he]
    exact mul_le_mul_of_nonneg_right hAU hT0
  have hp := pow_le_pow_left₀ (mul_nonneg hr0 (mul_pos hA hB).le) hr 4
  have hleft : ((T/(U*B))*(A*B))^4 = (T/(U*B))^4*(A*B)^4 := mul_pow _ _ _
  have hright : (2*V*T)^4=16*V^4*T^4 := by ring
  rw [hleft, hright] at hp
  have hm := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ)≤16*V^4)
  have hc : (T/(U*B))^4*(A*B)^4≤48*V^4*A^3*N^3*L*Q := by
    calc
      _ ≤ 16*V^4*T^4 := hp
      _ ≤ 16*V^4*((A*N)^2*(3*A*N*L)*Q) := hm
      _ = _ := by ring
  apply (le_div_iff₀ (mul_pos hA (pow_pos hB 4))).mpr
  have hf : ((T/(U*B))^4*(A*B^4))*A^3≤(48*V^4*N^3*L*Q)*A^3 := by
    convert hc using 1 <;> ring
  exact (mul_le_mul_iff_left₀ (pow_pos hA 3)).mp hf

end ZhangLS.Spec
