import ZhangLS.Spec.Lemma162RawLocalSeries

/-! Uniform polynomial-tail bounds for the actual raw local correction.
All coefficients/phase bounds are explicit; no analytic-product premise occurs. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2500000

noncomputable def lemma162RawP1 (b v : ℂ) : ℂ := -(1+2*v)*b
noncomputable def lemma162RawQ1 (v : ℂ) : ℂ := -(2+v)
noncomputable def lemma162RawPTail (b v z : ℂ) : ℂ := (1+2*v)*b^2-b^3*z
noncomputable def lemma162RawQTail (v z : ℂ) : ℂ := (1+2*v)-v*z
noncomputable def lemma162RawSTail (b v z : ℂ) : ℂ := -b*v*(1+2*v)+b*v*(b+v)*z
noncomputable def lemma162RawPQTail (b v z : ℂ) : ℂ :=
  lemma162RawPTail b v z+lemma162RawQTail v z+lemma162RawP1 b v*lemma162RawQ1 v +
    (lemma162RawP1 b v*lemma162RawQTail v z+lemma162RawQ1 v*lemma162RawPTail b v z)*z +
      lemma162RawPTail b v z*lemma162RawQTail v z*z^2
noncomputable def lemma162RawLinear (F00 F01 F10 lam b v : ℂ) : ℂ :=
  (1+2*v)*(v*F01+lam*b*F10)-(2+v+b+2*v*b)*F00
noncomputable def lemma162RawTail (F00 F01 F10 F11 lam b v z : ℂ) : ℂ :=
  (F00-lam*F10-F01+lam*F11)*lemma162RawPQTail b v z +
    (lam*F10-lam*F11)*lemma162RawQTail v z +
    (F01-lam*F11)*lemma162RawPTail b v z + lam*F11*lemma162RawSTail b v z

lemma lemma162_raw_polynomial_expansion (F00 F01 F10 F11 lam b v z : ℂ)
    (hv : v=1 ∨ v=-1) :
    lemma162RawPolynomial F00 F01 F10 F11 lam b v z =
      F00+lemma162RawLinear F00 F01 F10 lam b v*z+
        z^2*lemma162RawTail F00 F01 F10 F11 lam b v z := by
  rcases hv with rfl | rfl
  all_goals simp only [lemma162RawPolynomial,lemma162RawP,lemma162RawQ,lemma162RawS,
    lemma162RawLinear,lemma162RawTail,lemma162RawPQTail,lemma162RawPTail,
    lemma162RawQTail,lemma162RawSTail,lemma162RawP1,lemma162RawQ1]
  all_goals ring

lemma lemma162_norm_sum_four (a b c d : ℂ) :
    ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
  calc
    _ ≤ ‖a+b+c‖+‖d‖ := norm_add_le _ _
    _ ≤ ‖a+b‖+‖c‖+‖d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_add_le _ _

lemma lemma162_raw_small_polynomial_bounds (b v z : ℂ)
    (hb : ‖b‖≤1) (hv : ‖v‖≤1) (hz : ‖z‖≤1) :
    ‖lemma162RawP1 b v‖≤3 ∧ ‖lemma162RawQ1 v‖≤3 ∧
      ‖lemma162RawPTail b v z‖≤4 ∧ ‖lemma162RawQTail v z‖≤4 ∧
        ‖lemma162RawSTail b v z‖≤5 := by
  have hk : ‖1+2*v‖≤3 := by
    calc
      _ ≤ ‖(1:ℂ)‖+‖(2:ℂ)‖*‖v‖ := by simpa only [norm_mul] using norm_add_le (1:ℂ) (2*v)
      _ ≤ 1+2*1 := by norm_num; linarith
      _ = 3 := by norm_num
  have hvb : ‖b+v‖≤2 := (norm_add_le b v).trans (by linarith)
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [lemma162RawP1,norm_mul,norm_neg]
    calc
      ‖1+2*v‖*‖b‖ ≤ 3*1 := mul_le_mul hk hb (norm_nonneg _) (by norm_num)
      _ = 3 := by norm_num
  · rw [lemma162RawQ1,norm_neg]
    calc
      ‖2+v‖ ≤ ‖(2:ℂ)‖+‖v‖ := norm_add_le _ _
      _ ≤ 3 := by norm_num; linarith
  · unfold lemma162RawPTail
    calc
      _ ≤ ‖(1+2*v)*b^2‖+‖b^3*z‖ := norm_sub_le _ _
      _ = ‖1+2*v‖*‖b‖^2+‖b‖^3*‖z‖ := by rw [norm_mul,norm_pow,norm_mul,norm_pow]
      _ ≤ 3*1^2+1^3*1 := by gcongr
      _ = 4 := by norm_num
  · unfold lemma162RawQTail
    calc
      _ ≤ ‖1+2*v‖+‖v‖*‖z‖ := by simpa only [norm_mul] using norm_sub_le (1+2*v) (v*z)
      _ ≤ 3+1*1 := by gcongr
      _ = 4 := by norm_num
  · unfold lemma162RawSTail
    calc
      _ ≤ ‖b‖*‖v‖*‖1+2*v‖+‖b‖*‖v‖*‖b+v‖*‖z‖ := by
        simpa only [norm_mul,norm_neg] using norm_add_le (-b*v*(1+2*v)) (b*v*(b+v)*z)
      _ ≤ 1*1*3+1*1*2*1 := by gcongr
      _ = 5 := by norm_num

lemma lemma162_raw_pq_tail_bound (b v z : ℂ)
    (hb : ‖b‖≤1) (hv : ‖v‖≤1) (hz : ‖z‖≤1) : ‖lemma162RawPQTail b v z‖≤57 := by
  obtain ⟨hp1,hq1,hpt,hqt,hst⟩ := lemma162_raw_small_polynomial_bounds b v z hb hv hz
  have hcross : ‖lemma162RawP1 b v*lemma162RawQTail v z+
      lemma162RawQ1 v*lemma162RawPTail b v z‖≤24 := by
    calc
      _ ≤ ‖lemma162RawP1 b v‖*‖lemma162RawQTail v z‖+
          ‖lemma162RawQ1 v‖*‖lemma162RawPTail b v z‖ := by
        simpa only [norm_mul] using norm_add_le
          (lemma162RawP1 b v*lemma162RawQTail v z) (lemma162RawQ1 v*lemma162RawPTail b v z)
      _ ≤ 3*4+3*4 := by gcongr
      _ = 24 := by norm_num
  unfold lemma162RawPQTail
  calc
    _ ≤ ‖lemma162RawPTail b v z+lemma162RawQTail v z‖+
      ‖lemma162RawP1 b v*lemma162RawQ1 v‖+
      ‖(lemma162RawP1 b v*lemma162RawQTail v z+lemma162RawQ1 v*lemma162RawPTail b v z)*z‖+
      ‖lemma162RawPTail b v z*lemma162RawQTail v z*z^2‖ := lemma162_norm_sum_four _ _ _ _
    _ ≤ (‖lemma162RawPTail b v z‖+‖lemma162RawQTail v z‖)+
      ‖lemma162RawP1 b v‖*‖lemma162RawQ1 v‖+
      ‖lemma162RawP1 b v*lemma162RawQTail v z+lemma162RawQ1 v*lemma162RawPTail b v z‖*‖z‖+
      ‖lemma162RawPTail b v z‖*‖lemma162RawQTail v z‖*‖z‖^2 := by
        simp only [norm_mul,norm_pow]
        gcongr
        exact norm_add_le _ _
    _ ≤ (4+4)+3*3+24*1+4*4*1^2 := by gcongr
    _ = 57 := by norm_num

lemma lemma162_raw_tail_bound (F00 F01 F10 F11 lam b v z : ℂ) (M : ℝ)
    (hM : 0≤M) (h00 : ‖F00‖≤M) (h01 : ‖F01‖≤M) (h10 : ‖F10‖≤M) (h11 : ‖F11‖≤M)
    (hlam : ‖lam‖≤5) (hb : ‖b‖≤1) (hv : ‖v‖≤1) (hz : ‖z‖≤1) :
    ‖lemma162RawTail F00 F01 F10 F11 lam b v z‖≤773*M := by
  obtain ⟨hp1,hq1,hpt,hqt,hst⟩ := lemma162_raw_small_polynomial_bounds b v z hb hv hz
  have hpqt := lemma162_raw_pq_tail_bound b v z hb hv hz
  have hA : ‖lam*F10‖≤5*M := by rw [norm_mul]; gcongr
  have hC : ‖lam*F11‖≤5*M := by rw [norm_mul]; gcongr
  have hAm : ‖lam*F10-lam*F11‖≤10*M := (norm_sub_le _ _).trans (by linarith)
  have hBm : ‖F01-lam*F11‖≤6*M := (norm_sub_le _ _).trans (by linarith)
  have hD : ‖F00-lam*F10-F01+lam*F11‖≤12*M := by
    have h := lemma162_norm_sum_four F00 (-(lam*F10)) (-F01) (lam*F11)
    simp only [← sub_eq_add_neg,norm_neg] at h
    linarith
  unfold lemma162RawTail
  calc
    _ ≤ ‖(F00-lam*F10-F01+lam*F11)*lemma162RawPQTail b v z‖+
      ‖(lam*F10-lam*F11)*lemma162RawQTail v z‖+
      ‖(F01-lam*F11)*lemma162RawPTail b v z‖+‖lam*F11*lemma162RawSTail b v z‖ :=
        lemma162_norm_sum_four _ _ _ _
    _ ≤ (12*M)*57+(10*M)*4+(6*M)*4+(5*M)*5 := by simp only [norm_mul]; gcongr
    _ = 773*M := by ring

end ZhangLS.Spec
