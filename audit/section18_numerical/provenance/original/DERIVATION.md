# Source interpretation and verified model identities

All decimal parameters are exact decimal rationals. Use a=3/2, b=5/2,
r1=.504, r2=.5, r3=.498, h=.004. Actual βj logP tends to iπj and
β6 logP=iπa, β7 logP=iπb. The T correction in P2 contributes o(1) to
these limiting constants; it is not an exact finite-D identity.

## 1. The coefficient family and conjugations

(2.23)–(2.27), TeX 592–621, define
H1=H11+iota2 H12 and H2=conj(iota3)H13+conj(iota4)H12.
For z=(1,iota2,iota3,iota4), the exact pointwise expression in (2.32) is

|H11 + z2 H12 + z3 Z conj(H13) + z4 Z conj(H12)|².

This is a Hermitian quadratic form in z before any asymptotic argument.
The general form with first coefficient x instead of 1 is homogeneous; fixing
x=1 is essential to the constrained-minimum result. Scaling everything toward
zero would also scale the crucial separate mixed-moment lower bound.

(8.2)–(8.5), TeX 2269–2288, split the quadratic expression into c1+c2+2Re(c3),
where the cross term is Z^-1 H1 H2, and therefore is linear in (1,iota2) and
conjugate-linear in (iota3,iota4). The source integral tables f_j6, g_j6,
f_j7, g_j7 in (8.13)–(8.18) are used literally. The Proposition 7.1 weights
are q=(1/2,2,3/2), not the later (3,3,1) weights.

Set c12=b12+conj(b21), c34=b34+conj(b43). Then

c1=c11+iota2 conj(c12)+conj(iota2)c12+|iota2|²c22,
c2=|iota3|²c33+iota3 conj(iota4)c34+iota4 conj(iota3)conj(c34)+|iota4|²c22.

If c3=sum_{u=0,1;v=0,1} K_uv z_u conj(z_{v+2}) (zero-based indices), the
Hermitian matrix M for z*Mz has
M01=conj(c12), M23=conj(c34), M_{v+2,u}=K_uv,
M_{u,v+2}=conj(K_uv), and diagonal (c11,c22,c33,c22).
This fixes every conjugation in the certificate.

This is a rigorously defined free-coefficient **finite model**. The exact
pointwise family is also rigorous. Identifying the model with asymptotic
character means for every fixed coefficient choice still requires the pending
analytic basis-pair identities and error bounds; this package does not infer
those identities from polynomial dependence alone.

## 2. Section 9 denominator

TeX 2621–2623 explicitly has cross terms divided by log(P2)log(P3).
By (2.21), their limiting denominator is (.5)(.498)(logP)².
The .504 in (9.5),(9.6), TeX 2640–2645, conflicts with this substitution.
Changing .504 to .5 is uniquely dictated by the two specified kernels, not
optimization. The source's quoted c34≈−.4526+.19474i agrees with the .5 branch:

c34≈−.45260468988650574849+.19474195230260519579i.

The literal .504 branch gives approximately −.44901258917312078223+
.19319638125258451963i. Both are retained as separate numerical objects.

## 3. Section 17's undefined κ4

(12.2) says B=(H14+iota2 H12)H2, with H14 the H11 sum cut below P^.5.
Section 17 expands (L(s+β1)/L(s)) B G N2 N3 into coefficients ν*.
For n<D^4, each factor index is <D^4<P^.5 for large D. Therefore the H14
factor has κ1 coefficients and H2 has conj(iota3)κ3+conj(iota4)κ2 coefficients.
The κ4 in TeX 4734,4738,4743 must be κ2 if this expansion is to be an expansion
of the previously defined B. There is no independent free fourth kernel.
This coefficient identity does not prove the later diagonal reduction.

At n=1 the leading phases are k1=e^{.756πi}, k2=e^{1.25πi}, k3=e^{.747πi}, so
E0=(k1+iota2 k2)(conj(iota3)k3+conj(iota4)k2).
At finite D, k2=P2^{β7}; the displayed limiting phase drops an o(1) factor.

## 4. Section 15 / Appendix B tail

For r>0 and frequency α∈{3/2,5/2}, write
E_j(r,α)=(1−j/α+j/(α²rπi))e^{αrπi}−j/(α²rπi).
These exactly reproduce e1j', e2j, e3j in TeX 4283–4292, respectively.
An elementary integration by parts gives
E_j(r,α)=(1/r)∫_0^r (1+(α−j)πit)e^{απit}dt=(1/r)∫_0^r f_jα(t)dt.

The printed tail T_j=e1j'' in TeX 4295–4296 is
(j/.756)∫_0^.004[e^{1.5πi(.504−z)}−e^{.75πi}]dz.
Appendix B's actual last residue formula, TeX 5331–5333, gives instead

(j/.756)∫_.5^.504[e^{1.5πi(.504−z)}−e^{.006πi}]dz
= (j/.756)∫_0^h[e^{1.5πiu}−e^{1.5πih}]du
= −iπj b*,  b*=(1/.504)∫_0^h u e^{1.5πiu}du.

This is also the rational residue answer for the H11 tail: the limiting
ζ-ratio is (s−iπj)/s; its action away from t=0 is −iπj dt, applied to the
ramp ((r1−t)/r1)e^{1.5πi(r1−t)} on .5<t<.504.
The pole at s=β6 in the Appendix B bracket cancels because its two exponential
numerators coincide there. The remaining pole at s=0 gives the printed terminal
residue expression. These are verified formal residue/integral identities;
the source's contour error estimates are a separate obligation.

## 5. c3 and the Section 18 cancellation

(13.7), (15.24), (16.17), (17.10) yield the weights
(1,2,1)+(1,1,0)+(1,0,0)=(3,3,1) and the E0 term, all multiplied by −i.
For T_j the selected tail, define
Ej=[E_j(r1,1.5)−T_j+iota2 E_j(r2,2.5)]
   [conj(iota3)E_j(r3,1.5)+conj(iota4)E_j(r2,2.5)].
The uncollapsed displayed model is
c3=−i(3E1+3E2+E3+E0)+e1*+high,
with high=2e2* or A+conj(B), as specified below.

The low term is used directly from (12.15):
e1*=−πb*Σ_j (3,6,3)_j∫_0^.496[conj(iota3)f_j6(.498−z)/.498+
conj(iota4)f_j7(.5−z)/.5]dz.
The printed high term is from TeX 3675:
e2*=4/(.504π)[−.002conj(iota3)/.498−.008conj(iota4)
−2πi conj(iota4)/250²].

With the printed T_j, the cancellation remainder iΣ_j(3,3,1)_j T_j times
its second factor + e1* has real part <−.00007, incompatible with |epsilon|<10^-5.
With the Appendix B-derived T_j=−iπj b*, integration by parts and the above E
identity reduce the remainder exactly to

Σ_{(v,k,r)=(iota3,6,.498),(iota4,7,.5)} conj(v)·(12πb*/r)∫_0^{r−.496}f_2k(t)dt.

Here Σ_j(3,3,1)_j j f_jk=12 f_2k. At the paper coefficients the remainder is
−.00000547392560947683…−.00000728190946970770…i; its norm is certified <10^-5.
Thus a principled repair restores this local budget, but leaves the larger final
numerical obstruction. The `collapsed` branch drops this remainder entirely;
it is only a diagnostic comparison with the paper's compressed display.

## 6. Exact Section 12 high residue model

Let d6=.002, d7=.004, H=.004, β=1.5πi, a_j=jπi,
s_j=(6−j)πi, p_j=−π²(6,3,2)_j. Differentiating the displayed residue expression
in Lemma12.3, with its outer negative sign, gives
W2_j(t)=e^{βt}[−1+(s_j−β)t]+p_j∫_t^H v e^{βv}dv.
The exact limiting Lemma12.1 phase is
W1_j(t)=e^{−βt}[−1+(β−a_j)t].
For k=6,7 use (v_k,r_k,d_k)=(iota3,.498,.002),(iota4,.5,.004).

A=Σ_j q_j Σ_k conj(v_k)/(.504 r_k π)∫_0^{d_k}f_jk(d_k−t)W2_j(t)dt,
B=Σ_j q_j Σ_k v_k/(.504 r_k π)∫_0^{d_k}g_jk(d_k−t)W1_j(t)dt.

(12.9) requires A+conj(B), not A+B, not 2A. The exact-model correction relative
to 2e2* agrees with the separately certified phase audit:
ReΔ≈.00000327768185444876, ImΔ≈.00000121298440173447.
The coefficientwise formulas are retained so that the free-iota model is
well-defined rather than reusing a correction calculated at only one vector.

Actual Π=0 behavior, additive arithmetic errors, endpoint/beta perturbations,
and all low/high/transition passages remain unproved here. No exact-model
constant is promoted to an actual-character theorem.
