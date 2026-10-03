# Corrected joint root–mollifier phase: a finite positive-mass bridge

Source-level derivation, 2026-10-03. This is a new finite analytic argument, not a Lean theorem and not a reproof of BPZ Proposition 4.1. The original hypothesis (A), with exponent −2022, and the original target exponent −2024 are unchanged.

## 1. Precise outcome and scope

Let ψ be the actual real primitive character of conductor D, let L=log D, P=exp(L⁹), and let q be prime in the original P-window (the proof only needs q≥P and the inequalities below). Average over the primitive even characters modulo q, with probability expectation E₊ and cardinality

\[
N_q=(q-3)/2,\qquad c_q=(q-1)/(q-3)\le2.
\]

Use the literal arithmetic functions and the literal mollifier

\[
\nu=1*\psi,\quad \upsilon=\mu*(\mu\psi),\quad X=D^{20},
\quad M_\chi=\sum_{a\le X,\,D\nmid a}\frac{\upsilon(a)\chi(a)}{\sqrt a},
\quad S_\chi=\sum_{b\le X}\frac{\nu(b)\chi(b)}{\sqrt b}.
\]

Here S is an auxiliary finite inverse polynomial, not the full weighted AFE branch. Write

\[
r_\chi=\epsilon(\chi)\epsilon(\chi\psi),\qquad
U_\chi=r_\chi M_\chi/\overline{M_\chi}\quad(M_\chi\ne0).
\]

For sufficiently large D under (A), this note proves

\[
\boxed{\quad
\mathbb P_+\{M_\chi\ne0:\ |1+U_\chi|\le2h\}
\le {1+21\delta\over22-3542h^2},\qquad 0\le h<1/\sqrt{161},
\quad}\tag{1.1}
\]

where δ is completely specified in (7.3) and

\[
\delta=O(L^{-1399/84}),\qquad
\mathbb P_+(M_\chi=0)=O(L^{-1979/2}).\tag{1.2}
\]

In particular, with h=L⁻¹,

\[
\mathbb P_+\{M_\chi\ne0:\ |1+U_\chi|>2/L\}
\ge {21\over22}-O(L^{-2}).\tag{1.3}
\]

All constants are absolute, with one conductor threshold after the original uniform Lemma 3.1 threshold. This is a genuine positive-mass estimate for the corrected joint phase. It is not an o(1) concentration bound, almost-all nonvanishing, a bound under Zhang's weighted zero measure, or a judgment about the published CM/BPZ main theorems.

## 2. Inputs and uniform ranges

The exceptional-character tail input is the already proved actual Lemma 3.1 below. Separately, Section 6 invokes the published hyper-Kloosterman bound cited by CM (Smith, Theorem 6). That is an external deep theorem used at source level; it has not been formalized in this repository. This note therefore does not claim that the whole bridge follows solely from the existing Lean library.

\[
T:=\sum_{D^4<a\le X}{\nu(a)^2\over a}
\le\sum_{D^4<a\le\lfloor P^2\rfloor}{\nu(a)^2\over a}
\le1260L^{-2011}.\tag{2.1}
\]

We use X≤P², q∤D, q≥5, and

\[
2X^{22}=2D^{440}<q.\tag{2.2}
\]

These hold for all sufficiently large D when q≥exp(L⁹). No varying ε, varying fixed-C theorem, or growing approximation degree is invoked.

Set

\[
H=H_X=\sum_{n\le X}1/n\le1+20L,
\qquad J=H_{X^{22}}\le1+440L.
\]

The elementary divisor bounds used below are

\[
\tau_a\tau_b\le\tau_{ab},\qquad
\tau_a(mn)\le\tau_a(m)\tau_a(n),\qquad
\sum_{n\le Y}{\tau_a(n)\over n}\le H_Y^a.
\tag{2.3}
\]

They follow from prime-power coefficient inequalities or the standard ordered-factorization interpretation; the last inequality follows by dropping the product cutoff in the a-fold harmonic convolution. The literal local values of ν and υ give

\[
\upsilon*\nu=\delta_1,\qquad |\upsilon(n)|\le\nu(n)\le\tau_2(n).
\tag{2.4}
\]

Ramified primes are retained throughout.

## 3. Exact even-primitive orthogonality, including principal subtraction

If Aχ=Σₙ≤Y aₙχ(n)/√n and 2Y<q, then all n are units modulo q, congruence n≡m mod q is exactly n=m, and n≡−m mod q is impossible. Thus

\[
\mathbb E_+|A_\chi|^2
=c_q\sum_{n\le Y}{|a_n|^2\over n}
-{1\over N_q}\left|\sum_{n\le Y}{a_n\over\sqrt n}\right|^2
\le c_q\sum_{n\le Y}{|a_n|^2\over n}.\tag{3.1}
\]

The negative term is the exact principal-character subtraction, not an omitted error. In all high-moment applications below Y≤X²², so (2.2) rules out both ordinary and negative aliases.

## 4. Both hard cutoffs and the ramified deletion

First retain the deleted terms, writing M₀χ=Σₐ≤X υ(a)χ(a)/√a and R₀χ=M₀χSχ−1. Its coefficient c(n) vanishes for n≤X, since then both cutoffs are vacuous and υ*ν=δ₁. It is supported on n≤X². For n>X, any contributing pair a,b≤X has a>D¹⁰ or b>D¹⁰, hence a>D⁴ or b>D⁴. Consequently, on every positive integer n,

\[
|c(n)|\le2(f*g)(n),\quad
f(a)=\nu(a)\mathbf1_{D^4<a\le X},\quad
g(b)=\nu(b)\mathbf1_{b\le X}.\tag{4.1}
\]

This is a coefficientwise bound on the actual residual after both hard cutoffs. It does not replace the rectangular cutoff by an unjustified total-product cutoff.

Now set M_D=M₀−M. At every p|D, one has υ(p)=−1 and υ(pʲ)=0 for j≥2. Therefore:

* If D is not squarefree, every term with D|a has υ(a)=0, so M_D=0 exactly.
* If D is squarefree, υ(Dm)=μ(D)υ(m) when (m,D)=1, and is zero otherwise. Thus

\[
M_{D,\chi}={\mu(D)\chi(D)\over\sqrt D}
\sum_{m\le X/D,\,(m,D)=1}{\upsilon(m)\chi(m)\over\sqrt m}.\tag{4.2}
\]

No τ(D) factor is needed. Define R_D=M_DS. After the displayed D⁻¹ᐟ² unit factor, its coefficients are bounded by τ₂*τ₂=τ₄, supported up to X²/D. Let

\[
R=MS-1=R_0-R_D.\tag{4.3}
\]

This identity includes the entire deletion error for every real primitive conductor.

## 5. High moments of the inverse error, with fixed orders only

Let 1≤j≤11. By (4.1), the coefficients of R₀ʲ are bounded by 2ʲ(f*g)^{*j}. Expanding the 2j ordered variables, Cauchy gives

\[
\big((f*g)^{*j}(n)\big)^2
\le\tau_{2j}(n)
\sum_{a_1b_1\cdots a_jb_j=n}
\prod_{i=1}^j f(a_i)^2g(b_i)^2.
\]

Submultiplicativity of τ₂ⱼ and then dropping the total product cutoff yield

\[
\sum_n{\big((f*g)^{*j}(n)\big)^2\over n}
\le A_j^j B_j^j,
\]

where

\[
A_j=\sum_{D^4<a\le X}{\nu(a)^2\tau_{2j}(a)\over a},
\qquad B_j=\sum_{b\le X}{\nu(b)^2\tau_{2j}(b)\over b}.
\]

One more Cauchy inequality and (2.3) give the complete divisor budget

\[
A_j\le T^{1/2}
\left(\sum_{a\le X}{\nu(a)^2\tau_{2j}(a)^2\over a}\right)^{1/2}
\le T^{1/2}H^{8j^2},
\qquad B_j\le H^{8j},\tag{5.1}
\]

because

\[
\nu(n)^2\tau_{2j}(n)^2\le\tau_{16j^2}(n),\qquad
\nu(n)^2\tau_{2j}(n)\le\tau_{8j}(n).
\]

The resulting polynomial has length at most X²ʲ≤X²², so (3.1) applies and proves

\[
\boxed{\quad
\|R_0\|_{2j}\le2c_q^{1/(2j)}T^{1/4}H^{4j^2+4j}.
\quad}\tag{5.2}
\]

The deletion term is bounded independently: its jth power, after the factor D⁻ʲᐟ²χ(D)ʲ, has coefficient envelope τ₄ⱼ and length (X²/D)ʲ. Hence

\[
\|R_D\|_{2j}\le D^{-1/2}c_q^{1/(2j)}J^{8j}.\tag{5.3}
\]

The estimate is also valid when R_D=0.

Taking j=1 gives

\[
\|R\|_2\le\eta:=
2c_q^{1/2}T^{1/4}H^8+D^{-1/2}c_q^{1/2}J^8
=O(L^{-1979/4}).\tag{5.4}
\]

For the higher endpoint, (5.2) gives

\[
\|R_0\|_{20}\le2c_q^{1/20}T^{1/4}H^{440},
\qquad
\|R_0\|_{22}\le2c_q^{1/22}T^{1/4}H^{528}.
\]

The respective powers of L are −251/4 and +101/4. The second bound need not tend to zero. Interpolation is nonetheless valid and useful:

\[
\|R_0\|_{21}
\le\|R_0\|_{20}^{10/21}\|R_0\|_{22}^{11/21}
\le2c_q^{1/21}T^{1/4}H^{10208/21}.
\]

Using (5.3) at j=11 and monotonicity of probability-space norms for R_D, define

\[
\boxed{\quad
\|MS-1\|_{21}\le e:=
2c_q^{1/21}(1260L^{-2011})^{1/4}H^{10208/21}
+D^{-1/2}c_q^{1/22}J^{88}.
\quad}\tag{5.5}
\]

The exponent is exactly

\[
-{2011\over4}+{10208\over21}=-{1399\over84}<0.
\tag{5.6}
\]

Thus e=O(L⁻¹³⁹⁹ᐟ⁸⁴). The constants 21 and 22 are fixed before D. No sequence of increasing moment orders is hidden here. Formula (5.4), with T replaced by 1260L⁻²⁰¹¹, defines an entirely explicit η bound too.

The suggested annulus statement is also a valid byproduct, although the phase argument does not use it. From (3.1), E₊|M|² and E₊|S|² are each at most c_qH⁴. For any fixed a>0, Markov and |MS|≥1/2 outside |MS−1|>1/2 give

\[
\mathbb P_+\{|M|\notin[L^{-2-a},L^{2+a}]\}
\le4\eta^2+5c_qH^4L^{-4-2a}=O_a(L^{-2a})+O(L^{-1979/2}).
\tag{5.7}
\]

This alone would not license an unbounded polynomial approximation on the exceptional set. Sections 7–8 instead use the global inverse-error identity.

## 6. The twisted root moments, including every unit condition

For even primitive χ and any primitive ψ of conductor D coprime to q, the CRT identity for Gauss sums, with the parity factors included in ε, is

\[
r_\chi=\chi(D)\psi(q)\epsilon(\psi)\tau(\chi)^2/q.
\tag{6.1}
\]

Evenness of χ makes the parity factors on the two sides agree also when ψ is odd. This step needs primitivity and (q,D)=1; it does not need D squarefree.

For k≥1 and u,v with q∤uv, write t=u/v in F_q*. Expanding τ(χ)²ᵏ and using even-primitive orthogonality gives, with C=ψ(q)ε(ψ),

\[
\sum_\chi^+r_\chi^k\chi(t)
={C^k(q-1)\over2q^k}
\sum_{\substack{a_1,\ldots,a_{2k}\in\mathbb F_q^*\\
D^kt a_1\cdots a_{2k}=\pm1}}
e_q(a_1+\cdots+a_{2k})
-{C^k\over q^k}.\tag{6.2}
\]

The last term is exact because the unrestricted additive sum is (−1)²ᵏ=1; multiplying by the unit character monomial does not change principal subtraction. The two constrained sums are hyper-Kloosterman sums at the nonzero arguments ±(Dᵏt)⁻¹. CM's cited bound is 2k q^{(2k−1)/2} for each, uniformly in that argument. Therefore

\[
\left|\mathbb E_+ r_\chi^k\chi(u)\overline{\chi(v)}\right|
\le b_{q,k}:={2q^{-k}\over q-3}+4kc_q q^{-1/2}.\tag{6.3}
\]

This is the exact CM Gauss-sum computation with a unit monomial inserted; it is not an assumed joint-distribution theorem. Its constants are explicit in k, and below k≤21 only. The hyper-Kloosterman input is the same published external deep theorem as in CM Lemma 4, citing Smith, Theorem 6. It is assumed here as a source-level theorem and is not an existing Lean proof in this repository.

## 7. Convert the inverse error into the correct phase moments

Define U*=U when M≠0 and U*=1 when M=0. This is always a unit complex number. Let

\[
W=MS,\qquad T_\chi=M_\chi\overline{S_\chi},\qquad Z_\chi=r_\chi T_\chi.
\]

The exact identity

\[
Z=U^*\overline W\tag{7.1}
\]

holds both when M≠0 and when M=0; in the latter case both sides vanish. For every 1≤k≤21,

\[
\begin{aligned}
\mathbb E_+|(U^*)^k-Z^k|
&=\mathbb E_+|1-W^k|\\
&\le\sum_{j=1}^k\binom{k}{j}\mathbb E_+|W-1|^j
\le(1+e)^k-1.
\end{aligned}\tag{7.2}
\]

This controls the entire family, including all large-value and small-value tails. There is no annulus restriction and no bad-set probability multiplied by an uncontrolled polynomial supremum.

The full spectral ℓ¹ norm of T, after combining equal monomials if desired, is bounded by

\[
\left(\sum_{a\le X}{|\upsilon(a)|\over\sqrt a}\right)
\left(\sum_{b\le X}{\nu(b)\over\sqrt b}\right)
\le4XH^2=:A.
\]

Indeed Σₙ≤X τ₂(n)/√n≤2√X H. Thus the full ℓ¹ norm of Tᵏ is at most Aᵏ. Every monomial is χ(u/v), where u and v are products of at most k integers ≤X. Every factor is a unit since X<q, so q∤uv; no assumption that a product itself is below q is required for (6.3). We conclude

\[
|\mathbb E_+Z^k|\le b_{q,k}A^k.
\]

A single explicit bound valid for all 1≤k≤21 is

\[
\boxed{\quad
|\mathbb E_+(U^*)^k|\le\delta:=(1+e)^{21}-1
 +\left({2q^{-1}\over q-3}+84c_q q^{-1/2}\right)(4XH^2)^{21}.
\quad}\tag{7.3}
\]

The last term has the transparent size

\[
O\big(e^{-L^9/2+420L}(1+20L)^{42}\big).
\]

It therefore pays for every coefficient and every monomial with a large surplus. Together with (5.5), this proves δ=O(L⁻¹³⁹⁹ᐟ⁸⁴). Since M=0 implies |MS−1|=1, (5.4) independently gives

\[
\mathbb P_+(M=0)\le\eta^2=O(L^{-1979/2}).\tag{7.4}
\]

## 8. Fejér anti-concentration and positive mass

Use the nonnegative polynomial

\[
F_{21}(z)={1\over22}|1+z+\cdots+z^{21}|^2
=1+2\operatorname{Re}\sum_{k=1}^{21}(1-k/22)z^k.
\]

By (7.3), E₊F₂₁(−U*)≤1+21δ. If |1+U*|≤2h, then |1−(−U*)ᵏ|≤2kh and hence Re(−U*)ᵏ≥1−2k²h². The exact sum

\[
\sum_{k=1}^{21}(1-k/22)k^2={21\cdot22\cdot23\over12}={1771\over2}
\]

gives

\[
F_{21}(-U^*)\ge22-3542h^2.
\]

Nonnegativity now proves (1.1), and independently removing M=0 gives the explicit positive-mass form

\[
\boxed{\quad
\mathbb P_+\{M\ne0,\ |1+U|>2h\}
\ge1-\eta^2-{1+21\delta\over22-3542h^2}.
\quad}\tag{8.1}
\]

The denominator is positive precisely for h<1/√161. Taking h=L⁻¹ proves (1.3).

## 9. What this does and does not close

At the fixed center, the literal AFE multiplication gives, for M≠0 and real v,

\[
FM=v+B+U(v+\overline B),\qquad
|FM-v(1+U)|\le2|B|.
\]

If a separate proof establishes v≥1/2 and E₊|B|²=o(L⁻²), then (8.1) at h=L⁻¹ and Markov's inequality yield

\[
\mathbb P_+(F\ne0)\ge21/22-o(1).
\]

More explicitly one subtracts 4L² E₊|B|² in addition to the errors in (8.1). This is conditional on that separate full B theorem. The locally repaired Y-truncation in the prior range analysis is not such a theorem.

The method deliberately stops at 21 fixed phase moments. The stated generic divisor majorants do not make the 22nd inverse-error norm small. A measure uniform on the 22nd roots of unity has its first 21 nontrivial moments exactly zero and an atom of mass 1/22 at −1. Therefore the moment information actually established here cannot itself imply o(1) mass near −1. The 1/22 obstruction is sharp for these finite-moment data; it is not a claim about the actual character family.

Most importantly, no estimate in this note is under the character-dependent high-zero, good-family, c*ω weighted measure. The phase then also contains conductor and Γ factors. The previously stated Z1 (weighted AFE error) and Z2 (weighted signed phase) remain unproved. Even a full unweighted fixed-center joint equidistribution theorem would not automatically supply them.

## 10. Uniform fixed-height extension, without a zero-sampling claim

The entire joint-phase estimate extends uniformly to every deterministic real t. Replace M and S by

\[
M_\chi(t)=\sum_{a\le X,\,D\nmid a}{\upsilon(a)\chi(a)\over a^{1/2+it}},
\qquad S_\chi(t)=\sum_{b\le X}{\nu(b)\chi(b)\over b^{1/2+it}}.
\]

The residual coefficients in Section 4 acquire only the factor n⁻ⁱᵗ, so convolution cancellation, every coefficient majorant, every family moment, and every spectral ℓ¹ budget are unchanged. For any unit λ(t) independent of the running χ, the same proof applies to

\[
U_\chi(t)=\lambda(t)r_\chi M_\chi(t)/\overline{M_\chi(t)}.
\]

Indeed each twisted root moment is merely multiplied by λ(t)ᵏ. In the even family, the full functional-equation phase has exactly this form: with a=0 or 1 the parity of ψ and Q=q√D/π, one may take

\[
\lambda(t)=Q^{-2it}
{\Gamma((1/2-it)/2)\Gamma((1/2+a-it)/2)
\over\Gamma((1/2+it)/2)\Gamma((1/2+a+it)/2)},
\qquad |\lambda(t)|=1.
\]

This yields (1.1) and (8.1), with the same errors independent of t, for the unweighted family at each fixed height, including heights of order L⁵¹⁹. It establishes no corresponding uniform estimate for the weighted AFE error B(t), its derivatives, or a moving-character sample.

One cannot choose t=t(χ) at each character's zero in this conclusion: the bound controls an average for a common deterministic t, not an average along a character-dependent selection. Such a selection can correlate perfectly with the phase. At an actual zero, the exact AFE already imposes v_t+U\overline{v_t}=−(B+U\overline B); where its error is small, it forces the corrected phase near the cancelling value. The same issue remains under the good-family F/G approximation. Thus the auxiliary product M·conj(S) is a useful unweighted polynomial surrogate here; this note does not assert that inserting it as a new R4 trial gives an independent direction or a strict gain after evaluation at the original zeros.

## 11. Source audit and status

Definitions, local values, parity, AFE, and the same-side B are read directly from BPZ arXiv:2012.04392v2, author source `source.tex`, especially lines 148–207, 215–253, 323–358. CM arXiv:2303.05277v2, author source `Annalen_preprint_2.tex`, lines 141–171 and 248–304 supply the literal mollifier and the root Gauss/hyper-Kloosterman calculation.

The actual uniform ν² tail and coefficient inequalities are the already published repository inputs recorded in `audit/CLOUD_SHORT_UPSILON_STATUS.md`, `ZhangLS/Spec/Lemma31.lean`, `ShortUpsilonArithmetic.lean`, and `ShortUpsilonEnergy.lean`. These were read, not rebuilt or modified.

The original phase-interface audit is retained: this argument works with rM/conj(M), and neither asserts the printed bare phase identity nor diagnoses the published main theorems. New claims here are source-level finite inequalities. `check_finite.py` provides arithmetic/regression checks only; it is not an asymptotic proof or a Lean certificate.
