# Second independent review: limiting-profile obstruction and finite-D precision

Date: 2026-10-03. Repository inspected read-only at `d199d72a51149930ad06e3ddae8dfedf590b8ba7`. No Lean compilation, cache rebuild, dependency installation, repository modification, or publication was performed. The archived report has only path/presentation updates; the mathematical verdict is unchanged.

## Verdict: ACCEPT the structural proof, within its explicit algebraic scope

The claimed inequality

\[
 |L(\phi,\psi)|^2\le R\{Q(\phi)+Q(\psi)+2\Re C(\phi,\psi)\}
\]

is correct for the specified `.5:exact_model:upstream_tail` functional. The three-dimensional kernel assertion is correct for the glued variable, not for the pair space. This excludes a strict *leading-model* ratio above one within this model. It does not prove an actual-character mean identity, a finite-D obstruction, global optimality of all mollifiers, or falsity of the main theorem.

**Finite-D decision:** do not proceed from the current exported errors to a signed `L^-8` correction matrix. That bounded route's precision hypotheses currently fail. Several available bounds are substantially larger; the most immediate ones are the Section 8 weighted ξ boundary bound and the common exceptional-family bound. A fixed smooth decomposition can be investigated, but it needs a genuine source-level projected mean/error theorem. A numerical negative eigenvalue would not discharge this condition.

The full precision audit is in [ERROR_BUDGET.md](ERROR_BUDGET.md). A concrete source-specific improvement of the exceptional-family part is derived in [PREFIX_TAU4_BRIDGE.md](PREFIX_TAU4_BRIDGE.md): on the finite prefix, the true convolution coefficients admit a tau4 bound, leading to an L^-46 rate if the narrow mean bridge is formalized. This refinement is mathematically justified but has not been compiled in this review. One useful favorable distinction is that the local Euler-center errors in Sections 15 and 16 can already be smaller than `L^-8` after *correct* relative normalization; their coarse absolute exported powers are not unavoidable errors.

## What was checked independently

Inputs:

- `PROOF.md (original pre-archive report)`, SHA256 `97b904ed45f134f684ed3ace751eddf65c1250747f42e6e039b38cfffea368a2`
- Original source `arXiv:2211.02515v1 TeX source`, SHA256 `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`
- The associated diagnostic script/results, the repository's frozen model/source mappings, and the actual Lean theorem statements listed in the budget

`check_independent.py` is a separate exact SymPy calculation. It imports no source-model classes, original checker functions, or floating-point matrix data. It passes 26 exact checks, recorded in `exact-checks.json`: operator-to-Q integration, the cross identity including the low tail, reflection, the joined gauge form, mixed orientation, exact R, a nonzero overlap-cancellation pair, the three null modes' ODE and boundary conditions, and the optional covariance-kernel calculation. Reproduce with:

```
python audit/profile_barrier/check_independent.py
```

These checks catch algebraic mistakes; they do not replace the functional proof or verify arithmetic means. The initial floating-point diagnostic had additional source dependencies. This archive uses the independent self-contained exact script for reproducibility.

## Function class, endpoints, and scalar convention

A precise adequate space is

\[
 X_1=\{\phi\in H^1(0,1;\mathbb C):\phi=0\text{ on }(.504,1)\},\quad
 X_2=\{\psi\in H^1(0,1;\mathbb C):\psi=0\text{ on }(.5,1)\}.
\]

The continuous representatives have zero right traces at `.504` and `.5`. No zero trace at `0` is required. Continuous, piecewise-C1 profiles with finitely many pieces and square-integrable derivative are a convenient dense subclass. A statement for “piecewise C1” without square-integrability or a finite-partition convention should retain the H1 qualification. All displayed functionals are continuous on these H1 spaces, so their extension is legitimate. This is continuity of the *defined algebraic functionals*, not an extension theorem for the arithmetic sums.

Use `q(t)=conj(psi(1-t))`, `h=phi+q`, `W_h(t)=∫_t^1 h`. Then `h∈H1`, `W_h∈H2`, and `f=e^(3πit/2)W_h∈H2` has `f(1)=0`; its other traces are free. Reflection and conjugation make this an ordinary Hermitian form on `(phi,q)`, or on the pair space with scalar multiplication `(phi,psi)↦(z phi,conj(z) psi)`. It is not complex-linear in both raw profile entries simultaneously. This is exactly why C is bilinear in `(phi,psi)` and the mixed expression is `B(phi,J)+B(J2,psi)`.

## Q, cross orientation, and the indispensable tail

With `W'=-a`, integration by parts gives

\[
 \Re\int_0^1 a'\overline W
 =-\Re(a(0)\overline{W(0)})+\int_0^1|a|^2.
\]

The endpoint at `1` vanishes because `W(1)=0`, including when `a(1)` is nonzero. The six weighted sums in the first report are correct. They produce coefficients `8/π`, `48`, `88π`, `-24π`, and `-48π²` in Q with the reported signs. The polarization B is Hermitian and linear in its first argument.

Original (8.5) is `Z^-1 H1 H2`; there is no missing conjugation in C. For the source H2 coefficient convention, its matrix entry is `M[H2,H1]=C`, with conjugate reverse entry. In the cross expansion, integration of `-12π[y'A+B0 phi']` changes `64π phi y` to `88π phi y` and contributes `-12π psi(0) a_high`. Writing `A=a_high-W_phi` produces the remaining constant mass term. `A` remains nonzero above the support of phi. Deleting that region loses precisely the low-region contribution and destroys the gluing identity.

The verified exact identities are

\[
 C=B(\phi,q)-8i\phi(0)\psi(0)-12\pi\psi(0)W_\phi(0),
\]
\[
 Q(q)=Q(\psi)+24\pi\Re(\psi(0)\overline{W_\psi(0)}),
\]
\[
 N=Q(h)-24\pi\Re(h(1)\overline{W_h(0)})
       +16\Im(h(0)\overline{h(1)}).
\]

There is no extension of the joined interval to `1.004`. The overlap changes the decomposition of h; it does not lengthen its domain.

## Gauge, null modes, and positivity

Direct substitution gives exactly

\[
 E(f)=\frac8\pi\int_0^1\left(|f''|^2-\frac{5\pi^2}{2}|f'|^2
      +\frac{9\pi^4}{16}|f|^2\right)
 -12\pi\Re(f'(0)\overline{f(0)})
 -16\Re(f'(0)\overline{f'(1)}).
\]

The polarized integration-by-parts boundary form has the reported three natural conditions. Each of

\[
 \cos(\pi t/2),\quad\cos(3\pi t/2),\quad
 \sin(\pi t/2)+\sin(3\pi t/2)
\]

satisfies them, the essential condition `f(1)=0`, and the fourth-order ODE. Thus its pairing with every admissible H2 test function is zero before positivity is invoked.

The stated coefficients A, B, C match `f(0), f'(0), f'(1)`. Their subtraction gives `g(0)=g'(0)=g(1)=g'(1)=0`. Therefore `g'∈H1` has equal endpoint traces and zero integral. Periodic mean-zero Wirtinger applies to its real and imaginary parts and yields

\[
 E(f)=E(g)\ge\frac3\pi\|g''\|_2^2+\frac{9\pi^3}{2}\|g\|_2^2.
\]

Equality is exactly the three-dimensional displayed f span. The inverse map `h=e^(-3πit/2)((3πi/2)f-f')` identifies its image with `span_C{e^(-iπjt):j=1,2,3}`.

The pair-space kernel is the full preimage of this span under gluing. In addition to representatives of these three modes, it contains all `phi=b`, `psi(t)=-conj(b(1-t))` for `b∈H1_0(.5,.504)`. Consequently it is infinite-dimensional. A remainder controlled only by `||h||H1` would force all actual errors to vanish on every overlap cancellation pair, which has not been proved. Use a norm of both profiles (and, for generalized Mellin formulas, their necessary higher derivatives), or explicitly restrict to a bounded chosen right inverse of gluing.

## Mixed form and source proposition mapping

For the unit-height tent J of width `w=.004`, `∫J=w/2`, `∫|J'|²=4/w`, `∫J²=w/3`. Its endpoint and imaginary terms vanish. Therefore

\[
 R=Q(J)=32/(\pi w)+88\pi w/3.
\]

The reflected-conjugated term acquires `+12π(w/2)conj(psi(0))` under B, and the joined boundary polarization contributes its negative. This proves `B_N(h,J)=B(phi,J)+B(J2,psi)=L` and `B_N(J,J)=R`. Cauchy–Schwarz for the positive semidefinite form gives the claimed inequality, with equality `h-(L/R)J` in the three-mode span.

The original numbering matters:

| Model quantity | Intended original arithmetic object and location |
|---|---|
| N | `(a𝒫)^-1 Ξ1`, the weighted square norm of `H1+Z conj(H2)` in (8.2)–(8.5). Same-side components are (8.23), (9.7); cross component is assembled in Section 18, (18.1). The requested small energy is (2.32), used for **Proposition 2.5** |
| L | `(a𝒫)^-1 Ξ1*`, the mixed expression in (2.17), evaluated in Section 10, (10.17). Its large absolute value is **Proposition 2.4**, a lower bound, not an upper bound |
| R | `(a𝒫)^-1 Σ c* |J1|² ω`, the J1 square norm in (2.33), evaluated/bounded in Section 18. Together with N it bounds Ξ2* by Cauchy in **Proposition 2.5**. The exact R above belongs to the selected complete limiting operator; the printed argument only needs its coarse bound `<3000` |
| Transfer remainder | Ξ3* in (2.20), controlled by **Proposition 2.6** via the squared norm of `J1−Z conj(J2)` in (11.1). It is not R |

Original (2.18) is `|Ξ1*|≤Ξ2*+Ξ3*`. A finite-D mixed-ratio contradiction therefore also needs the transfer error at the same resolved precision. If `ε_D=L^-8`, bounded normalized H2 energy and a Cauchy treatment would require the normalized J-transfer **square norm** to be `o(ε_D²)=o(L^-16)` to make Ξ3*/(a𝒫)=o(ε_D). A direct projected negative N direction would instead contradict (2.16) and avoid this additional J-transfer obligation entirely.

## Optional formalization shortcut: ACCEPT

For periodic mean-zero u with weak derivative v, `∫v=0` and

\[
 u(t)=\int_0^1K(t,s)v(s)ds,\qquad
 K(t,s)=\mathbf1_{s<t}+s-t-\tfrac12.
\]

The representation follows from the fundamental theorem for H1 and the mean-zero condition. The subtraction `-t-1/2` is harmless because `∫v=0`. By piecewise polynomial integration,

\[
 H(s,r)=\int K(t,s)K(t,r)dt=\tfrac12 B_2(|s-r|),
 \qquad\iint H^2=1/720.
\]

Fubini is justified by bounded K and `v∈L2` on a finite interval. Product-space Cauchy–Schwarz gives

\[
 \|u\|_2^2=\iint H(s,r)v(s)\overline{v(r)}\,dsdr
 \le\frac1{\sqrt{720}}\|v\|_2^2.
\]

This is weaker than sharp Wirtinger but sufficient: `sqrt(720)>5π²/2`. A rational certificate uses `π<22/7` and

\[
 720-\frac{25}{4}(22/7)^4=264620/2401>0.
\]

For u=g′ and v=g″ it proves positive coercivity of the clamped residual, though with a smaller coefficient than `3/π`. No Fourier-series completeness theorem is needed. It is an optional elementary analytical proof, not an already compiled Lean theorem.

## Source-fidelity caveats

The F/G operators restrict to the original beta6/beta7 ramps and reproduce the source (8.13)–(8.22) tables. The C orientation agrees with (8.5), and its reverse-conjugate assembly with (12.9). The full tail agrees with the selected upstream branch, including the terminal Appendix B computation. The endpoint product agrees with (17.4)–(17.5).

This does not identify every printed approximation in Sections 12/15/18 with the selected exact model. In particular, the `.5` denominator and upstream-tail branch are explicit audited choices; inconsistent printed alternatives cannot all be silently declared equal. Nor do agreement on source ramps and algebraic density prove generalized arithmetic means. The actual beta offsets, `P2=P^.5 T^-10`, conductor Dp, finite J2 displacement, smoothing, and all uniform arithmetic errors still have to be retained in an actual mean theorem.

Statement-name consistency check: all 41 backticked theorem/definition identifiers inventoried at the review stage were located in the repository or the explicitly identified private corrected-residue package. `source-statement-manifest.json` records these locations and content hashes; it is not a recompilation certificate. The centrally promoted `Lemma171MainLowerBound.lean` content exactly matches the privately verified frozen source (SHA256 `42a17229c95adbfa61ce075f9b05d17a69d72fb9822698645322c8010e81fb47`).
