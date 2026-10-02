# Independent Section 18 quadratic-form audit (frozen)

## Result

For the original coefficients (2.26), evidence-based repairs of the identified
Section 9 denominator, Section 17 kernel label, Appendix B tail phase, and the
Section 12 high-range phase model do **not** recover the required numerical
inequality (2.32). In the most upstream-supported finite model audited here,

- c1 = 7.05010466979205041964393903214…
- c2 = 6.98709229778193001759470409477…
- c3 = −6.99092771402436271881273463731… − 0.02031059081994386174945506766… i
- Q = c1+c2+2Re(c3) lies in
  [0.0553415395252549996131, 0.0553415395252549996132]

The target is Q<0.001. This model has an exact-rational interval LDL certificate
showing its global constrained minimum, with the H11 coefficient fixed to 1 and
all three iotas free over C, lies in

[0.0249294244390953127716, 0.0249294244390953127717].

Thus changing only iota2, iota3, iota4 cannot produce Q<0.001 in this model.
The same obstruction holds in all twelve explicitly distinguished branches:
each original-coefficient Q is >0.05, and each constrained minimum is >0.024.
These are model statements, **not** a proof that no other analytic correction,
mollifier parameters, different construction, or proof can recover the main
theorem. No character satisfying (A) is constructed; no vacuity argument is used.

## Classification and trust boundary

The literal source does not define κ4, so it has no unambiguous numerical c3
without resolving that notation. All twelve branches use the κ2 expression
forced by expansion of the previously defined B and H2. This is an algebraically
motivated repair, not a selected free value for κ4.

The branch key is `denominator:high:tail`:

- denominator `.504`: literal (9.5),(9.6); `.5`: denominator forced by their
  preceding log(P2)log(P3) formula and (2.21)
- high `printed`: use 2e2*; `exact`: use the exact high-residue **model** A+conj(B)
- tail `printed`: retain displayed Lemma 15.1 e1j'' and e1*; `collapsed`: use
  Section 18's asserted cancellation as if it were exact; `upstream`: use
  e1j''=−iπj b*, derived from Appendix B's final residue expression

The highlighted branch is `.5:exact:upstream`. The collapsed branches are
comparisons with a paper approximation, not assertions that cancellation is
exact. The Section 12 exact-high branch does not prove the actual arithmetic
asymptotic or its passage through the outer sums. Full analytic mean-value,
error, contour, uniformity, and character-theoretic bridges remain outside this
package. The leading numerical matrices are fully specified and certified;
their equality to actual normalized character means is not certified here.

At the original coefficients, the uncollapsed source-table branch with derived
`.5` denominator gives Q in
[0.0552006550935136584591,0.0552006550935136584592]. The literal `.504` denominator
instead gives [0.0630223469664643413684,0.0630223469664643413685]. Neither is close
to .001. The printed cancellation itself fails its epsilon<10^-5 budget; its
upstream-tail repair restores that **local** cancellation budget, as detailed in
DERIVATION.md. Neither restores the final inequality.

## Central replay

Run from any directory:

    python /tmp/section18-quadratic-audit/certify_independent.py

This uses only Python's standard library and writes the deterministic exact
endpoints to `/tmp/section18-quadratic-audit/certified.json`. It prints each
branch's Q and constrained minimum and asserts all the stated common strict
bounds. It does not invoke Lean, the repository, Lake, caches, network, or GitHub.

To replay the exact certificate and check every matrix entry and reported scalar against the separately stored 70-digit calculation:

    python /tmp/section18-quadratic-audit/check_replay.py

This comparison also uses only the standard library. It has passed for all twelve branches.

For the separately implemented, non-certifying 70-digit quadrature/spectral check:

    python /tmp/section18-quadratic-audit/explore_independent.py

That check requires mpmath. Its outputs are explicitly exploratory, including
eigenvalues and stationary coefficients. The certified global minimum uses
interval LDL and completion of squares, not those floating-point eigenvalues.
The scripts were independently written for this audit; no existing broad
Section 18 exploratory script was imported or executed. Section 12 formulas
were cross-checked against the earlier phase audit, but all integrals and
certification arithmetic were implemented afresh.

## Files

- DERIVATION.md: source-to-model formulas, conjugations, repair rationale, scope
- CERTIFICATE_METHOD.md: exact arithmetic, Taylor enclosure, and LDL proof
- source-excerpts.txt: numbered frozen TeX excerpts
- certify_independent.py / certified.json / certified.txt: exact certificate
- explore_independent.py / exploratory.json / exploratory.txt: independent mp check
- check_replay.py: exact replay plus independent-output containment checks
- integration_manifest.json and SHA256SUMS: frozen identities and replay order

Source: Yitang Zhang, arXiv:2211.02515v1,
https://arxiv.org/abs/2211.02515v1 and https://arxiv.org/pdf/2211.02515v1.
All computation used the supplied official TeX/PDF; their hashes are in the
manifest. This audit does not overwrite the live Lean repository or prior audit.
