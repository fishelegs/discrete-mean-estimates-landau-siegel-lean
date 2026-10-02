# Reproduce the Section 8 numerical audit

Source: arXiv:2211.02515v1, PDF pages49–50, formulas(8.13)–(8.24), using **all three +0.004 shifts in(8.22)**. The PDF and official TeX agree on these shifts. No missing-shift allegation is made.

Python3.12 and installed mpmath1.3.0 were used. Run:

```sh
python3 audit/section8_numerical/parameterized_quadrature.py
python3 audit/section8_numerical/closed_forms.py
python3 audit/section8_numerical/interval_closed_forms.py
```

The first method reconstructs F/G from limiting beta parameters and numerically integrates. The second independently enters the six printed coefficient tables and integrates polynomial-times-exponential terms by closed-form moments. It additionally cross-checks those literal tables by quadrature. The third evaluates the same closed-form expression using directed interval arithmetic and the proven mathlib bracket3.14159265358979323846<pi<3.14159265358979323847 (`Real.pi_gt_d20`, `Real.pi_lt_d20`).

For frequency v=i*pi*r, the moments used are J0=(exp(vT)-1)/v, Jk=T^k exp(vT)/v-kJ(k-1)/v; when r=0 they are T^(k+1)/(k+1). All input decimals are rational numbers; no fitted parameter or omitted source shift is used. Complex conjugates are applied exactly as defined below(8.23).

The mpmath interval implementation's conjugate method raised an internal ValueError in this environment, so the standard identity conjugate(z)=real(z)-i*imag(z) is implemented explicitly. Interval endpoints are computed at60 decimal working precision. No outcome depends on rounding to the printed five-decimal numbers.

These are reproducible independent numerical and interval calculations. They are **not Lean-kernel proofs of the integral definitions**, nor proofs/counterexamples about actual Dirichlet characters or the paper's final theorem. The independent Fraction-only Taylor certificate is now included: run `python3 audit/section8_numerical/certify.py`. It uses degree40 for the Section8 integrals, exact rational interval operations and an explicit geometric-series tail bound; see `CERTIFICATE_METHOD.md`. Its wider independent c1 enclosure is[7.050104669792050376,7.050104669792050463]. This too remains a computer-assisted certificate outside the Lean kernel. See the parent audit report for the exact scope and logical impact.
