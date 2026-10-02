# Independent full-ratio certificate review

## Verdict

**ACCEPT the stated homogeneous finite-model inequality, with the scope qualifications below.** All twelve frozen fixed-support/frequency Hermitian models satisfy, for every nonzero z in C^4,

    |L^T z|^2 / (R z* M z) < 1/2.

There is no H11=1 normalization and no excluded z1=0 chart. This is a reproducible rational computer-assisted result with a reviewed source-to-residue-model derivation. It is not a Lean theorem, an actual-character mean asymptotic, a proof that the paper's main theorem is false, or a proof excluding repairs that change the true matrix after arithmetic reconstruction.

## Source derivation

Primary source: /tmp/zhang-2211.02515-source.tex, SHA256 5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b. Matching PDF: /tmp/zhang-2211.02515.pdf, SHA256 4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713. Both match frozen provenance.

- Original ramps, tent and conjugated H2 coefficients: TeX 576–613, (2.21)–(2.30).
- P7.1 weights q=(1/2,2,3/2) and 1/alpha factor: TeX 1830–1850. L8.1 supplies the Hermitian symmetrization: TeX 2187–2189. L8.2/L8.4 have Mellin symbols s-beta_j and (s+beta_(j+1))(s+beta_(j+2))/s: TeX 2339–2415. The harmonic partial-summation normalization is at TeX 2436–2477, (8.10)–(8.12).
- Thus in t=log(n)/log(P), A_j phi=-phi'-i*pi*j*phi and B_j psi=-psi'+i*pi*(6-j)*psi-pi^2*ab*integral_t^infinity psi, with ab=(6,3,2). The ramp output exactly recovers the f/g tables and their 1/r factors. The tent recovers L10.1/L10.2, TeX 2719–2851, including B_j w=-pi^2*ab*h/2 below the support. Dropping that below-support term would give incorrect mixed coefficients.
- TeX 2695–2717, especially (10.1), fixes the order of the four moments. With T first-linear and second-conjugate-linear, L=(T(phi1,w),T(phi2,w),T(wR,phi3),T(wR,phi2)). Since H2=conj(z3)H13+conj(z4)H12, these last components multiply z3,z4 without another conjugation.
- J2 is the reflected tent w(1-t+alphaTilde); the source's symmetric tent makes this w(t+.004-alphaTilde), on [.496+alphaTilde,.5+alphaTilde]. TeX 609–613 and L11.2 at 3319–3352 establish the conductor D*t0 shift. Setting alphaTilde to zero and replacing log(P2)/log(P) by .5 are limiting-model steps, not finite-D equalities. PDF p65 was independently rendered and inspected.
- For the original real tent, integration by parts gives integral w'*(integral_t^infinity w)=integral w^2, with zero boundary contribution. The real part of A_j w B_j w is (w')^2+11*pi^2*w^2 after integration because j(6-j)+ab=11. With sum q=4 and the Hermitian factor 2, R=8/pi*integral(w')^2+88*pi*integral(w^2)=32/(pi*h)+88*pi*h/3, h=1/250. Thus R=2546.8477030083465747... is correct. For generalized profiles the integration-by-parts statement requires suitable absolute continuity/piecewise smoothness; the source tent has it.
- PDF p100 was independently rendered and inspected. It confirms the missing C* on the left of (18.3) and the upper-half y_1j printed where L10.2 prescribes y_2j. The reviewed R derivation uses the preceding S_j and L10.2 rather than either typo.

A separate diagnostic, source_moment_check.py, directly transcribes the d3,d4,d5,d6 integrals of (10.12)–(10.17), TeX 2953–3168. It does not import either new implementation. At 85-digit mpmath precision all four real and imaginary coefficient values are contained in the frozen rational intervals. The output is source_moment_check.json. This is independent diagnostic evidence, not a rigorous floating-point error bound.

## Computation, Hermitian orientation and positivity

Reviewed frozen files: /tmp/mollifier-repair-admissibility/certify_ratio.py and interval_engine.py.

- certify_ratio.py:19–46 implements the correct profiles, integrals, operators and L orientation. Lines 47–52 use the correctly derived closed R; the overlap assertion with the independently evaluated residue expression is a cross-check, not itself an equality proof.
- interval_engine.py:11–35 performs outward-rounded rational fixed-point real arithmetic. Complex rectangle operations at 42–56 are inclusive; zero denominators are excluded. Lines 59–65 enclose pi by Machin's identity and alternating series. Lines 92–106 enclose the degree-80 exponential tail by 2*M^81/81!, with M<40, so successive remaining terms have ratio below 1/2.
- Pointwise Taylor remainders are stored as interval constant coefficients. This is sound for integration here: every monomial is nonnegative on every integration interval. Coefficientwise integration bounds even a t-dependent remainder; separate endpoint subtraction only widens the enclosure. Polynomial products are full convolutions, not truncated products.
- The imported M data are byte-identical to the published audit/section18_numerical/certified.json, SHA256 cbc3bcc982f46c81572e246b9fbd66645a02ef4c91ebc748ce706d8c45481441. Quadrature data and the original certifier also match provenance. The source builder's matrix() assigns conjugate-reflected entries, and check_structure.py independently verifies real diagonal intervals and exact conjugate-reflected boxes in all twelve 4x4 matrices.
- certify_ratio.py:61–70 is the ordinary Hermitian LDL recurrence, with every real pivot lower endpoint positive. Discarding the imaginary enclosure is justified by the exact Hermitian identities; merely checking that the imaginary interval contains zero would not suffice without those identities.
- Lines 79–86 form A=[[M,conj(L)],[L^T,R/2]], with the correct orientation for ell(z)=L^T z. The leading four positive pivots prove M positive definite, so every nonzero z has a positive denominator. The fifth pivot encloses the real Schur complement R/2-L^T M^-1 conj(L). Its positivity proves the strict bound for all nonzero complex vectors. The smallest leading-four pivot lower bound exceeds .00874; the smallest final pivot lower bound exceeds 217.6812680560.

The largest of the twelve certified maxima is in [0.41452913819742913056,0.41452913819742913057]. The .5:exact:upstream value is in [0.40716299028789405383,0.40716299028789405384]. No optimization or parameter search is used.

## Scope and wording corrections

ACCEPT coefficient-only obstruction within these twelve precisely frozen models. REJECT extending it to actual arithmetic means without their missing analytic bridges, or to all mollifier/profile/frequency/core-beta constructions.

REPORT.md conclusion 3 says core beta shifts 'cannot legitimately be tuned'. This must be limited to preserving the current original construction and proved interfaces. Suggested replacement:

    Under the current normalization and original zero-gap/positivity/residue framework, pi and the core beta shifts are not independent numerical tuning parameters. Changing that framework would require new proofs and lies outside this certificate. Varying the sufficiently large fixed c-prime has no leading-model effect. Coefficient variation alone is ruled out in these twelve models.

A source-correct reconstruction of the actual B and its coefficient basis could change M. That possibility is not excluded. The Appendix B terminal-expression branch remains a specified model, not a repaired actual Lemma 15.1. Likewise, overlap of independently computed interval boxes and high-precision diagnostic agreement do not prove the character-sum-to-model identities. The actual mean-value, contour, error, endpoint/boundary and finite-D-to-limit arguments remain separate obligations. This review introduces no theorem, axiom or parameter search and compiles no Lean.

## Reproduction and integrity

All review writes and reruns are isolated in /tmp/mollifier-ratio-review. The frozen package, original TeX/PDF, live repository and GitHub were not edited.

    cd /tmp/mollifier-ratio-review/replay
    sha256sum -c SHA256SUMS
    python3 -S certify_ratio.py
    python3 -S /tmp/mollifier-ratio-review/check_structure.py
    python3 /tmp/mollifier-ratio-review/source_moment_check.py

The first two pass; generated ratio-certificate.json and replay stdout are byte-identical to the frozen originals. Stdlib output is recorded in /tmp/mollifier-ratio-review/stdlib-replay.log. Independent PDF renders are source-p65.png and source-p100.png. The copied original matrix certifier is additionally replayed by matrix-replay/check_replay.py; its result is recorded in matrix-replay.log.

## Repository replay

Use `python3 -S audit/mollifier_ratio/certify_ratio.py` for the exact full-ratio replay. The prior matrix certificate is reproducible with `python3 -S audit/section18_numerical/check_replay.py`. The independent diagnostic is `python3 audit/mollifier_ratio/source_moment_check.py`; its certificate input path is the sole relocation edit to that script.
