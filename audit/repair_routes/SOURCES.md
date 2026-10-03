# Sources and version scope

The reports use the following fixed arXiv versions. Official version records were checked on 2026-10-03; mathematical locators are those verified in the attached independent reviews. Versioned records, rather than a mutable latest-version link, identify the cited text.

- Yitang Zhang, *Discrete mean estimates and the Landau-Siegel zero*, [arXiv:2211.02515v1](https://arxiv.org/abs/2211.02515v1), 4 November 2022. Definitions (2.2), (2.6)–(2.15); Lemmas 2.3, 3.1, 4.6–4.8, 5.2; Proposition 7.1; (8.5); Sections 8 and 12–17; Appendix B. [Official TeX source](https://arxiv.org/src/2211.02515v1). The source is used for definitions and claimed conditional reductions, not as validation of its final theorem.
- H. M. Bui, Kyle Pratt, Alexandru Zaharescu, *Exceptional characters and nonvanishing of Dirichlet L-functions*, [arXiv:2012.04392v2](https://arxiv.org/abs/2012.04392v2), 10 December 2020. Gamma weights in Section 3, Proposition 4.1, [Section 6.1 deletion](https://arxiv.org/html/2012.04392v2#S6.SS1). The new deletion bound in this package is proved independently and does not invoke Proposition 4.1 outside its range.
- Martin Čech, Kaisa Matomäki, *A note on exceptional characters and non-vanishing of Dirichlet L-functions*, [arXiv:2303.05277v2](https://arxiv.org/abs/2303.05277v2), 12 December 2023. [Proposition 3, Lemma 4 and its proof](https://arxiv.org/html/2303.05277v2#S4), equations (7)–(8). The inserted-character and parity/conductor extensions in the reports are derived there, not attributed as printed theorems.
- Djordje Milićević, Xinhua Qin, Xiaosheng Wu, *Bilinear forms with Kloosterman sums and moments of twisted L-functions*, [arXiv:2511.07550v1](https://arxiv.org/abs/2511.07550v1), 10 November 2025. [Theorem 2.2](https://arxiv.org/html/2511.07550v1#S2.SS1), specialized to a prime modulus. This is the bilinear estimate used for the bare two-polynomial bound.
- Martin Čech, Kaisa Matomäki, *On optimality of mollifiers*, [arXiv:2501.12526v3](https://arxiv.org/abs/2501.12526v3), 17 October 2025. [Section 2](https://arxiv.org/html/2501.12526v3#S2) only, for complete-ratio moment algebra and the near-degenerate warning. No family-specific optimality theorem is transferred.
- NIST Digital Library of Mathematical Functions, [gamma reflection formula 5.5.3](https://dlmf.nist.gov/5.5#E3), for the exact parity factor.
- Felipe Gonçalves, [analytic number theory notes, Section 2](https://w3.impa.br/~goncalves/NotesDavenport.pdf), for quadratic characters and fundamental discriminants. The reports also give the local conductor argument, including the 2-part. This auxiliary hosted reference is not an immutable arXiv record.

## Source coordinates and repository statements

The TeX line coordinates in the admissible-shift reports refer to the inspected Zhang v1 source file with SHA-256

    5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b

Line offsets are secondary locators; equation, lemma, and section labels above identify the mathematical passages independently. The paper itself is not repackaged here. The checks do not require a paper download.

The Lean filenames and line coordinates in SOURCE_REVIEW.md record a read-only statement-scope audit as of the report date. They are not claims of a new compiled theorem, and can move as the repository changes. They distinguish existing original-shift ports from the newly derived leading source-weight model.
