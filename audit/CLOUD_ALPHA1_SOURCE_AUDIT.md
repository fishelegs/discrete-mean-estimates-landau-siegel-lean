# Source-alignment issue: alpha-one notation

Inspected on 2026-10-02: the official [arXiv:2211.02515v1 PDF](https://arxiv.org/pdf/2211.02515v1), [HTML](https://arxiv.org/html/2211.02515v1), and [TeX source](https://arxiv.org/src/2211.02515v1). The arXiv record lists only v1. The source is one gzip-compressed `lsz3__2_.tex`; the uncompressed UTF-8 source SHA256 is `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`.

The source defines `\al` as `\alpha` on line47. There are **28 occurrences** of `\al_1`, and no definition of this subscript-one quantity was located. In contrast, alpha is explicitly defined by (2.10) on source line401, and alpha-two on line1621. Directly inspecting the rendered PDF pages37 and87 confirms an actual subscript1, not an OCR error.

Relevant locations:

- First use: p37, source line1972, in the phase approximation immediately before the reduction of Proposition7.1
- Lemma15.2: p87, source line4335, in its uniform near-one error term
- Lemma15.3: p87, source line4350, in its Euler-product value error
- Further occurrences occur in Sections8,10,12,15–17 and AppendicesA/B

This is a precise unresolved source-specification issue, **not a demonstrated false mathematical claim**. It is not legitimate to choose an arbitrary power of log D for alpha-one and report the original lemmas as proved. Work on15.2 is proving an explicit-rate statement using the defined alpha; comparison with the paper's alpha-one remains a separate obligation. Lemma15.3 also switches the U1j/U2j labels between its definition and conclusion; AppendixA uses U1j throughout. Any interpretation must retain the actual arithmetic coefficients and be stated explicitly.

## Evidence-based reconstruction

The subsequent [explicit-scale reconstruction ledger](CLOUD_ERROR_SCALE_RECONSTRUCTION.md) maps every occurrence and records six formally proved budget interfaces. It keeps original and repaired statements separate and does not declare a new definition of alpha-one.
