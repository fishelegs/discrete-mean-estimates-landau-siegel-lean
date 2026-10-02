# Full homogeneous finite-model ratio certificate

Read REPORT.md for definitions and scope, and REVIEW.md for independent review. For all twelve frozen Hermitian models and nonzero complex4-vectors, |ell|²/(R Q)<1/2. This is not a Lean or actual-character asymptotic theorem.

From the repository root:

    sha256sum -c audit/mollifier_ratio/SHA256SUMS
    python3 -S audit/mollifier_ratio/certify_ratio.py

Optional diagnostics require mpmath:

    python3 audit/mollifier_ratio/ratio_diagnostic.py 70
    python3 audit/mollifier_ratio/ratio_diagnostic.py 100
    python3 audit/mollifier_ratio/source_moment_check.py

The first diagnostic is one independent implementation run at two precisions. The source-moment check is another independent implementation transcribed directly from the four source integrals. They are cross-checks, not proof premises. The rational certificate uses only the Python standard library.

inputs/ contains byte-identical published Section18 matrix and quadrature snapshots. New scalar/mixed moments are computed independently by certify_ratio.py. The source/provenance files name the original source snapshots; full PDFs are not bundled. Original certificate and numerical outputs are unchanged. Current editorial scope wording deliberately does not exclude a different beta construction or a changed true matrix after B-basis reconstruction.
