# Reproduce the focused arithmetic verification

Use the repository-pinned Lean4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.

    lake build ZhangLS.Spec.SquareNuTailConvolutionCapstone
    lake env lean audit/CloudSquareNuTailCentralAudit.lean > square-nu-audit.log
    python3 audit/square_nu_tail/check_audit.py square-nu-audit.log
    python3 audit/square_nu_tail/verify_package.py
    python3 audit/square_factor_tail/verify_bundle.py --repo-root . --rerun

The central original checks used direct pinned Lean with one thread and a4096MiB allocation limit, immutable cached dependencies, and independently rebuilt private outputs. Sixteen dependency/proof compiles passed before the full182-entry audit and its exact second pass. Reproduction above builds the same final qualified modules normally.

The package verifier checks immutable mathematical source/audit bytes and244 project-source pins. The source companion's exact finite checks supplement its universal arguments. Full repository CI and the signed global theorem are separate from this focused acceptance.
