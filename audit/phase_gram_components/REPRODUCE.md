# Reproduce the phase/Gram component verification

Use the committed Lean 4.30.0 toolchain and lake manifest, from the repository root. A clean setup needs the pinned Mathlib dependencies/cache. Serial compilation is sufficient.

```sh
lake build
lake env lean -j1 audit/CloudPhaseGramComponentsAxioms.lean > .lake/phase-gram-audit.log
python3 audit/phase_gram_components/check_audit.py .lake/phase-gram-audit.log
python3 tools/generate_spec_all_imports.py --check
python3 tools/generate_all_imports.py --check
python3 tools/check_no_placeholders.py
python3 tools/check_lean_structure.py
python3 tools/spec_audit.py --strict
python3 audit/phase_gram_components/finite_regressions.py
python3 audit/phase_gram_components/verify_package.py
```

The strict scanner intentionally exits 1 for its 445 candidates. It is not an all-clear test: compare its single new candidate with STRICT_AUDIT_REVIEW.md, retaining historical reviews. Fresh Lean replay prints full public types, direct references, generated owners and transitive axioms. The included hashes bind historical logs; no platform-dependent build cache is uploaded. Finite exact tests are regressions, not replacements for the Lean proofs.
