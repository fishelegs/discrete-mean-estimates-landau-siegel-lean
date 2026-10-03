# Reproduce at this publication revision

Use the committed Lean 4.30.0 toolchain and lake manifest, from the repository root:

```sh
lake build
lake env lean -j1 audit/CloudGramSmoothingAxioms.lean > .lake/gram-smoothing-audit.log
python3 audit/gram_smoothing_components/check_audit.py .lake/gram-smoothing-audit.log
python3 tools/generate_spec_all_imports.py --check
python3 tools/generate_all_imports.py --check
python3 tools/check_no_placeholders.py
python3 tools/check_lean_structure.py
python3 tools/spec_audit.py --strict
python3 audit/gram_smoothing_components/verify_package.py
```

The strict scan intentionally retains exit 1. Review the one new local-derivation candidate and retain the historical candidate reviews. The complete audit prints public types, direct references and generated owners; it does not count only the actualGram name prefix. Log hashes identify the recorded run. No platform-dependent cache or internal runtime logs are uploaded. Mutable progress ledgers are excluded from the proof package manifest.
