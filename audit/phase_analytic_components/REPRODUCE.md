# Reproduce

Use the pinned Lean 4.30.0 project manifest at this revision, from the repository root:

```sh
lake build
lake env lean -j1 audit/CloudPhaseAnalyticAxioms.lean > .lake/phase-analytic-audit.log
python3 audit/phase_analytic_components/check_audit.py .lake/phase-analytic-audit.log
python3 tools/generate_spec_all_imports.py --check
python3 tools/generate_all_imports.py --check
python3 tools/check_no_placeholders.py
python3 tools/check_lean_structure.py
python3 tools/spec_audit.py --strict
python3 audit/phase_analytic_components/verify_package.py
```

The strict scan intentionally retains exit 1; compare the one new local-derivation candidate with STRICT_AUDIT_REVIEW.json and keep historical reviews. The exact audit prints complete public types, direct references and all generated owned declarations. Log hashes identify the central run; no platform-dependent build cache is uploaded. Historical fingerprints should be reproduced at the publication revision.
