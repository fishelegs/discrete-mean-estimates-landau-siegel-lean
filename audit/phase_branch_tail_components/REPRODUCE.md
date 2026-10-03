# Reproduce

Use the pinned Lean 4.30.0 project manifest at this revision, from the repository root:

```sh
lake build
lake env lean -j1 audit/CloudPhaseBranchTailAxioms.lean > .lake/phase-branch-tail-audit.log
python3 audit/phase_branch_tail_components/check_audit.py .lake/phase-branch-tail-audit.log
python3 tools/generate_spec_all_imports.py --check
python3 tools/generate_all_imports.py --check
python3 tools/check_no_placeholders.py
python3 tools/check_lean_structure.py
python3 tools/spec_audit.py --strict
python3 audit/phase_branch_tail_components/verify_package.py
```

The strict scan intentionally retains exit 1 and all historical candidates; this checkpoint adds none. The exact audit enumerates all actual owners, including generated helpers, and prints public types/direct references. Log hashes identify this central run; platform-dependent caches are not uploaded. Historical fingerprints are reproduced at the publication revision.
