#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

REPORT="audit/lean_kernel_verification.txt"
mkdir -p audit
STARTED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
STATUS="FAIL"
SPEC_STATUS="NOT_RUN"
SPEC_MODULE_STATUS="NOT_RUN"
FULL_STATUS="NOT_RUN"
AUDIT_STATUS="NOT_RUN"
REASON="verification did not complete"
LEAN_VERSION="unavailable"
LAKE_VERSION="unavailable"

write_report() {
  {
    echo "LEAN_KERNEL_VERIFICATION=${STATUS}"
    echo "trusted_spec_module_verification=${SPEC_MODULE_STATUS}"
    echo "trusted_spec_kernel_verification=${SPEC_STATUS}"
    echo "full_project_kernel_verification=${FULL_STATUS}"
    echo "audit_regression_kernel_verification=${AUDIT_STATUS}"
    echo "started_at_utc=${STARTED_AT}"
    echo "finished_at_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "pinned_toolchain=$(tr -d '\r\n' < lean-toolchain 2>/dev/null || echo missing)"
    echo "lean_version=${LEAN_VERSION}"
    echo "lake_version=${LAKE_VERSION}"
    echo "reason=${REASON}"
    echo "trusted_spec_modules_command=tools/verify_trusted_spec_modules.sh"
    echo "trusted_spec_command=lake env lean ZhangLS/Spec/All.lean"
    echo "full_project_command=lake build"
    echo "authoritative_command=tools/verify_all_lean.sh"
  } > "$REPORT"
}
trap write_report EXIT

if [[ ! -f lean-toolchain ]]; then
  REASON="lean-toolchain is missing"
  echo "ERROR: $REASON" >&2
  exit 2
fi
if [[ "$(tr -d '\r\n' < lean-toolchain)" != "leanprover/lean4:v4.30.0" ]]; then
  REASON="unexpected Lean toolchain pin"
  echo "ERROR: $REASON" >&2
  exit 2
fi
if ! command -v lean >/dev/null 2>&1; then
  REASON="lean executable is unavailable; no kernel verification was performed"
  echo "ERROR: $REASON" >&2
  exit 127
fi
if ! command -v lake >/dev/null 2>&1; then
  REASON="lake executable is unavailable; no kernel verification was performed"
  echo "ERROR: $REASON" >&2
  exit 127
fi

LEAN_VERSION="$(lean --version | head -1)"
LAKE_VERSION="$(lake --version | head -1)"
printf 'Pinned toolchain: '; cat lean-toolchain
printf 'Lean: %s\n' "$LEAN_VERSION"
printf 'Lake: %s\n' "$LAKE_VERSION"
if [[ "$LEAN_VERSION" != *"version 4.30.0"* ]]; then
  REASON="active Lean version does not match pinned Lean 4.30.0"
  echo "ERROR: $REASON: $LEAN_VERSION" >&2
  exit 2
fi

python3 tools/generate_spec_all_imports.py --check
python3 tools/generate_all_imports.py --check
python3 tools/check_no_placeholders.py
python3 tools/check_lean_structure.py

echo '== Stage 1a/3: trusted Spec modules, individually =='
if tools/verify_trusted_spec_modules.sh; then
  SPEC_MODULE_STATUS="PASS"
else
  SPEC_MODULE_STATUS="FAIL"
  REASON="individual trusted Spec module kernel check failed"
  exit 1
fi

echo '== Stage 1b/3: trusted Spec aggregate =='
if lake env lean ZhangLS/Spec/All.lean; then
  SPEC_STATUS="PASS"
else
  SPEC_STATUS="FAIL"
  REASON="trusted Spec aggregate kernel check failed"
  exit 1
fi

echo '== Stage 2/3: full project kernel check =='
if lake build; then
  FULL_STATUS="PASS"
else
  FULL_STATUS="FAIL"
  REASON="full project lake build failed"
  exit 1
fi

echo '== Stage 3/3: audit regression modules =='
if ! lake env python3 tools/verify_audit_modules.py; then
  AUDIT_STATUS="FAIL"
  REASON="audit regression dependency check or kernel check failed"
  exit 1
fi
AUDIT_STATUS="PASS"

STATUS="PASS"
REASON="Spec modules, Spec aggregate, full project, and audit regressions passed"
echo 'LEAN_KERNEL_VERIFICATION=PASS'
