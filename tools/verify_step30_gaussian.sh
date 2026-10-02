#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

REPORT="audit/step30_gaussian_kernel_verification.txt"
STATUS="FAIL"
REASON="verification did not complete"
write_report() {
  {
    echo "STEP30_GAUSSIAN_KERNEL_VERIFICATION=${STATUS}"
    echo "pinned_toolchain=$(tr -d '\r\n' < lean-toolchain 2>/dev/null || echo missing)"
    echo "lean_version=$(lean --version 2>/dev/null | head -1 || echo unavailable)"
    echo "reason=${REASON}"
    echo "command=tools/verify_step30_gaussian.sh"
  } > "$REPORT"
}
trap write_report EXIT

EXPECTED_TOOLCHAIN="leanprover/lean4:v4.30.0"
if [[ "$(tr -d '\r\n' < lean-toolchain)" != "$EXPECTED_TOOLCHAIN" ]]; then
  REASON="unexpected Lean toolchain pin"
  echo "ERROR: expected $EXPECTED_TOOLCHAIN in lean-toolchain" >&2
  exit 2
fi
if ! command -v lean >/dev/null 2>&1 || ! command -v lake >/dev/null 2>&1; then
  REASON="Lean or Lake is unavailable"
  echo "ERROR: Lean and Lake are required" >&2
  exit 127
fi
if [[ "$(lean --version | head -1)" != *"version 4.30.0"* ]]; then
  REASON="active Lean version does not match pinned Lean 4.30.0"
  echo "ERROR: active Lean version does not match 4.30.0" >&2
  exit 2
fi

lake build \
  +ZhangLS.Spec.Lemma57GaussianGlobal:olean \
  +ZhangLS.Spec.Lemma57SmoothedSummability:olean
lake env lean audit/Step30GaussianRegression.lean

STATUS="PASS"
REASON="Gaussian modules and terminal theorem API regression compiled successfully"
echo "STEP30_GAUSSIAN_KERNEL_VERIFICATION=PASS"
