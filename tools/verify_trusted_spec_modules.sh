#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG_DIR="audit/spec_kernel_logs"
SUMMARY="audit/spec_kernel_modules.txt"
mkdir -p "$LOG_DIR"
: > "$SUMMARY"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: lake executable is unavailable" >&2
  echo "trusted_spec_modules=NOT_RUN" > "$SUMMARY"
  exit 127
fi

if [[ "${ZHANGMATH_SPEC_JOBS:-1}" != "1" ]]; then
  python3 tools/verify_trusted_spec_modules_parallel.py
  exit $?
fi

MODULES=()
while IFS= read -r file; do
  MODULES+=("$file")
done < <(find ZhangLS/Spec -maxdepth 1 -type f -name '*.lean' ! -name 'All.lean' | sort)
COUNT=0
for file in "${MODULES[@]}"; do
  rel="${file#./}"
  module="${rel%.lean}"
  module="${module//\//.}"
  log="$LOG_DIR/$(basename "$file" .lean).log"
  echo "== kernel-check $rel =="
  if lake build "+${module}:olean" 2>&1 | tee "$log" &&
      lake env lean "$rel" 2>&1 | tee -a "$log"; then
    COUNT=$((COUNT + 1))
    printf 'PASS\t%s\n' "$rel" >> "$SUMMARY"
  else
    printf 'FAIL\t%s\n' "$rel" >> "$SUMMARY"
    echo "first_failed_spec_module=$rel" >> "$SUMMARY"
    echo "trusted_spec_modules_passed=$COUNT" >> "$SUMMARY"
    echo "trusted_spec_modules_total=${#MODULES[@]}" >> "$SUMMARY"
    exit 1
  fi
done

echo "trusted_spec_modules=PASS" >> "$SUMMARY"
echo "trusted_spec_modules_passed=$COUNT" >> "$SUMMARY"
echo "trusted_spec_modules_total=${#MODULES[@]}" >> "$SUMMARY"
