#!/usr/bin/env bash
set -euo pipefail

# Reproducible bootstrap for the pinned Lean/mathlib project.
# Requires outbound HTTPS and standard build tools.

if ! command -v elan >/dev/null 2>&1; then
  curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
fi

# shellcheck disable=SC1090
source "${HOME}/.elan/env"

printf 'Lean: '; lean --version
printf 'Lake: '; lake --version

lake update
lake exe cache get
tools/verify_all_lean.sh
