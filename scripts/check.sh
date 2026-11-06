#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd "$NC_CUBIC_ROOT"
mode="${1:-}"
if [[ -n "$mode" && "$mode" != '--complete' ]]; then
  echo 'Usage: bash scripts/check.sh [--complete]' >&2
  exit 2
fi
python3 scripts/project_check.py
python3 scripts/dependency_info.py check
lake build NcCubic
lake env lean scripts/Audit.lean
python3 scripts/project_check.py --lean-check
if [[ "$mode" == '--complete' ]]; then
  python3 scripts/project_check.py --complete
else
  echo 'Current library checked. The original Theorem 1.1(3) remains OPEN unless the complete gate passes.'
fi
