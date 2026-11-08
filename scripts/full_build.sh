#!/usr/bin/env bash
# The root lakefile.lean calls this script only after its NcCubic target builds.
# Subprocesses use explicit targets: they never recursively call root lake build.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/scripts/env.sh"
cd "$ROOT"

echo "[nc-cubic] Checking metadata and source integrity"
python3 scripts/project_check.py
python3 scripts/dependency_info.py check

echo "[nc-cubic] Checking proof kernel axioms"
lake env lean scripts/Audit.lean
python3 scripts/project_check.py --lean-check

echo "[nc-cubic] Checking Blueprint graph consistency"
python3 scripts/check_blueprint.py

echo "[nc-cubic] Building and auditing selected Axiom Stacks adapters"
cd integrations/stacks
if [[ ! -f lake-manifest.json ]]; then
  echo "Stacks lockfile missing; explicit dependency resolution required." >&2
  exit 1
fi
bash "$ROOT/scripts/resolve_deps.sh" "$PWD"
# NcCubic already built against the same shared mathlib/Stacks artifacts.
# Avoid repeatedly resolving and downloading the selected mathlib cache.
lake build NcCubicStacks NcCubicStacksAudit
cd "$ROOT"

echo "[nc-cubic] Rendering Verso Blueprint HTML and LuaLaTeX PDF"
bash scripts/build_blueprint.sh --already-checked

echo "[nc-cubic] Full project build, audits, and Blueprint generation complete"
echo "[nc-cubic] Note: this is NOT proof of Theorem 1.1(3)."
