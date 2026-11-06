#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/scripts/env.sh"
cd "$ROOT"
python3 scripts/check_blueprint.py
python3 scripts/project_check.py
cd blueprint/verso
if [[ ! -f lake-manifest.json ]]; then
  echo "Resolving VersoBlueprint v4.35.0 dependency graph (first run)."
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
else
  lake resolve-deps
fi
lake exe vbp build
echo "Blueprint HTML: $PWD/_out/site/html-multi/index.html"
