#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/scripts/env.sh"
cd "$ROOT"
python3 scripts/check_blueprint.py
python3 scripts/project_check.py
cd blueprint/verso
if [[ ! -f lake-manifest.json ]]; then
  echo "Resolving VersoBlueprint v4.35.0 dependencies on first use."
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
else
  lake resolve-deps
fi
# The renderer does not remove obsolete chapter paths after a title/file change.
# Clear only generated HTML so old chapters cannot remain in the current site.
rm -rf -- "$PWD/_out/site/html-multi"
lake exe vbp build
site="$PWD/_out/site/html-multi/index.html"
if [[ ! -s "$site" ]]; then
  echo "Verso output is missing or empty: $site" >&2
  exit 1
fi
echo "Blueprint HTML: $site"
