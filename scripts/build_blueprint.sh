#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/scripts/env.sh"
cd "$ROOT"
case "${1:-}" in
  "") python3 scripts/check_blueprint.py
      python3 scripts/project_check.py ;;
  --already-checked) ;; # full_build.sh has already checked both
  *) echo "Usage: bash scripts/build_blueprint.sh [--already-checked]" >&2; exit 2 ;;
esac
cd blueprint/verso
# This independent Lake package inherits root NcCubic and its dependencies.
# Both git checkouts and compiled artifacts live in ROOT/.lake/packages.
# Reuse the same partial-clone repair as the root and integrations/stacks.
# Do not silently update the checked-in lockfile if it is missing.
if [[ ! -f lake-manifest.json ]]; then
  echo "Missing blueprint/verso/lake-manifest.json; restore the pinned lockfile." >&2
  exit 1
fi
bash "$ROOT/scripts/resolve_deps.sh" "$PWD"
# Verso Blueprint v4.35.0 has a native LuaLaTeX PDF renderer.
# Fail visibly if the required TeX environment is unavailable.
command -v lualatex >/dev/null || { echo "Missing lualatex: install a TeX Live/MacTeX distribution." >&2; exit 1; }
command -v kpsewhich >/dev/null || { echo "Missing kpsewhich: install a TeX Live/MacTeX distribution." >&2; exit 1; }
[[ -n "$(kpsewhich luatexja.sty)" ]] || {
  echo "Missing luatexja.sty: install LuaTeX-ja for Japanese Blueprint text." >&2
  exit 1
}
# The renderer does not remove obsolete chapter paths after a title/file change.
# Clear generated HTML so old chapters cannot remain in the current site.
rm -rf -- "$PWD/_out/site/html-multi"
# --pdf also generates the HTML site and a TeX tree. The engine wrapper
# enables Japanese text without adding unsupported preamble commands to KaTeX.
lake exe vbp build --pdf --pdf-engine "$ROOT/scripts/blueprint_lualatex.sh"
site="$PWD/_out/site/html-multi/index.html"
pdf="$PWD/_out/site/pdf/main.pdf"
if [[ ! -s "$site" ]]; then
  echo "Verso HTML output is missing or empty: $site" >&2
  exit 1
fi
if [[ ! -s "$pdf" ]]; then
  echo "Verso PDF output is missing or empty: $pdf" >&2
  exit 1
fi
echo "Blueprint HTML: $site"
echo "Blueprint PDF:  $pdf"
