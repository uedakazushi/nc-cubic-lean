#!/usr/bin/env bash
# LuaLaTeX engine used by Verso Blueprint; add Japanese text support to generated TeX.
set -euo pipefail
command -v lualatex >/dev/null || {
  echo '[nc-cubic] LuaLaTeX is required for the Blueprint PDF.' >&2
  exit 1
}
command -v kpsewhich >/dev/null || {
  echo '[nc-cubic] kpsewhich (TeX Live) is required for the Blueprint PDF.' >&2
  exit 1
}
if [[ -z "$(kpsewhich luatexja.sty)" ]]; then
  echo '[nc-cubic] The luatexja package is missing. Install LuaTeX-ja with your TeX distribution.' >&2
  exit 1
fi
python3 - <<'PY'
from pathlib import Path

tex = Path('main.tex')
if not tex.is_file():
    raise SystemExit('[nc-cubic] Expected generated Verso TeX at main.tex')
source = tex.read_text(encoding='utf-8')
header = r'\usepackage{luatexja}'
marker = r'\begin{document}'
if header not in source:
    if source.count(marker) != 1:
        raise SystemExit('[nc-cubic] Cannot locate a unique TeX document start; refusing to patch output')
    source = source.replace(marker, header + '\n' + marker, 1)
    tex.write_text(source, encoding='utf-8')
PY
exec lualatex "$@"
