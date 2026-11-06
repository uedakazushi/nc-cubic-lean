#!/usr/bin/env bash
# Explicit, optional wrapper for the procfs mismatch described in README.md.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/../env.sh"
if [[ "$(uname -s)" != Linux || $# -eq 0 ]]; then
  echo 'Usage on the affected Linux executor: bash scripts/compat/run.sh COMMAND [ARGS...]' >&2
  exit 2
fi
mkdir -p "$NC_CUBIC_ROOT/.tools/compat"
compat_so="$NC_CUBIC_ROOT/.tools/compat/lean_self_path.so"
"${CC:-cc}" -shared -fPIC -O2 \
  "$NC_CUBIC_ROOT/scripts/compat/lean_self_path.c" -ldl -o "$compat_so"
export LD_PRELOAD="$compat_so${LD_PRELOAD:+:$LD_PRELOAD}"
exec "$@"
