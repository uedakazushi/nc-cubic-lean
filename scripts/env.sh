#!/usr/bin/env bash
# Source this file; it does not change HOME or any network/security setting.
NC_CUBIC_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ -x "$NC_CUBIC_ROOT/.tools/lean/bin/lake" ]]; then
  export PATH="$NC_CUBIC_ROOT/.tools/lean/bin:$PATH"
elif [[ -d "${ELAN_HOME:-$HOME/.elan}/bin" ]]; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi
