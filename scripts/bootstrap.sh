#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd "$NC_CUBIC_ROOT"

for cmd in curl git python3 tar; do
  command -v "$cmd" >/dev/null || { echo "Missing prerequisite: $cmd" >&2; exit 1; }
done
python3 -c 'import sys; sys.version_info >= (3, 11) or sys.exit("Python 3.11 or later is required.")'
version="$(sed -n 's|^leanprover/lean4:v||p' lean-toolchain)"
if [[ -z "$version" ]]; then
  echo 'Unsupported lean-toolchain format; inspect it before changing anything.' >&2
  exit 1
fi

if ! command -v lean >/dev/null || ! lean --version 2>/dev/null | grep -Fq "version $version,"; then
  command -v zstd >/dev/null || { echo 'Install zstd, then rerun this script.' >&2; exit 1; }
  case "$(uname -s):$(uname -m)" in
    Linux:x86_64) platform=linux ;;
    Linux:aarch64|Linux:arm64) platform=linux_aarch64 ;;
    Darwin:x86_64) platform=darwin ;;
    Darwin:arm64) platform=darwin_aarch64 ;;
    *) echo 'Install the pinned Lean toolchain with elan on this platform.' >&2; exit 1 ;;
  esac
  mkdir -p .tools/downloads
  archive=".tools/downloads/lean-$version-$platform.tar.zst"
  digest="$(python3 scripts/dependency_info.py lean-digest "$platform")"
  echo "Downloading official Lean $version ($platform)."
  curl --fail --location --retry 2 --connect-timeout 20 --max-time 1200 \
    --output "$archive" "https://releases.lean-lang.org/lean4/v$version/lean-$version-$platform.tar.zst"
  python3 - "$archive" "$digest" <<'PY'
import hashlib, pathlib, sys
p = pathlib.Path(sys.argv[1])
h = hashlib.file_digest(p.open('rb'), 'sha256').hexdigest()
if h != sys.argv[2]:
    raise SystemExit(f'Official Lean archive checksum mismatch: {p.name}')
print('Official Lean archive SHA256 verified.')
PY
  mkdir -p .tools/lean
  tar --no-same-owner --zstd -xf "$archive" --strip-components=1 -C .tools/lean
  export PATH="$NC_CUBIC_ROOT/.tools/lean/bin:$PATH"
fi

lean --version
lake --version
if [[ ! -f lake-manifest.json ]]; then
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
else
  bash scripts/resolve_deps.sh
fi
python3 scripts/dependency_info.py check

# Fetch only the imports needed by this project's files. Avoid Mathlib's entire cache.
cache_targets=()
while IFS= read -r target; do
  cache_targets+=("$target")
done < <(python3 scripts/dependency_info.py imports)
if [[ ${#cache_targets[@]} -eq 0 ]]; then
  echo 'No Mathlib import targets found; inspect the source tree.' >&2
  exit 1
fi
lake exe cache get "${cache_targets[@]}"
bash scripts/check.sh
