#!/usr/bin/env bash
# Resolve a locked Lake workspace with shared root package cache;
# repair an incomplete Stacks partial clone once.
# Never change global Git settings or silently discard a dependency checkout.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
PACKAGE_DIR="${1:-$ROOT}"
cd "$PACKAGE_DIR"

if [[ ! -f lake-manifest.json ]]; then
  echo "Missing lake-manifest.json in $PWD; cannot safely repair pinned dependencies." >&2
  exit 1
fi

# The ordinary fast path is unchanged; no extra Git transfer is needed.
resolve_log="$(mktemp)"
trap 'rm -f -- "$resolve_log"' EXIT
if lake resolve-deps 2>&1 | tee "$resolve_log"; then
  exit 0
fi
if ! grep -Eiq 'Stacks|promisor remote' "$resolve_log"; then
  echo '[nc-cubic] Lake failed for a reason not identified as Stacks; no repair attempted.' >&2
  exit 1
fi

echo '[nc-cubic] Lake dependency resolution failed; checking the pinned Stacks checkout.' >&2

# Read the lockfile and verify it against the project's independent pin before
# making any changes. In particular, never fall back to an unpinned branch.
pin_line="$(python3 - "$ROOT/dependencies.json" "$PWD/lake-manifest.json" <<'PY'
import json
from pathlib import Path
import re
import sys

pins = json.loads(Path(sys.argv[1]).read_text())['stacks']
manifest = json.loads(Path(sys.argv[2]).read_text())
packages = [p for p in manifest['packages'] if p['name'] == 'Stacks']
root = Path(sys.argv[1]).resolve().parent
package_dir = Path(sys.argv[2]).resolve().parent
packages_dir = manifest.get('packagesDir')
if not isinstance(packages_dir, str) or (
    package_dir / packages_dir
).resolve() != (root / '.lake/packages').resolve():
    raise SystemExit('Unexpected packagesDir: must point to the root shared .lake/packages')
if len(packages) != 1:
    raise SystemExit('Expected exactly one pinned Stacks package')
package = packages[0]
if (package.get('type') != 'git' or package['url'] != pins['url']
        or package['rev'] != pins['rev']
        or not re.fullmatch(r'[0-9a-f]{40}', pins['rev'])):
    raise SystemExit('Stacks lockfile does not match dependencies.json; refusing repair')
print(pins['url'], pins['rev'])
PY
)"
read -r stacks_url stacks_rev <<< "$pin_line"
stacks_dir="$ROOT/.lake/packages/Stacks"

if [[ ! -e "$stacks_dir" ]]; then
  # Lake may remove a failed clone. Fetch just the pinned commit, not main.
  mkdir -p "$stacks_dir"
  git init -q "$stacks_dir"
  git -C "$stacks_dir" remote add origin "$stacks_url"
elif ! git -C "$stacks_dir" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "[nc-cubic] $stacks_dir exists but is not a Git checkout; leaving it untouched." >&2
  exit 1
fi

remote_url="$(git -C "$stacks_dir" remote get-url origin)"
if [[ "$remote_url" != "$stacks_url" ]]; then
  echo "[nc-cubic] Unexpected Stacks origin: $remote_url; refusing repair." >&2
  exit 1
fi

if [[ "$(git -C "$stacks_dir" config --get remote.origin.promisor || true)" == true ]]; then
  echo '[nc-cubic] Refetching Stacks without the partial-clone filter (HTTP/1.1).' >&2
  git -C "$stacks_dir" -c http.version=HTTP/1.1 \
    fetch --refetch --no-filter origin "$stacks_rev"
else
  echo '[nc-cubic] Fetching the pinned Stacks commit without partial cloning (HTTP/1.1).' >&2
  git -C "$stacks_dir" -c http.version=HTTP/1.1 \
    fetch --depth=1 origin "$stacks_rev"
fi

git -C "$stacks_dir" checkout --detach "$stacks_rev"
echo '[nc-cubic] Retrying Lake dependency resolution after Stacks repair.' >&2
lake resolve-deps
