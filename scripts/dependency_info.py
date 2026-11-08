#!/usr/bin/env python3
"""Read pinned dependencies and cache targets; never silently upgrade pins."""
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PINS = json.loads((ROOT / 'dependencies.json').read_text())

def check():
    toolchain = (ROOT / 'lean-toolchain').read_text().strip()
    if toolchain != PINS['lean']['toolchain']:
        raise SystemExit('lean-toolchain and dependencies.json disagree')
    manifest_path = ROOT / 'lake-manifest.json'
    if not manifest_path.exists():
        raise SystemExit('Missing lake-manifest.json; run bootstrap first')
    manifest = json.loads(manifest_path.read_text())
    packages = {p['name']: p for p in manifest['packages']}
    if packages.get('mathlib', {}).get('rev') != PINS['mathlib']['rev']:
        raise SystemExit('mathlib lockfile revision mismatch')
    for package in manifest['packages']:
        if package.get('type') == 'git' and not re.fullmatch(r'[0-9a-f]{40}', package['rev']):
            raise SystemExit(f"Unpinned dependency: {package['name']}")
        path = ROOT / '.lake/packages' / package['name']
        if not path.is_dir():
            raise SystemExit(f"Missing dependency checkout: {package['name']}; run lake update")
        if package.get('type') == 'git':
            head = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
            if head != package['rev']:
                raise SystemExit(f"Dependency checkout differs from lockfile: {package['name']}")
    upstream_toolchain = (ROOT / '.lake/packages/mathlib/lean-toolchain').read_text().strip()
    if upstream_toolchain != toolchain:
        raise SystemExit('mathlib requires a different Lean toolchain')
    shared_check()
    print('Pinned toolchain, lockfile, and dependency checkouts agree.')

def shared_check():
    """Verify that every workspace uses one pinned Git checkout/build store."""
    root_manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    root_deps = {p['name']: p for p in root_manifest['packages']}
    if root_manifest.get('packagesDir') != '.lake/packages':
        raise SystemExit('Root package store must remain .lake/packages')
    for rel in ('integrations/stacks', 'blueprint/verso'):
        workspace = ROOT / rel
        manifest = json.loads((workspace / 'lake-manifest.json').read_text())
        if manifest.get('packagesDir') != '../../.lake/packages':
            raise SystemExit(f'{rel}: Lake manifest does not use the shared package store')
        config = (workspace / 'lakefile.toml').read_text()
        if not re.search(
            r'^packagesDir\s*=\s*"\.\./\.\./\.lake/packages"\s*
    targets = set()
    for path in sorted((ROOT / 'NcCubic').rglob('*.lean')):
        for module in re.findall(r'^\s*(?:public\s+)?import\s+(Mathlib\.[\w.]+)', path.read_text(), re.M):
            targets.add(module)
    print('\n'.join(sorted(targets)))

if __name__ == '__main__':
    if len(sys.argv) < 2:
        raise SystemExit('Usage: dependency_info.py check|shared-check|imports|lean-digest PLATFORM')
    if sys.argv[1] == 'check':
        check()
    elif sys.argv[1] == 'shared-check':
        shared_check()
    elif sys.argv[1] == 'imports':
        imports()
    elif sys.argv[1] == 'lean-digest' and len(sys.argv) == 3:
        print(PINS['lean']['sha256'][sys.argv[2]])
    else:
        raise SystemExit('Unknown dependency_info command')
, config, re.M
        ):
            raise SystemExit(f'{rel}: Lake config does not use the shared package store')
        for pkg in manifest['packages']:
            other = root_deps.get(pkg['name'])
            if other and pkg.get('type') == 'git':
                if (pkg.get('url'), pkg.get('rev')) != (other.get('url'), other.get('rev')):
                    raise SystemExit(f'{rel}: conflicting pinned dependency {pkg["name"]}')
    print('All three workspaces share identical pinned dependencies and root .lake/packages.')


def imports():
    targets = set()
    for path in sorted((ROOT / 'NcCubic').rglob('*.lean')):
        for module in re.findall(r'^\s*(?:public\s+)?import\s+(Mathlib\.[\w.]+)', path.read_text(), re.M):
            targets.add(module)
    print('\n'.join(sorted(targets)))

if __name__ == '__main__':
    if len(sys.argv) < 2:
        raise SystemExit('Usage: dependency_info.py check|imports|lean-digest PLATFORM')
    if sys.argv[1] == 'check':
        check()
    elif sys.argv[1] == 'imports':
        imports()
    elif sys.argv[1] == 'lean-digest' and len(sys.argv) == 3:
        print(PINS['lean']['sha256'][sys.argv[2]])
    else:
        raise SystemExit('Unknown dependency_info command')
