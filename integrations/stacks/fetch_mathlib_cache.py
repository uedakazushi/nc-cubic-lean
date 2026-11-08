#!/usr/bin/env python3
"""Fetch Mathlib artifacts for the Stacks modules imported by this package.

Run after `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`. Only the Mathlib roots
reached through the selected project's Stacks imports are sent to the cache CLI;
that CLI resolves their own Mathlib dependencies. This does not build Stacks.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess


IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$")
MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z0-9_']+)*$")


def imports(path: Path) -> list[str]:
    result: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT.match(line)
        if not match:
            continue
        for token in match[1].split("--", 1)[0].split():
            if token == "all":
                continue
            if not MODULE.fullmatch(token):
                raise SystemExit(f"Unrecognized import syntax in {path}: {line}")
            result.append(token)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cm", action="store_true", help="include the optional CM target")
    parser.add_argument("--list-only", action="store_true", help="print roots without downloading")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    # All three Lake workspaces share the root package store and build artifacts.
    stacks = here.parents[1] / ".lake" / "packages" / "Stacks"
    if not (stacks / "lakefile.toml").is_file():
        raise SystemExit("Stacks checkout missing; run MATHLIB_NO_CACHE_ON_UPDATE=1 lake update first.")

    pending = imports(here / "NcCubicStacks.lean")
    if args.cm:
        pending.extend(imports(here / "NcCubicStacksCM.lean"))
    seen: set[str] = set()
    mathlib: set[str] = set()
    while pending:
        name = pending.pop()
        if name.startswith("Mathlib."):
            mathlib.add(name)
        elif name.startswith(("StacksCore.", "StacksFrontier.")):
            if name in seen:
                continue
            seen.add(name)
            source = stacks.joinpath(*name.split(".")).with_suffix(".lean")
            if not source.is_file():
                raise SystemExit(f"Imported Stacks source missing: {name}")
            pending.extend(imports(source))
        elif name.split(".", 1)[0] not in {"Init", "Lean", "Std", "Batteries", "Qq", "Aesop"}:
            raise SystemExit(f"Review new external import before fetching cache: {name}")

    roots = sorted(mathlib)
    print(f"Selected Stacks modules: {len(seen)}; Mathlib import roots: {len(roots)}", flush=True)
    if args.list_only:
        print("\n".join(roots))
        return 0
    if not roots:
        raise SystemExit("No Mathlib roots found; review the import scan.")
    return subprocess.run(["lake", "exe", "cache", "get", *roots], cwd=here).returncode


if __name__ == "__main__":
    raise SystemExit(main())
