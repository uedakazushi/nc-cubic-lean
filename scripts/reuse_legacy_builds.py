#!/usr/bin/env python3
"""Reuse old dependency builds in the shared root Lake package directory.

Default is a safe report. --apply merges only missing artifacts after verifying
that both Git checkouts are at the exact same pinned revision. No automatic
deletion and no overwriting of an existing artifact. Run only with Lake idle.
"""
import argparse
import errno
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SHARED = ROOT / ".lake" / "packages"
WORKSPACES = [ROOT / "integrations" / "stacks", ROOT / "blueprint" / "verso"]


def git(path, *args):
    return subprocess.check_output(
        ["git", "-C", str(path), *args], text=True, stderr=subprocess.DEVNULL
    ).strip()


def valid_checkout(path, package):
    if not path.is_dir() or path.is_symlink():
        return False
    try:
        return (
            git(path, "rev-parse", "HEAD") == package["rev"]
            and git(path, "remote", "get-url", "origin") == package["url"]
        )
    except (OSError, subprocess.CalledProcessError, KeyError):
        return False


def migrate(workspace, apply):
    manifest = json.loads((workspace / "lake-manifest.json").read_text())
    expected = (workspace / manifest["packagesDir"]).resolve()
    if expected != SHARED.resolve():
        raise SystemExit(f"Shared packagesDir mismatch: {workspace}")
    old = workspace / ".lake" / "packages"
    if not old.exists():
        print(f"{workspace.relative_to(ROOT)}: no legacy checkout directory")
        return
    for package in manifest["packages"]:
        if package.get("type") != "git":
            continue
        name = package["name"]
        src = old / name
        dst = SHARED / name
        if not src.exists():
            continue
        if not valid_checkout(src, package):
            print(f"SKIP {src}: not a verified pinned Git checkout")
            continue
        if not dst.exists():
            print(f"{'MOVE' if apply else 'WOULD MOVE'} {src} -> {dst}")
            if apply:
                SHARED.mkdir(parents=True, exist_ok=True)
                shutil.move(str(src), str(dst))
            continue
        if not valid_checkout(dst, package):
            print(f"SKIP {dst}: existing checkout does not match the lockfile")
            continue
        src_build = src / ".lake" / "build"
        if not src_build.is_dir():
            continue
        count = 0
        for parent, dirs, files in os.walk(src_build, followlinks=False):
            dirs[:] = [d for d in dirs if not (Path(parent) / d).is_symlink()]
            for name in files:
                source = Path(parent) / name
                if not source.is_file() or source.is_symlink():
                    continue
                target = dst / ".lake" / "build" / source.relative_to(src_build)
                if target.exists() or target.is_symlink():
                    continue
                count += 1
                if apply:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    try:
                        # Same-volume hardlinks reuse storage without byte copies.
                        os.link(source, target)
                    except OSError as exc:
                        if exc.errno not in {errno.EXDEV, errno.EPERM, errno.ENOTSUP}:
                            raise
                        # Only copy missing files. Never replace an existing file.
                        with source.open("rb") as inp, target.open("xb") as out:
                            shutil.copyfileobj(inp, out)
                        shutil.copystat(source, target)
        if count:
            label = "LINKED/COPIED" if apply else "CAN REUSE"
            print(f"{label} {count} missing artifacts: {src_build} -> {dst / '.lake/build'}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true", help="move missing checkouts and reuse missing build artifacts")
    args = parser.parse_args()
    for ws in WORKSPACES:
        migrate(ws, args.apply)
    if not args.apply:
        print("Dry run only. To migrate, use --apply after all builds have stopped.")
    else:
        print("Migration complete. Old directories were not deleted; run a full build before manual cleanup.")


if __name__ == "__main__":
    main()
