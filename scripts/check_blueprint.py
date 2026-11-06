#!/usr/bin/env python3
"""Check stable Blueprint labels and task dependencies against the Verso chapters."""
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
tasks = {t["id"]: t for t in json.loads((root / "blueprint/tasks.json").read_text())["tasks"]}
chapterdir = root / "blueprint/verso/NcCubicBlueprint/Chapters"
nodes = {}
pattern = re.compile(r'^:::(?:definition|lemma|proposition|theorem)\s+"([^"]+)"([^\n]*)', re.M)
for chapter in sorted(chapterdir.glob("*.lean")):
    content = chapter.read_text()
    for label, opts in pattern.findall(content):
        if label in nodes:
            raise SystemExit(f"Duplicate Blueprint node {label}")
        uses = re.search(r'\(uses\s*:=\s*"([^"]+)"\)', opts)
        deps = [] if uses is None else [x.strip() for x in uses.group(1).split(",")]
        nodes[label] = {"file": chapter.name, "depends_on": deps}

missing = sorted(set(tasks) - set(nodes))
extra = sorted(set(nodes) - set(tasks))
if missing or extra:
    raise SystemExit(f"Blueprint/task labels mismatch: missing={missing}, extra={extra}")
for label, data in nodes.items():
    expected = tasks[label]["depends_on"]
    if set(data["depends_on"]) != set(expected):
        raise SystemExit(f"Dependency mismatch for {label}: Verso {data['depends_on']}, tasks.json {expected}")
print(f"Blueprint labels and declared dependencies agree for {len(nodes)} tasks.")
