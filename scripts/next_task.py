#!/usr/bin/env python3
"""Print the ready proof tasks in the current research priority order."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
data = json.loads((root / 'blueprint/tasks.json').read_text())
tasks = {task['id']: task for task in data['tasks']}
ready = sorted(
    (task for task in tasks.values()
     if task['status'] != 'proved'
     and all(tasks[dep]['status'] == 'proved' for dep in task['depends_on'])),
    key=lambda task: (task.get('priority', 100), task['id']))
if ready:
    for i, task in enumerate(ready, 1):
        print(f"{i}. {task['id']}: {task['title']}")
        print(f"   Acceptance: {task['acceptance']}")
else:
    print('No ready task. Inspect blockers, or run scripts/check.sh --complete if all nodes are proved.')
