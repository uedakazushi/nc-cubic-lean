#!/usr/bin/env python3
"""Check coverage, source integrity, task dependencies, and explicit completion.

Static scanning is a lint, not a proof. scripts/Audit.lean performs the separate
transitive axiom audit in Lean. --lean-check elaborates each claimed declaration.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|sorryAx|native_decide|unsafe|implemented_by)\b|debug\.skipKernelTC')

def code_only(text):
    """Erase nested Lean comments and string literals, retaining line numbers."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i): depth = 1; out.extend('  '); i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            j = len(text) if j < 0 else j
            out.extend(' ' * (j - i)); i = j
        elif text[i] == '"':
            out.append(' '); i += 1
            while i < len(text):
                if text[i] == '\\': out.extend('  '); i += 2
                elif text[i] == '"': out.append(' '); i += 1; break
                else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        else: out.append(text[i]); i += 1
    return ''.join(out)

def main():
    check_tmp = ROOT / '.lake' / 'nc-cubic-checks'
    if '--lean-check' in sys.argv or '--complete' in sys.argv:
        check_tmp.mkdir(parents=True, exist_ok=True)
    tasks = json.loads((ROOT / 'blueprint/tasks.json').read_text())
    nodes = {t['id']: t for t in tasks['tasks']}
    if len(nodes) != len(tasks['tasks']): raise SystemExit('Duplicate task ID')
    visiting, visited = set(), set()
    def visit(key):
        if key not in nodes: raise SystemExit(f'Unknown dependency {key}')
        if key in visiting: raise SystemExit(f'Cyclic task graph at {key}')
        if key in visited: return
        visiting.add(key)
        for dep in nodes[key]['depends_on']: visit(dep)
        visiting.remove(key); visited.add(key)
    for key in nodes: visit(key)
    modules = sorted((ROOT / 'NcCubic').rglob('*.lean'))
    imports = set(re.findall(r'^\s*(?:public\s+)?import\s+(NcCubic\.[\w.]+)',
                            (ROOT / 'NcCubic.lean').read_text(), re.M))
    for path in modules:
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        if module not in imports: raise SystemExit(f'Production module absent from NcCubic.lean: {module}')
    for path in modules + [ROOT / 'NcCubic.lean']:
        code = code_only(path.read_text())
        bad = FORBIDDEN.search(code)
        if bad:
            line = code[:bad.start()].count('\n') + 1
            raise SystemExit(f'Untrusted shortcut: {path.relative_to(ROOT)}:{line}: {bad.group()}')
        if re.search(r'^\s*(?:public\s+)?import\s+(Mathlib|Stacks|StacksFrontier|StacksCore)\s*$', code, re.M):
            raise SystemExit(f'Unbounded umbrella import: {path.relative_to(ROOT)}')
    provenance = json.loads((ROOT / 'paper/source.json').read_text())
    source = ROOT / provenance['path']
    # hashlib.file_digest is only available since Python 3.11. Read in chunks
    # so the integrity check works with the system Python on macOS as well.
    digest = hashlib.sha256()
    with source.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    if digest.hexdigest() != provenance['sha256']:
        raise SystemExit('Original paper checksum differs from source.json')
    proved = []
    for task in nodes.values():
        if task['status'] not in {'open', 'in_progress', 'proved'}:
            raise SystemExit(f"Invalid task status: {task['id']}")
        if task['status'] == 'proved':
            if not task.get('declarations'): raise SystemExit(f"No declarations for proved task {task['id']}")
            if any(not re.fullmatch(r'NcCubic\.[A-Za-z_][A-Za-z_0-9.]*', name)
                   for name in task['declarations']):
                raise SystemExit(f"Invalid theorem name in task {task['id']}")
            if any(nodes[d]['status'] != 'proved' for d in task['depends_on']):
                raise SystemExit(f"Unproved dependency of proved task {task['id']}")
            proved.extend(task['declarations'])
    if '--lean-check' in sys.argv:
        names = sorted(set(proved))
        quoted_names = ', '.join('`' + name for name in names)
        body = ('import NcCubic\nimport Lean.Elab.Command\n'
                'open Lean Elab Command\n'
                'run_cmd do\n'
                f'  let names : Array Name := #[{quoted_names}]\n'
                '  for name in names do\n'
                '    let info ← getConstInfo name\n'
                '    match info with\n'
                '    | .thmInfo _ => pure ()\n'
                '    | _ => throwError "Claimed proof is not a theorem: {name}"\n'
                f'  logInfo "Verified {len(names)} claimed theorem declarations."\n')
        if nodes['A']['status'] == 'proved':
            body += 'example : NcCubic.AffineClassificationStatement := NcCubic.theorem113_affine\n'
        if nodes['T']['status'] == 'proved':
            body += 'example : NcCubic.GeometricClassificationStatement := NcCubic.theorem113\n'
        with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=check_tmp, delete=False) as f:
            f.write(body); temp_path = Path(f.name)
        try:
            subprocess.run(['lake', 'env', 'lean', str(temp_path)], cwd=ROOT, check=True)
        finally: temp_path.unlink(missing_ok=True)
    if '--complete' in sys.argv:
        missing = [t['id'] for t in nodes.values() if t.get('required', True) and t['status'] != 'proved']
        if missing: raise SystemExit('MAIN THEOREM OPEN: ' + ', '.join(missing))
        if tasks.get('geometric_statement_review') != 'passed':
            raise SystemExit('Original geometric statement has not passed the semantic review')
        completion = ROOT / 'NcCubic/Completion.lean'
        if not completion.is_file(): raise SystemExit('Missing final theorem module NcCubic/Completion.lean')
        # The required module must contain a checked theorem, not just a Prop definition.
        if not re.search(r'\btheorem\s+theorem113\b', code_only(completion.read_text())):
            raise SystemExit('Missing theorem declaration theorem113')
        subprocess.run([sys.executable, str(ROOT / 'scripts/dependency_info.py'), 'check'], cwd=ROOT, check=True)
        subprocess.run(['lake', 'build', 'NcCubic'], cwd=ROOT, check=True)
        subprocess.run(['lake', 'env', 'lean', 'scripts/Audit.lean'], cwd=ROOT, check=True)
        body = ('import NcCubic\n'
                'example : NcCubic.AffineClassificationStatement := NcCubic.theorem113_affine\n'
                'example : NcCubic.GeometricClassificationStatement := NcCubic.theorem113\n'
                '#print axioms NcCubic.theorem113\n')
        with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=check_tmp, delete=False) as f:
            f.write(body); temp_path = Path(f.name)
        try: subprocess.run(['lake', 'env', 'lean', str(temp_path)], cwd=ROOT, check=True)
        finally: temp_path.unlink(missing_ok=True)
        print('Original theorem completion gate passed.')
    print(f'Project metadata and production coverage checked ({len(modules)} modules, {len(nodes)} tasks).')

if __name__ == '__main__':
    main()
