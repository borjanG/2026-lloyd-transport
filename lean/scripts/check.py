#!/usr/bin/env python3
"""Build all proofs and audit the axioms of every project theorem."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LAKE = os.environ.get('LLOYD_LAKE', 'lake')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def run(*args):
    result = subprocess.run([LAKE, *args], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end='')
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


run('build')
files = sorted((ROOT / 'Lloyd').rglob('*.lean'))
theorems = []
for path in files:
    # Every declaration currently lives directly in namespace Lloyd.
    names = re.findall(r'^theorem\s+([A-Za-z0-9_]+)\b', path.read_text(), re.M)
    theorems.extend('Lloyd.' + name for name in names)
if not theorems or len(theorems) != len(set(theorems)):
    raise SystemExit('Empty or duplicate theorem list; audit needs review.')

with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='Audit-',
                                 dir=ROOT, delete=False) as handle:
    audit_path = Path(handle.name)
    handle.write('import Lloyd\n\n')
    handle.write('\n'.join('#print axioms ' + name for name in theorems) + '\n')
try:
    output = run('env', 'lean', str(audit_path))
finally:
    audit_path.unlink(missing_ok=True)

records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
# Lean can also report a theorem with no axioms.
empty = re.findall(r"'([^']+)' does not depend on any axioms", output)
axioms = {name: [x.strip() for x in body.split(',') if x.strip()]
          for name, body in records}
axioms.update({name: [] for name in empty})
if set(axioms) != set(theorems):
    raise SystemExit('Could not audit every theorem; inspect Lean output.')
for name, dependencies in axioms.items():
    unexpected = set(dependencies) - ALLOWED_AXIOMS
    if unexpected:
        raise SystemExit(f'{name} has unapproved axioms: {sorted(unexpected)}')

tracked = files + [ROOT / 'Lloyd.lean', ROOT / 'lakefile.toml',
                   ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain']
report = {
    'build': 'passed',
    'axiom_audit': 'passed',
    'theorem_count': len(theorems),
    'allowed_axioms': sorted(ALLOWED_AXIOMS),
    'theorem_axioms': axioms,
    'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in tracked},
}
report_path = ROOT / 'verification.json'
report_path.write_text(json.dumps(report, indent=2) + '\n')
print(f'PASS: {len(theorems)} theorems checked; only standard Lean axioms used.')
print('This audits the proved components. It does not certify completion of Theorem 4.1.')
