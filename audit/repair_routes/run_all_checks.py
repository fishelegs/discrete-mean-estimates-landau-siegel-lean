#!/usr/bin/env python3
"""Run the portable audit checks without network access, Lean, or a repository.

All generated files stay inside this package. Run normally (not Python -O),
since assertion checks are part of the certificates.
"""
from pathlib import Path
import json
import os
import platform
import subprocess
import sys

import mpmath
import sympy

if not __debug__:
    raise SystemExit('Assertions are disabled; rerun without Python -O.')

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / 'results'
RESULTS.mkdir(exist_ok=True)
CHECKS = [
    ('admissible-shift-repair/check_extension.py', None),
    ('admissible-shift-repair/check_general_extension.py', None),
    ('admissible-shift-repair/check_spectral_bounds.py', None),
    ('admissible-shift-independent-review/derive_cross_flux.py', None),
    ('admissible-shift-independent-review/check_direct_extension.py', None),
    ('admissible-shift-independent-review/check_spectral_and_target.py', None),
    ('phase-mechanism-repair/check_algebra.py', 'phase-mechanism-repair/algebra-checks.json'),
    ('phase-mechanism-repair/check_gauss_identities.py', 'phase-mechanism-repair/gauss-checks.json'),
    ('phase-arithmetic-independent-review/exact_checks.py', None),
]
env = os.environ.copy()
env['PYTHONDONTWRITEBYTECODE'] = '1'
env['PYTHONHASHSEED'] = '0'
env.pop('PYTHONOPTIMIZE', None)
summary = {
    'python': platform.python_version(),
    'sympy': sympy.__version__,
    'mpmath': mpmath.__version__,
    'scope': 'Symbolic certificates and finite regressions; no Lean or actual arithmetic mean proof.',
    'checks': [],
}
for relative, json_output in CHECKS:
    print('Running ' + relative, flush=True)
    proc = subprocess.run([sys.executable, '-B', str(ROOT / relative)], cwd=ROOT,
                          env=env, capture_output=True, text=True)
    # Remove the local package prefix even in an unexpected diagnostic.
    stdout = proc.stdout.replace(str(ROOT), '.')
    stderr = proc.stderr.replace(str(ROOT), '.')
    logname = relative.replace('/', '__').replace('.py', '.txt')
    (RESULTS / logname).write_text(stdout + stderr, encoding='utf-8')
    row = {'script': relative, 'exit_code': proc.returncode,
           'status': 'PASS' if proc.returncode == 0 else 'FAIL',
           'log': 'results/' + logname}
    summary['checks'].append(row)
    if proc.returncode != 0:
        summary['all_passed'] = False
        (RESULTS / 'check-summary.json').write_text(json.dumps(summary, indent=2)+'\n')
        raise SystemExit('Check failed; inspect ' + row['log'])
    if json_output:
        parsed = json.loads(stdout)
        (ROOT / json_output).write_text(json.dumps(parsed, indent=2)+'\n', encoding='utf-8')
    print('PASS ' + relative, flush=True)
summary['all_passed'] = True
(RESULTS / 'check-summary.json').write_text(json.dumps(summary, indent=2)+'\n', encoding='utf-8')
print('PASS: all nine checks', flush=True)
