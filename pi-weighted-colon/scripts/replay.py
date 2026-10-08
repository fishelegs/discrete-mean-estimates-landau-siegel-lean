#!/usr/bin/env python3
"""Compile and audit the weighted-colon checkpoint using an existing pinned cache.

No Lake command, installation, network request, hook or dependency build is run.
All compilers run serially, with one worker and a 4096 MiB memory limit.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
CORE = ['WeightedColon', 'DataIdealPresentation', 'EndpointColon']
EXTRA_CORE = ['RemainderVanish', 'QuadraticRemainder', 'EndpointRemainderBridge', 'RightRemainderBridge']
REGRESSIONS = ['WeightedColonRegression', 'RemainderRegression', 'BridgeRegression']
POSITIVE = CORE + EXTRA_CORE + REGRESSIONS + ['WeightedColonAudit', 'RemainderAudit', 'BridgeAudit']
NEGATIVE = {
    'ExpectedFailureWrongQuotientSquare': ('Tactic `assumption` failed', 'reduction'),
    'ExpectedFailureZeroScale': ('1 ≤ 0', 'proved that the proposition'),
    'ExpectedFailureWrongWeight': ('5 = 1 ∨ 5 = 3', 'proved that the proposition'),
    'ExpectedFailureMissingRemainderCoupling': ('⊢ (X + 1) ^ 3 ∣ X', 'unsolved goals'),
    'ExpectedFailureWeakRemainderDegree': ('4 ≤ 1', 'proved that the proposition'),
}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--existing-mathlib-project', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    lean = args.lean.resolve()
    project = args.existing_mathlib_project.resolve()
    out = args.out.resolve()
    for protected in [ROOT, project]:
        if out == protected or protected in out.parents or out in protected.parents:
            parser.error('--out must be outside, and must not contain, source/dependency trees')

    pins = json.loads((ROOT / 'dependency-pins.json').read_text())
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    actual = {p['name']: p['rev'] for p in manifest['packages']}
    for package in pins['packages']:
        name, rev = package['name'], package['rev']
        if actual.get(name) != rev:
            parser.error(f'Wrong manifest revision for {name}')
        cached_project = project / '.lake/packages' / name
        head = subprocess.check_output(
            ['git', '-C', str(cached_project), 'rev-parse', 'HEAD'], text=True).strip()
        if head != rev:
            parser.error(f'Wrong actual source checkout for {name}: {head}')
        if subprocess.check_output(
                ['git', '-C', str(cached_project), 'status', '--porcelain'], text=True):
            parser.error(f'Dirty dependency checkout: {name}')
    if (project / 'lean-toolchain').read_text().strip() != pins['toolchain']:
        parser.error('Wrong project toolchain pin')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if not re.search(r'version 4\.30\.0(?:,|\))', version):
        parser.error(f'Wrong Lean executable: {version}')

    sources = json.loads((ROOT / 'verification/source-hashes.json').read_text())
    for relative, digest in sources.items():
        if sha(ROOT / relative) != digest:
            parser.error(f'Checkpoint hash mismatch: {relative}')

    attestation = json.loads((ROOT / 'verification/dependency-attestation.json').read_text())
    imports = {}
    for module, expected in attestation['direct_imports'].items():
        relative = Path(*module.split('.'))
        if module.startswith('Mathlib.'):
            source = project / '.lake/packages/mathlib' / relative.with_suffix('.lean')
            cached = project / '.lake/packages/mathlib/.lake/build/lib/lean' / relative.with_suffix('.olean')
        else:
            source = lean.parent.parent / 'src/lean' / relative.with_suffix('.lean')
            cached = lean.parent.parent / 'lib/lean' / relative.with_suffix('.olean')
        if not source.is_file() or sha(source) != expected['source_sha256']:
            parser.error(f'Dependency source mismatch: {module}')
        if not cached.is_file():
            parser.error(f'Missing cached dependency: {module}; no dependencies are built')
        imports[module] = {'source_sha256': sha(source), 'olean_sha256': sha(cached)}

    build, logs = out / 'build', out / 'logs'
    build.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    libraries = sorted((project / '.lake/packages').glob('*/.lake/build/lib/lean'))
    env = os.environ.copy()
    env.update(LEAN_PATH=':'.join(map(str, [build] + libraries)), LEAN_NUM_THREADS='1')
    checks = []
    for name in POSITIVE + list(NEGATIVE):
        source = ROOT / 'src' / (name + '.lean')
        output = build / (name + '.olean')
        if output.exists():
            output.unlink()
        command = [str(lean), '-j1', '-M4096', '-DautoImplicit=false',
                   '-DwarningAsError=true', '-o', str(output), source.name]
        started = time.monotonic()
        run = subprocess.run(command, cwd=ROOT / 'src', env=env, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs / (name + '.log')
        log.write_text(run.stdout)
        expected_failure = name in NEGATIVE
        passed = (run.returncode == 0 and output.is_file()) if not expected_failure else (
            run.returncode == 1 and run.stdout.count('error:') == 1 and
            all(fragment in run.stdout for fragment in NEGATIVE[name]) and not output.exists())
        check = {'module': name, 'command': command, 'cwd': str(ROOT / 'src'),
                 'source_sha256': sha(source), 'exit_code': run.returncode,
                 'expected_failure': expected_failure, 'passed': passed,
                 'log_sha256': sha(log), 'elapsed_seconds': round(time.monotonic() - started, 3)}
        if output.exists():
            check['olean_sha256'] = sha(output)
        checks.append(check)
        print(f'{name}: {"PASS" if passed else "FAIL"}', flush=True)
        if not passed:
            print(run.stdout, file=sys.stderr)
            return 1

    declarations = {}
    for name in CORE + EXTRA_CORE + REGRESSIONS:
        source = (ROOT / 'src' / (name + '.lean')).read_text()
        if re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b', source):
            raise RuntimeError(f'Prohibited proof construct in {name}')
        namespace = 'PiWeightedColon.Regression.' if name.endswith('Regression') else 'PiWeightedColon.'
        for kind, declaration in re.findall(r'^(theorem|def|abbrev|instance) (\w+)\b', source, re.M):
            declarations[namespace + declaration] = kind
    audit = '\n'.join((logs / (name + '.log')).read_text()
                      for name in ['WeightedColonAudit', 'RemainderAudit', 'BridgeAudit'])
    reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit, re.S))
    reports.update({name: '' for name in re.findall(
        r"'([^']+)' does not depend on any axioms", audit)})
    if set(reports) != set(declarations):
        raise RuntimeError('Axiom audit does not cover exactly all new declarations')
    axioms = {}
    for name, body in reports.items():
        used = {re.sub(r'\.\{[^}]*\}', '', value.strip())
                for value in body.split(',') if value.strip()}
        if not used <= ALLOWED_AXIOMS:
            raise RuntimeError(f'Unexpected axioms for {name}: {used}')
        axioms[name] = sorted(used)
    receipt = {'status': 'passed', 'lean_version': version,
               'lean_executable_sha256': sha(lean), 'dependency_pins': pins,
               'direct_imports': imports, 'checks': checks,
               'declaration_kinds': declarations, 'axiom_audit': axioms,
               'scope': 'Weighted colon lemma for the actual F2 endpoint ideals, and '
                        'remainder vanishing with all local divisibility conditions derived '
                        'from actual endpoint ideal membership via a quadratic quotient model. '
                        'Remainder decomposition and degree bounds are explicit inputs; '
                        'staircase division, V_N induction, matrix and determinant/analytic '
                        'bridges are not proved.'}
    (out / 'replay-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'All {len(declarations)} declaration audits and {len(checks)} compilation checks passed.', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
