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
EXTRA_CORE = ['RemainderVanish', 'QuadraticRemainder', 'EndpointRemainderBridge', 'RightRemainderBridge', 'StaircaseDivision', 'StaircaseNonvanishing', 'MatrixIndices', 'MatrixEntries', 'BinaryMatrixNonvanishing', 'NewtonIntegral', 'IntegerNewtonMatrix', 'FrequencyProfile', 'IntegerOriginNonvanishing']
REGRESSIONS = ['WeightedColonRegression', 'RemainderRegression', 'BridgeRegression', 'AllScaleRegression', 'MatrixRegression', 'NewtonRegression', 'OriginRegression']
POSITIVE = CORE + EXTRA_CORE + REGRESSIONS + ['WeightedColonAudit', 'RemainderAudit', 'BridgeAudit', 'AllScaleAudit', 'MatrixAudit', 'NewtonAudit', 'OriginAudit']
NEGATIVE = {
    'ExpectedFailureOriginFactor': ('proved that the proposition', 'integerEvaluationFactor 1 originTestCol originTestCol = 1'),
    'ExpectedFailureOriginDropFactor': ('proved that the proposition', '27 = 13'),
    'ExpectedFailurePairZero': ('proved that the proposition', 'frequencyLength 0 1 = 1'),
    'ExpectedFailureNewtonValue': ('proved that the proposition', '13 = 12'),
    'ExpectedFailureBinaryZeroPower': ('proved that the proposition', 'binaryEntry 0 1 false 1 0 = 0'),
    'ExpectedFailureBinaryParity': ('proved that the proposition', 'binaryEntry 4 0 true 0 2 = 1'),
    'ExpectedFailureWithoutStaircase': ('Tactic `assumption` failed', 'V_N 0'),
    'ExpectedFailureExcessQuotientLoss': ('Tactic `assumption` failed', 'StairBound 1 globalQ'),
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
                      for name in ['WeightedColonAudit', 'RemainderAudit', 'BridgeAudit', 'AllScaleAudit', 'MatrixAudit', 'NewtonAudit', 'OriginAudit'])
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
                        'bounded staircase division and the full V_N intersection theorem '
                        'for the fixed F2 endpoint family d0=1, d1=3, Q=t4+t2+y2. '
                        'The actual binomial-entry F2 matrix has the proved finite index sets '
                        'and dimensions, zero kernel, nonzero square determinant and inverse. '
                        'Integral synthetic Newton coefficients reduce to the concrete binary matrix; '
                        'their square determinant has nonzero reduction modulo two. The actual '
                        'frequency profile has proved prefix nodes, original-column bijections '
                        'and counts, and entrywise integral Newton expansion with nonzero diagonal '
                        'factors. The explicit global Z-matrix multiplication and determinant '
                        'factorization are proved; the actual original integer evaluation '
                        'determinant is nonzero for every N and every proved original-column '
                        'ordering. Integer collision-quotient and rational/integer determinant '
                        'normalization and '
                        'residual-polynomial/analytic bridges are not proved; arbitrary '
                        'arithmetic weights and pi badly approximability are not covered.'}
    (out / 'replay-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'All {len(declarations)} declaration audits and {len(checks)} compilation checks passed.', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
