#!/usr/bin/env python3
"""Compile and audit the weighted-colon checkpoint using an existing pinned cache.

No Lake command, installation, network request, hook or dependency build is run.
All compilers run serially, with one worker. Existing modules retain a 4096 MiB
limit; modules importing the attributed broad-Mathlib A7 proof use 8192 MiB.
"""
import argparse
import fcntl
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
EXTRA_CORE = ['RemainderVanish', 'QuadraticRemainder', 'EndpointRemainderBridge', 'RightRemainderBridge', 'StaircaseDivision', 'StaircaseNonvanishing', 'MatrixIndices', 'MatrixEntries', 'BinaryMatrixNonvanishing', 'NewtonIntegral', 'IntegerNewtonMatrix', 'FrequencyProfile', 'IntegerOriginNonvanishing', 'RationalOriginNonvanishing', 'HermitePolynomialNonvanishing', 'HermiteComplexSpecialization', 'PiHermiteNonvanishing', 'ApproximationPairs', 'SqrtTwoBenchmark', 'SqrtTwoPellPairs', 'LogPadeRecurrence', 'LogPadeCoefficients', 'LogPadeCoefficientRecurrence', 'LogPadeNormalization', 'LogPadeFiniteIdentity']
REGRESSIONS = ['WeightedColonRegression', 'RemainderRegression', 'BridgeRegression', 'AllScaleRegression', 'MatrixRegression', 'NewtonRegression', 'OriginRegression', 'RationalRegression', 'HermiteRegression', 'SpecializationRegression', 'PiSpecializationRegression', 'ApproximationPairsRegression', 'LogPadeRegression']
VENDOR_PREFIX = 'LeanFormalizations.NumberTheory.Transcendence.'
VENDOR = [VENDOR_PREFIX + name for name in ['ETranscendental', 'PiLindemann', 'HermiteLindemann', 'MonicRootSums', 'SubsetSumEsymm', 'PiTranscendental']]
AUDITS = ['WeightedColonAudit', 'RemainderAudit', 'BridgeAudit', 'AllScaleAudit', 'MatrixAudit', 'NewtonAudit', 'OriginAudit', 'RationalAudit', 'HermiteAudit', 'SpecializationAudit', 'A7ImportedAudit', 'PiSpecializationAudit', 'ApproximationPairsAudit', 'LogPadeAudit']
POSITIVE = VENDOR + CORE + EXTRA_CORE + REGRESSIONS + AUDITS
LARGE_IMPORTS = set(VENDOR + ['PiHermiteNonvanishing', 'PiSpecializationRegression', 'A7ImportedAudit', 'PiSpecializationAudit', 'ExpectedFailurePiMatrixEntry', 'ExpectedFailurePiParameterSubstitution'])
NEGATIVE = {
    'ExpectedFailureLogPadeExponent': ('Type mismatch', 'X ^ 2'),
    'ExpectedFailureLogPadeNormalizedSign': ('Type mismatch', '= -(1 / 6)'),
    'ExpectedFailureLogPadeNormalizedFactor': ('Type mismatch', 'logPadeRationalQ 1 * logPadeRationalP 0 = 1'),
    'ExpectedFailureLogPadeNumeratorScale': ('Type mismatch', 'logPadeLCoeff 1 1 = 1 / 2'),
    'ExpectedFailureLogPadeMissingNormalization': ('Type mismatch', '/ (1 + Complex.I) ^ 1'),
    'ExpectedFailurePairsWithoutIndependence': ('Application type mismatch', 'PiWeightedColon.HasApproximationPairs 0 1 0'),
    'ExpectedFailureSqrtTwoZeroDenominator': ('unsolved goals', '⊢ False'),
    'ExpectedFailurePairsEtaOne': ('unsolved goals', '⊢ False'),
    'ExpectedFailurePairsMissingGrowth': ('Application type mismatch', '↑b ≤ C * ↑q'),
    'ExpectedFailurePairsSingleScale': ('Application type mismatch', 'PiWeightedColon.HasApproximationPairs (√2) 9 (1 / 2)'),
    'ExpectedFailurePiMatrixEntry': ('Type mismatch', 'piHermiteParameter + 3'),
    'ExpectedFailurePiParameterSubstitution': ('Type mismatch', '4 * Complex.I'),
    'ExpectedFailureComplexEntry': ('Type mismatch', 'Complex.I + 3'),
    'ExpectedFailureRationalParameterTranscendence': ('Type mismatch', 'Transcendental ℚ (imaginaryRealParameter 2)'),
    'ExpectedFailureUnavailablePiTranscendence': ('Unknown constant `Real.transcendental_pi`', 'error(lean.unknownIdentifier)'),
    'ExpectedFailureHermiteConstant': ('Type mismatch', 'Polynomial.coeff (hermiteCoefficientEntry 1 1 1 2 1) 1 = 0'),
    'ExpectedFailureHermiteEval': ('Type mismatch', 'Polynomial.eval 0 (hermiteCoefficientEntry 1 1 1 2 1) = 1'),
    'ExpectedFailureRationalEntry': ('Type mismatch', 'rationalOriginEntry 3 0 0 3 = 27'),
    'ExpectedFailureRationalDet': ('Type mismatch', 'rationalScaleZeroOrdering).det = 1'),
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


def proof_text(source):
    """Remove nested Lean comments before scanning executable proof syntax."""
    result, index, depth = [], 0, 0
    while index < len(source):
        pair = source[index:index + 2]
        if pair == '/-':
            depth += 1
            index += 2
        elif depth and pair == '-/':
            depth -= 1
            index += 2
        elif depth:
            if source[index] == '\n':
                result.append('\n')
            index += 1
        elif pair == '--':
            end = source.find('\n', index)
            index = len(source) if end == -1 else end
        else:
            result.append(source[index])
            index += 1
    if depth:
        raise RuntimeError('Unclosed Lean comment')
    return ''.join(result)


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

    vendor_root = ROOT / 'vendor/gotrevor-pi'
    vendor = json.loads((vendor_root / 'provenance.json').read_text())
    if vendor['revision'] != 'bad0e21a37874f09f45072dad6225de55742e6c5':
        parser.error('Wrong A7 upstream commit')
    if sha(vendor_root / 'LICENSE') != vendor['license_sha256']:
        parser.error('A7 license hash mismatch')
    expected_vendor_files = {str(Path(*name.split('.')).with_suffix('.lean')) for name in VENDOR}
    if set(vendor['files']) != expected_vendor_files:
        parser.error('A7 scope is not exactly the six approved project modules')
    vendor_declarations = {}
    for relative, record in vendor['files'].items():
        source = vendor_root / 'src' / relative
        if sha(source) != record['ported_sha256']:
            parser.error(f'A7 source hash mismatch: {relative}')
        if record['compatibility_edits'] or record['ported_sha256'] != record['upstream_sha256']:
            parser.error('This checkpoint requires the original six sources without compatibility edits')
        code = proof_text(source.read_text())
        if re.search(r'\b(sorry|admit|native_decide|unsafe|axiom|run_cmd|initialize|implemented_by|extern)\b', code):
            parser.error(f'Prohibited A7 proof construct: {relative}')
        for imported in re.findall(r'^import (\S+)\s*$', code, re.M):
            if not (imported == 'Mathlib' or imported.startswith('Mathlib.') or imported in VENDOR):
                parser.error(f'Unapproved A7 project import: {imported}')
        namespace = ''
        for line in code.splitlines():
            match = re.match(r'^namespace (\S+)', line)
            if match:
                namespace = match.group(1) + '.'
            elif line.startswith('end LeanFormalizations.Transcendence.SubsetSumEsymm'):
                namespace = ''
            match = re.match(r'^(theorem|lemma) (\w+)\b', line)
            if match:
                vendor_declarations[namespace + match.group(2)] = match.group(1)
    if vendor_declarations != vendor['declarations']:
        parser.error('A7 declaration inventory mismatch')

    attestation = json.loads((ROOT / 'verification/dependency-attestation.json').read_text())
    imports = {}
    for module, expected in attestation['direct_imports'].items():
        relative = Path(*module.split('.'))
        if module == 'Mathlib' or module.startswith('Mathlib.'):
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

    gap = json.loads((ROOT / 'verification/pi-transcendence-gap.json').read_text())
    mathlib_revision = next(p['rev'] for p in pins['packages'] if p['name'] == 'mathlib')
    if gap['mathlib_revision'] != mathlib_revision:
        parser.error('Wrong mathlib revision in the pi-transcendence gap record')
    for relative, digest in gap['source_hashes'].items():
        if sha(project / '.lake/packages/mathlib' / relative) != digest:
            parser.error(f'Pi-transcendence source evidence mismatch: {relative}')

    build, logs = out / 'build', out / 'logs'
    build.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    libraries = sorted((project / '.lake/packages').glob('*/.lake/build/lib/lean'))
    env = os.environ.copy()
    env.update(LEAN_PATH=':'.join(map(str, [build] + libraries)), LEAN_NUM_THREADS='1')
    checks = []
    slot = Path('/tmp/mc6-lean-slots')
    slot.mkdir(exist_ok=True)
    lock = (slot / '8gib.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX)
    for name in POSITIVE + list(NEGATIVE):
        relative = Path(*name.split('.'))
        source = ((vendor_root / 'src') if name in VENDOR else (ROOT / 'src')) / relative.with_suffix('.lean')
        output = build / relative.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        if output.exists():
            output.unlink()
        command = [str(lean), '-j1', '-M8192' if name in LARGE_IMPORTS else '-M4096', '-DautoImplicit=false',
                   '-DwarningAsError=true', '-o', str(output), str(source)]
        started = time.monotonic()
        cwd = vendor_root / 'src' if name in VENDOR else ROOT / 'src'
        run = subprocess.run(command, cwd=cwd, env=env, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs / relative.with_suffix('.log')
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text(run.stdout)
        expected_failure = name in NEGATIVE
        passed = (run.returncode == 0 and output.is_file()) if not expected_failure else (
            run.returncode == 1 and len(re.findall(r'error(?:\([^\n)]*\))?:', run.stdout)) == 1 and
            all(fragment in run.stdout for fragment in NEGATIVE[name]) and not output.exists())
        check = {'module': name, 'command': command, 'cwd': str(cwd),
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

    declarations = dict(vendor_declarations)
    for name in CORE + EXTRA_CORE + REGRESSIONS:
        source = proof_text((ROOT / 'src' / (name + '.lean')).read_text())
        if re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b', source):
            raise RuntimeError(f'Prohibited proof construct in {name}')
        namespace = 'PiWeightedColon.Regression.' if name.endswith('Regression') else 'PiWeightedColon.'
        for kind, declaration in re.findall(r'^(theorem|def|abbrev|instance) (\w+)\b', source, re.M):
            declarations[namespace + declaration] = kind
    audit = '\n'.join((logs / (name + '.log')).read_text()
                      for name in AUDITS)
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
               'attributed_pi_transcendence_import': vendor,
               'pi_transcendence_gap': gap,
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
                        'ordering. The actual guarded rational origin entry is proved to scale '
                        'by row a!s! and column 1/c! to the integer entry, all scales are nonzero, '
                        'and the actual rational origin determinant is nonzero for every N and '
                        'every proved original-column ordering. The actual Hermite coefficient matrix '
                        'over Q[x] is defined using monic remainders of z^d modulo z^n(z-x)^n; '
                        'its evaluation at x=0 is proved equal to the rational origin matrix, '
                        'and its determinant polynomial is nonzero for every N and every proved '
                        'original-column ordering. Its complex evaluation is proved equal to the '
                        'determinant of the actual complex matrix with original row and column labels. '
                        'At every complex point proved transcendental over Q, both are nonzero for '
                        'all N. For any real r, transcendence of 2*r*i is proved equivalent to '
                        'transcendence of r. The six separately attributed original A7 modules at '
                        'gotrevor commit bad0e21a37874f09f45072dad6225de55742e6c5 compile on the unchanged '
                        '4.30 pins without compatibility edits; all their named declarations are '
                        'recursively axiom-audited. Their ordinary Real.pi transcendence theorem '
                        'supplies the input, so the actual Hermite determinant at literal 2*pi*i '
                        'is nonzero for every N and every original-column reindexing, without an '
                        'unproved transcendence assumption. The pointwise '
                        'result supplies no uniform analytic lower bound. The derivative-jet x^nu '
                        'factor, Schur-compressed '
                        'residual identity, integer collision-quotient and '
                        'residual-polynomial/analytic bridges are not proved; arbitrary '
                        'arithmetic weights and pi badly approximability are not covered. '
                        'Separately, every integer p and positive integer q satisfy the explicit '
                        'sqrt(2) lower bound 1/(4*q^2). An all-positive-integer-scale pair criterion '
                        'with positive denominators bounded by C*Q, nonzero integer determinant '
                        'and linear errors at most eta/Q supplies the positive constant (1-eta)/C '
                        'when C>0 and 0<=eta<1. The explicit Pell recurrence constructs this '
                        'interface for sqrt(2) with C=9 and eta=1/2, giving 1/(18*q^2). '
                        'These benchmarks and the reusable criterion supply no such pair '
                        'construction or uniform lower bound for pi. '
                        'The logarithmic Pade polynomials are defined by the specified finite '
                        'binomial and harmonic-number coefficient sums over Q. Their equality '
                        'with the three-term recurrence family is proved for every natural r; '
                        'the exact adjacent determinant is d_r*x^(2*r+1), where '
                        'd_r=(r!)^4/((2*r)!*(2*r+1)!) is positive. At x=1-i, the specified '
                        'normalizations P_r/(1+i)^r and 2*i*L_r/(1+i)^r equal explicitly '
                        'constructed rational sequences for every r. Their exact complex, '
                        'rational and real adjacent determinant is 2*(-1)^r*d_r and is nonzero. '
                        'No general binomial-parameter identity, formal logarithmic remainder '
                        'order, complex integral, convergence to pi, denominator clearing, '
                        'integer linear-error bound, Baker irrationality measure or pi BA '
                        'statement is formalized by this Pade addition.'}
    (out / 'replay-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'All {len(declarations)} declaration audits and {len(checks)} compilation checks passed.', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
