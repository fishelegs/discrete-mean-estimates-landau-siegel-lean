#!/usr/bin/env python3
"""Verify the source-only square-factor audit using pinned public input bytes.

Only this directory, --repo-root and fresh temporary checker directories are
used. The checker neither accesses the network nor invokes Lean. Original
historical files are provenance declarations, not runtime dependencies.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def confined(root, name):
    relative = Path(name)
    require(not relative.is_absolute() and '..' not in relative.parts,
            'Input path is not portable: ' + name)
    path = root / relative
    require(not path.is_symlink(), 'Symlink input is not allowed: ' + name)
    path = path.resolve()
    require(path.is_relative_to(root), 'Input escapes its root: ' + name)
    return path


def verify_file(path, record):
    data = path.read_bytes()
    require(len(data) == record['bytes'], 'Byte count differs: ' + path.name)
    require(hashlib.sha256(data).hexdigest() == record['sha256'],
            'SHA256 differs: ' + path.name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', required=True, type=Path,
                        help='Root containing the public paths listed in INPUTS.json')
    parser.add_argument('--rerun', action='store_true',
                        help='Rerun all three finite checkers in fresh temporary directories')
    args = parser.parse_args()
    repository = args.repo_root.resolve()
    require(repository.is_dir(), 'Repository input root is not a directory')
    manifest_bytes = (ROOT / 'MANIFEST.json').read_bytes()
    seal = (ROOT / 'MANIFEST.sha256').read_text().strip().split()
    require(seal == [hashlib.sha256(manifest_bytes).hexdigest(), 'MANIFEST.json'],
            'Manifest checksum differs')
    manifest = json.loads(manifest_bytes)
    require(manifest['status'] == 'SOURCE_ONLY', 'Manifest scope differs')
    listed = [entry['path'] for entry in manifest['files']]
    require(len(listed) == len(set(listed)), 'Duplicate manifest path')
    actual = sorted(str(path.relative_to(ROOT)) for path in ROOT.rglob('*')
                    if path.is_file() and path.name not in ('MANIFEST.json', 'MANIFEST.sha256'))
    require(sorted(listed) == actual, 'Package contains missing or unlisted files')
    for entry in manifest['files']:
        verify_file(confined(ROOT, entry['path']), entry)

    inputs = read_json(ROOT / 'INPUTS.json')
    require(inputs['source_commit'] == 'cbcfbcbc7ceafaafcf3e711b7216d2f059da192d',
            'Unexpected source commit')
    require(len(inputs['repository_inputs']) == 11, 'Unexpected repository input count')
    input_names = [entry['path'] for entry in inputs['repository_inputs']]
    require(len(set(input_names)) == len(input_names), 'Duplicate repository input')
    for entry in inputs['repository_inputs']:
        verify_file(confined(repository, entry['path']), entry)
        expected_url = inputs['repository_url'] + '/blob/' + inputs['source_commit'] + '/' + entry['path']
        require(entry['source_url'] == expected_url, 'Source URL does not match its pin')

    provenance = read_json(ROOT / 'PROVENANCE.json')
    originals = {entry['id']: entry for entry in provenance['originals']}
    require(len(originals) == 12, 'Unexpected original provenance count')
    require(all(entry['preserved_byte_exact_at_preparation'] and
                not entry['required_for_portable_verifier']
                for entry in originals.values()), 'Invalid historical dependency claim')
    for entry in provenance['public_editions']:
        verify_file(confined(ROOT, entry['path']), entry['public_file'])
        for source in entry['source_ids']:
            require(source in originals, 'Unknown provenance source')
        if entry['relationship'] == 'byte_identical':
            require(len(entry['source_ids']) == 1, 'Ambiguous byte-identical source')
            original = originals[entry['source_ids'][0]]
            require(all(original[key] == entry['public_file'][key] for key in ['bytes', 'sha256']),
                    'Byte-identical provenance does not match')

    scope = read_json(ROOT / 'SCOPE.json')
    require(scope['status'] == 'SOURCE_ONLY' and scope['verdict'] == 'ACCEPT_SOURCE_MATHEMATICS',
            'Mathematical source scope differs')
    for key in ['lean_certification', 'compiler_invoked', 'transitive_axiom_audit_claimed',
                'global_signed_half_threshold_proved', 'exponent_2024_theorem_proved']:
        require(scope[key] is False, 'Source-only scope was promoted: ' + key)
    require(scope['spec_count_change'] == 0 and scope['future_formalization_cross_reference'] is None,
            'Unexpected formalization or Spec status change')
    require(scope['source_hypothesis_exponent'] == 2022 and scope['target_exponent'] == 2024,
            'Hypothesis/target exponents changed')
    require(scope['weighted_tail']['q_min'] == 1 and scope['weighted_tail']['q_max'] == 9,
            'Tail q scope changed')
    require(scope['weighted_tail']['PV_required'] is False, 'PV is not a required input')
    require(scope['completion']['HB_levels'] == [1, 2, 3, 4], 'HB levels differ')
    require(scope['completion']['HB_coefficients'] == [4, -6, 4, -1], 'HB coefficients differ')

    checkers = [('check_author.py', 'AUTHOR_CHECKS.json'),
                ('check_independent.py', 'CHECKS.json'),
                ('check_scope.py', 'SCOPE_CHECKS.json')]
    saved = {result: read_json(ROOT / result) for _, result in checkers}
    require(saved['AUTHOR_CHECKS.json']['checks'] == 6072, 'Author assertion total differs')
    require(saved['CHECKS.json']['assertions'] == 307346, 'Independent assertion total differs')
    require(saved['SCOPE_CHECKS.json']['assertions'] == 10661, 'Scope assertion total differs')
    for result in ['CHECKS.json', 'SCOPE_CHECKS.json']:
        require(sum(saved[result]['counts'].values()) == saved[result]['assertions'],
                'Category total differs: ' + result)
    require(scope['completion']['rows'] == saved['SCOPE_CHECKS.json']['HB_rows'],
            'Completion rows do not match exact checks')
    expected = ['-1273/2', '-1103/2', '-861/2', '-547/2']
    require([row['paired_log'] for row in scope['completion']['rows']] == expected,
            'Completion exponents differ')
    for row in scope['completion']['rows']:
        j, q = row['j'], row['q']
        require(q == 2*j+1 and Fraction(row['paired_log']) ==
                18*j*j+31*j-Fraction(1371, 2), 'Invalid completion budget')
    total = saved['AUTHOR_CHECKS.json']['checks'] + saved['CHECKS.json']['assertions'] + saved['SCOPE_CHECKS.json']['assertions']
    require(scope['verification']['total_finite_assertions'] == total == 324079,
            'Combined finite assertion count differs')
    require(scope['verification']['public_input_pins'] == len(input_names), 'Pin total differs')

    rerun_receipts = []
    if args.rerun:
        for script_name, result_name in checkers:
            with tempfile.TemporaryDirectory(prefix='square-tail-check-') as name:
                temporary = Path(name)
                shutil.copyfile(ROOT / script_name, temporary / script_name)
                subprocess.run([sys.executable, '-I', str(temporary / script_name)],
                               cwd=temporary, capture_output=True, text=True,
                               check=True, timeout=120)
                fresh = read_json(temporary / result_name)
            require(fresh == saved[result_name], 'Fresh receipt differs: ' + result_name)
            rerun_receipts.append(result_name)

    print(json.dumps(dict(
        package_verified=True, status='SOURCE_ONLY', mathematical_verdict=scope['verdict'],
        package_files_verified=len(listed), public_inputs_verified=len(input_names),
        source_commit=inputs['source_commit'], rerun=args.rerun,
        fresh_receipts=rerun_receipts, author_assertions=6072,
        independent_assertions=307346, scope_assertions=10661,
        total_finite_assertions=total, historical_originals_required=False,
        historical_originals_freshly_read=False, compiler_invoked=False,
        lean_certification=False, spec_count_change=0,
        global_signed_half_threshold_proved=False, exponent_2024_theorem_proved=False,
        scope='Byte-integrity and exact finite regressions; universal proofs remain mathematical source claims.'
    ), indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, subprocess.SubprocessError) as error:
        print('Verification failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
