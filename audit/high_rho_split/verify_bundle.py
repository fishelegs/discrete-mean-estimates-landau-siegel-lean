#!/usr/bin/env python3
"""Verify source-only evidence and rerun finite checks without modifying files."""
from pathlib import Path, PurePosixPath
from decimal import Decimal
import argparse
import hashlib
import json
import os
import subprocess
import sys

EXPECTED_PROOF = '406fc6bb49533adbbce81142924a2ad4d11517c532a5361094a4074c7f5b409b'
EXPECTED_REVIEW = '2b0058599fb94c7da901c017d380bd8fecc8d9113545cac5a913812aa0763c30'
STATUS = 'source_only_independently_reviewed'
TARGET = 'Re Delta_large-rare <= (1/2-epsilon)m_H + o(1)'
FALSE_CLAIMS = ('lean_certification', 'strict_gain_proved',
                'full_rare_part_signed_bound_proved', 'final_exponent_2024_proved')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def relative_path(name):
    require(isinstance(name, str) and bool(name), 'Empty or non-string path')
    path = PurePosixPath(name)
    require(not path.is_absolute() and '..' not in path.parts,
            'Non-relative source inventory path')
    require(path.as_posix() == name, 'Non-canonical source inventory path')
    return path


def compare_receipt(actual, expected):
    actual, expected = dict(actual), dict(expected)
    for field in ('normalized_gauss_max_error', 'normalized_fourier_max_error'):
        if field in expected:
            for receipt in (actual, expected):
                value = Decimal(receipt.pop(field))
                require(value.is_finite() and Decimal(0) <= value < Decimal('1e-35'),
                        field + ' exceeds the original strict tolerance')
    require(actual == expected, 'Finite mathematical receipt differs')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, help='Optional root for exact source pins')
    parser.add_argument('--require-accepted', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest_bytes = (root/'MANIFEST.json').read_bytes()
    receipt = (root/'MANIFEST.sha256').read_text().strip().split()
    require(len(receipt) == 2 and receipt[1] == 'MANIFEST.json', 'Malformed manifest checksum')
    require(sha(manifest_bytes) == receipt[0], 'Manifest digest mismatch')
    manifest = json.loads(manifest_bytes)
    require(manifest['schema_version'] == 1, 'Unknown manifest schema')
    entries = manifest['files']
    names = [item['path'] for item in entries]
    require(len(names) == len(set(names)), 'Duplicate inventory entry')
    require(not any(path.is_symlink() for path in root.rglob('*')), 'Symlink in package')
    actual_files = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
    require(set(names) == actual_files-{'MANIFEST.json', 'MANIFEST.sha256'}, 'File inventory mismatch')
    for entry in entries:
        data = (root/relative_path(entry['path'])).read_bytes()
        require(len(data) == entry['bytes'], entry['path']+' size mismatch')
        require(sha(data) == entry['sha256'], entry['path']+' digest mismatch')

    provenance = json.loads((root/'PROVENANCE.json').read_text())
    originals = {item['source_id']: item for item in provenance['historical_originals']}
    require(originals['author_proof']['sha256'] == EXPECTED_PROOF, 'Original proof identity differs')
    require(originals['independent_review']['sha256'] == EXPECTED_REVIEW, 'Original review identity differs')
    for name, key in [('PROOF.md', 'public_proof_sha256'),
                      ('INDEPENDENT_REVIEW.md', 'public_independent_review_sha256')]:
        require(sha((root/name).read_bytes()) == provenance[key], 'Public document identity differs')
    for name, key in [('AUTHOR_ORIGINAL.json', 'author_receipt'),
                      ('INDEPENDENT_ORIGINAL.json', 'independent_receipt')]:
        require(sha((root/name).read_bytes()) == originals[key]['sha256'], 'Original receipt differs')

    sources = json.loads((root/'SOURCE_HASHES.json').read_text())
    pins = {'repository:'+item['path']: item['sha256'] for item in sources['repository_sources']}
    for item in sources['public_dependencies']:
        pins['repository:'+item['path']] = item['public_sha256']
        if 'historical_sha256' in item:
            pins['dependency:'+item['source_id']] = item['historical_sha256']
    pins.update({'original:'+key: item['sha256'] for key, item in originals.items()})
    for name, count in [('AUTHOR_SOURCE_MANIFEST.json', 9), ('INDEPENDENT_SOURCE_MANIFEST.json', 18)]:
        source_manifest = json.loads((root/name).read_text())
        require(len(source_manifest) == count, name+' source count differs')
        for source_id, wanted in source_manifest.items():
            require(pins.get(source_id) == wanted, name+' source pin differs: '+source_id)

    checks = {'check_author.py': 'AUTHOR_RERUN.json', 'check_independent.py': 'INDEPENDENT_RERUN.json'}
    require(manifest['portable_checks'] == checks, 'Portable checker inventory differs')
    env = dict(os.environ)
    env.pop('PYTHONOPTIMIZE', None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    for script, name in checks.items():
        result = subprocess.run([sys.executable, '-B', str(root/script)],
                                check=True, capture_output=True, text=True, cwd=root, env=env)
        compare_receipt(json.loads(result.stdout), json.loads((root/name).read_text()))

    if args.repo:
        for entry in sources['repository_sources']:
            path = args.repo/relative_path(entry['path'])
            require(sha(path.read_bytes()) == entry['sha256'], entry['path']+' source differs')
        for entry in sources['public_dependencies']:
            path = args.repo/relative_path(entry['path'])
            require(sha(path.read_bytes()) == entry['public_sha256'], entry['path']+' dependency differs')

    if args.require_accepted:
        require(manifest['status'] == STATUS, 'Independent source acceptance is not finalized')
        require(provenance['independent_review_finalized'] is True, 'Review is not finalized')
        require(manifest['independent_review_original_sha256'] == EXPECTED_REVIEW
                == provenance['independent_review_original_sha256'], 'Final review identity differs')
        require(provenance['independent_review_final_decision'].startswith('ACCEPT at source level'),
                'Missing final source-level acceptance')
        require('**ACCEPT at source level' in (root/'INDEPENDENT_REVIEW.md').read_text(),
                'Public independent review does not record acceptance')
        for key in FALSE_CLAIMS:
            require(manifest[key] is False and provenance[key] is False, 'Acceptance exceeds scope: '+key)
        require(manifest['remaining_target'] == TARGET, 'Remaining signed target differs')
        require(manifest['high_rho_label_condition'] == '2K>P^(99/100)', 'Whole-label condition differs')
        require(manifest['paid_selector'] == 'b_chi(v)<=P^(1/100)', 'Paid selector differs')
        require(manifest['paid_error'] == 'O(a^-1 P^-1/200)', 'Paid error differs')
        require(manifest['source_assumption_exponent'] == 2022 and manifest['final_target_exponent'] == 2024,
                'Source or target exponent changed')

    print(json.dumps({'integrity': 'PASS', 'finite_checks': 'PASS',
                      'repository_source_hashes': 'PASS' if args.repo else 'not requested',
                      'mathematical_status': manifest['status'],
                      'independent_review_original_sha256': EXPECTED_REVIEW,
                      **{key: False for key in FALSE_CLAIMS},
                      'paid_error': manifest['paid_error'],
                      'remaining_target': manifest['remaining_target']}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
