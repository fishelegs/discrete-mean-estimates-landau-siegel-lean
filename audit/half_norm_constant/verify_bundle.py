#!/usr/bin/env python3
"""Verify source-only evidence and rerun finite checks, without modifying files."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import subprocess
import sys

EXPECTED_REPORT = '7fd1bf67bb8bd94474c14467d05c7a36144401e009fa21f14a85291ad5414724'
EXPECTED_REVIEW = '4b359bd05a58c11a3aec508b740dab02b741b2558aa6e41b43174e4b70403e9c'
ACCEPTED_STATUS = 'source_only_independently_reviewed'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def relative_path(name):
    require(isinstance(name, str) and bool(name), 'Empty or non-string path')
    path = PurePosixPath(name)
    require(not path.is_absolute() and '..' not in path.parts,
            'Non-relative path in source inventory')
    require(path.as_posix() == name, 'Non-canonical path in source inventory')
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path,
                        help='Optional repository root for exact source checks')
    parser.add_argument('--require-accepted', action='store_true',
                        help='Require the finalized independent source review')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest_bytes = (root/'MANIFEST.json').read_bytes()
    wanted = (root/'MANIFEST.sha256').read_text().strip().split()
    require(len(wanted) == 2 and wanted[1] == 'MANIFEST.json',
            'Malformed manifest checksum receipt')
    require(sha(manifest_bytes) == wanted[0], 'MANIFEST.json digest mismatch')
    manifest = json.loads(manifest_bytes)
    require(manifest['schema_version'] == 1, 'Unknown manifest schema')
    entries = manifest['files']
    names = [entry['path'] for entry in entries]
    require(len(names) == len(set(names)), 'Duplicate manifest entry')
    actual = {path.relative_to(root).as_posix() for path in root.rglob('*')
              if path.is_file()}
    require(set(names) == actual-{'MANIFEST.json', 'MANIFEST.sha256'},
            'File inventory mismatch')
    require(not any(path.is_symlink() for path in root.rglob('*')),
            'Symlink in evidence package')
    for entry in entries:
        path = root/relative_path(entry['path'])
        data = path.read_bytes()
        require(len(data) == entry['bytes'], entry['path']+' byte length mismatch')
        require(sha(data) == entry['sha256'], entry['path']+' digest mismatch')

    provenance = json.loads((root/'PROVENANCE.json').read_text())
    originals = {item['source_id']: item for item in provenance['historical_originals']}
    require(originals['author_proof']['sha256'] == EXPECTED_REPORT,
            'Original proof identity differs')
    require(originals['independent_review']['sha256'] == EXPECTED_REVIEW,
            'Original independent review identity differs')
    for name, key in [('PROOF.md', 'public_proof_sha256'),
                      ('INDEPENDENT_REVIEW.md', 'public_independent_review_sha256')]:
        require(sha((root/name).read_bytes()) == provenance[key],
                'Public proof/review identity differs from provenance')
    for name, source_id in [('AUTHOR_ORIGINAL.json', 'author_receipt'),
                            ('INDEPENDENT_ORIGINAL.json', 'independent_receipt')]:
        require(sha((root/name).read_bytes()) == originals[source_id]['sha256'],
                'Original receipt identity differs')

    sources = json.loads((root/'SOURCE_HASHES.json').read_text())
    logical_pins = {'repository:'+item['path']: item['sha256']
                    for item in sources['repository_sources']}
    logical_pins.update({'dependency:'+item['source_id']: item['historical_sha256']
                         for item in sources['public_dependencies']})
    logical_pins.update({'original:'+key: item['sha256']
                         for key, item in originals.items()})
    for name, count in [('AUTHOR_SOURCE_MANIFEST.json', 23),
                        ('INDEPENDENT_SOURCE_MANIFEST.json', 39)]:
        source_manifest = json.loads((root/name).read_text())
        require(len(source_manifest) == count, name+' entry count differs')
        for source_id, expected in source_manifest.items():
            require(logical_pins.get(source_id) == expected,
                    name+' source pin differs: '+source_id)

    expected_checks = {'check_author.py': 'AUTHOR_RERUN.json',
                       'check_independent.py': 'INDEPENDENT_RERUN.json'}
    require(manifest['portable_checks'] == expected_checks,
            'Portable checker inventory differs')
    for script, receipt in expected_checks.items():
        result = subprocess.run([sys.executable, str(root/script)], check=True,
                                capture_output=True, text=True, cwd=root)
        require(json.loads(result.stdout) == json.loads((root/receipt).read_text()),
                script+' differs from stored rerun receipt')

    if args.repo:
        for entry in sources['repository_sources']:
            path = args.repo/relative_path(entry['path'])
            require(sha(path.read_bytes()) == entry['sha256'],
                    entry['path']+' repository-source digest differs')
        for entry in sources['public_dependencies']:
            path = args.repo/relative_path(entry['path'])
            require(sha(path.read_bytes()) == entry['public_sha256'],
                    entry['path']+' public-dependency digest differs')

    if args.require_accepted:
        require(manifest['status'] == ACCEPTED_STATUS,
                'Independent mathematical review is not finalized as accepted')
        require(provenance['independent_review_finalized'] is True,
                'Independent review finalization is pending')
        require(manifest['independent_review_original_sha256'] == EXPECTED_REVIEW
                == provenance['independent_review_original_sha256'],
                'Final review identity mismatch')
        require(provenance['independent_review_final_decision'].startswith('ACCEPT at source level'),
                'Missing final source-level acceptance')
        require('**ACCEPT at source level' in (root/'INDEPENDENT_REVIEW.md').read_text(),
                'Public independent review does not record acceptance')
        for key in ('lean_certification', 'strict_gain_proved', 'final_exponent_2024_proved'):
            require(manifest[key] is False and provenance[key] is False,
                    'Acceptance exceeds the reviewed mathematical scope')
        require(manifest['remaining_target'] == 'Re Delta_rho,high <= (1/2-epsilon)m_H + o(1)',
                'Remaining high-rho target differs')
        require(manifest['high_rho_label_condition'] == '2K>P^(99/100)',
                'Original high-rho label condition differs')

    print(json.dumps({
        'integrity': 'PASS', 'finite_checks': 'PASS',
        'repository_source_hashes': 'PASS' if args.repo else 'not requested',
        'mathematical_status': manifest['status'],
        'independent_review_original_sha256': EXPECTED_REVIEW,
        'lean_certification': False, 'strict_gain_proved': False,
        'final_exponent_2024_proved': False,
        'remaining_target': manifest['remaining_target'],
    }, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
