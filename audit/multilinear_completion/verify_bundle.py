#!/usr/bin/env python3
"""Verify the portable mathematical audit; no network or compiler is used.

Only this directory and --repo-root are read. A fresh independent run uses a
new temporary directory, preserving both the bundle and repository.
Historical original hashes are declarations, not files required by this tool.
"""
import argparse
import hashlib
import json
import math
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))

def confined(root, relative):
    rel = Path(relative)
    require(not rel.is_absolute() and '..' not in rel.parts, 'Non-portable input path')
    path = (root / rel).resolve()
    require(path.is_relative_to(root), 'Input path escapes its declared root')
    return path

def verify_file(path, item):
    data = path.read_bytes()
    require(len(data) == item['bytes'], 'Byte count mismatch: ' + item.get('path', path.name))
    require(hashlib.sha256(data).hexdigest() == item['sha256'],
            'SHA256 mismatch: ' + item.get('path', path.name))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', required=True, type=Path,
                        help='Repository containing the public input paths in INPUTS.json')
    parser.add_argument('--rerun', action='store_true', help='Rerun independent finite checks')
    args = parser.parse_args()
    repository = args.repo_root.resolve()
    require(repository.is_dir(), 'Repository root is not a directory')
    manifest = read_json(ROOT / 'MANIFEST.json')
    paths = [x['path'] for x in manifest['files']]
    require(len(paths) == len(set(paths)), 'Duplicate manifest paths')
    for item in manifest['files']:
        verify_file(confined(ROOT, item['path']), item)
    inputs = read_json(ROOT / 'INPUTS.json')
    require(len(inputs['repository_inputs']) == 22, 'Unexpected source input count')
    require(len(inputs['public_ancestry_mappings']) == 2, 'Unexpected ancestry mapping count')
    for item in inputs['repository_inputs']:
        verify_file(confined(repository, item['path']), item)
    for mapping in inputs['public_ancestry_mappings']:
        history = read_json(confined(repository, mapping['history_path']))
        matching = [x for x in history['historical_sources']
                    if x.get('original_sha256') == mapping['original_sha256']]
        require(len(matching) == 1, 'Ambiguous historical source mapping')
        require(matching[0]['curated_sha256'] == mapping['public_sha256'],
                'Historical-to-public mapping mismatch')
        actual = hashlib.sha256(confined(repository, mapping['public_path']).read_bytes()).hexdigest()
        require(actual == mapping['public_sha256'], 'Public ancestry bytes mismatch')
    provenance = read_json(ROOT / 'PROVENANCE.json')
    for entry in provenance['derived_public_editions']:
        verify_file(confined(ROOT, entry['path']), entry['derived_public'])
    for entry in provenance['retained_independent_files']:
        require(entry['original_source'] == entry['distributed_file'],
                'Independent file is not byte-identical to original')
        verify_file(confined(ROOT, entry['path']), entry['distributed_file'])
    archival = read_json(ROOT / 'ARCHIVAL_PROVENANCE.json')
    missing = [x['id'] for x in archival['originals'] if x['status'] == 'original_bytes_unavailable']
    require(len(archival['originals']) == 9 and len(missing) == 8, 'Archival count mismatch')
    require(archival['missing_original_count'] == 8 and not archival['author_checker_rerun'],
            'Invalid archival scope')
    scope = read_json(ROOT / 'SCOPE.json')
    require(not scope['lean_certification'] and not scope['global_signed_half_threshold_proved'],
            'Source scope improperly promoted')
    require(scope['verification']['public_input_pins'] == len(inputs['repository_inputs']),
            'Scope input count mismatch')
    require(scope['verification']['historical_to_public_mappings'] == 2, 'Scope mapping count mismatch')
    saved = read_json(ROOT / 'CHECKS.json')
    require(saved['passed'] and saved['assertions'] == 53354, 'Unexpected independent check receipt')
    require(sum(saved['categories'].values()) == saved['assertions'], 'Assertion count mismatch')
    require(scope['verification']['independent_assertions'] == saved['assertions'], 'Scope total mismatch')
    require(scope['verification']['category_count'] == len(saved['categories']), 'Scope categories mismatch')
    require(math.isfinite(saved['maximum_normalized_error']) and
            0 <= saved['maximum_normalized_error'] < saved['tolerance'], 'Numerical error exceeds tolerance')
    rerun = False
    fresh_error = None
    if args.rerun:
        with tempfile.TemporaryDirectory(prefix='multilinear-public-check-') as directory:
            script = Path(directory) / 'check_independent.py'
            shutil.copyfile(ROOT / 'check_independent.py', script)
            completed = subprocess.run([sys.executable, '-I', str(script)],
                                       capture_output=True, text=True, check=True)
            fresh = read_json(Path(directory) / 'CHECKS.json')
        fresh_error = fresh.pop('maximum_normalized_error')
        saved_without_error = dict(saved)
        saved_without_error.pop('maximum_normalized_error')
        require(math.isfinite(fresh_error) and 0 <= fresh_error < fresh['tolerance'],
                'Fresh numerical error exceeds tolerance')
        require(fresh == saved_without_error, 'Fresh independent receipt differs')
        rerun = True
    summary = {
        'package_verified': True,
        'package_files_verified': len(manifest['files']),
        'repository_source_commit': inputs['source_commit'],
        'public_inputs_verified': len(inputs['repository_inputs']),
        'historical_to_public_mappings_verified': len(inputs['public_ancestry_mappings']),
        'independent_checker_rerun': rerun,
        'independent_assertions': saved['assertions'],
        'independent_check_categories': len(saved['categories']),
        'fresh_maximum_normalized_error': fresh_error,
        'original_author_source_recovered_byte_exact_at_preparation': True,
        'original_author_source_distributed': False,
        'original_author_source_freshly_verified_by_this_portable_run': False,
        'author_checker_rerun': False,
        'unavailable_archival_original_count': len(missing),
        'unavailable_archival_original_ids': missing,
        'historical_provenance_complete': False,
        'mathematical_verdict': scope['verdict'],
        'lean_certification': False,
        'global_signed_half_threshold_proved': False,
        'verification_scope': saved['scope'],
    }
    print(json.dumps(summary, indent=2))

if __name__ == '__main__':
    try:
        main()
    except (AssertionError, ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        print('Verification failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
