#!/usr/bin/env python3
"""Verify local public evidence bytes; optionally rerun finite checks in isolation.

This does not run Lean or certify an analytic estimate or a signed gap.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--rerun', action='store_true', help='Rerun finite checks using installed dependencies; receipts go to a temporary directory.')
args = parser.parse_args()
manifest_bytes = (ROOT / 'MANIFEST.json').read_bytes()
expected_manifest = (ROOT / 'MANIFEST.sha256').read_text().split()[0]
assert hashlib.sha256(manifest_bytes).hexdigest() == expected_manifest, 'Manifest hash mismatch'
manifest = json.loads(manifest_bytes)
for row in manifest['files']:
    rel = Path(row['path'])
    assert not rel.is_absolute() and '..' not in rel.parts, 'Nonportable manifest path'
    path = ROOT / rel
    assert path.is_file() and not path.is_symlink(), f'Missing/nonregular file: {rel}'
    assert path.stat().st_size == row['bytes'], f'Size mismatch: {rel}'
    assert hashlib.sha256(path.read_bytes()).hexdigest() == row['sha256'], f'Hash mismatch: {rel}'
for receipt in manifest['receipts']:
    assert json.loads((ROOT / receipt).read_text())['status'] == 'PASS', receipt
reruns = []
if args.rerun:
    with tempfile.TemporaryDirectory(prefix='signed-phase-checks-') as temporary:
        for check in manifest['checks']:
            output = Path(temporary) / (Path(check['script']).stem + '.json')
            run = subprocess.run([sys.executable, str(ROOT / check['script']), '--output', str(output)],
                                 cwd=temporary, capture_output=True, text=True)
            if run.returncode:
                raise RuntimeError(f"{check['script']} failed: {run.stderr[-3000:]}")
            fresh = json.loads(output.read_text())
            assert fresh['status'] == 'PASS', check['script']
            baseline = json.loads((ROOT / check['baseline']).read_text())
            for key in check['stable_fields']:
                assert fresh[key] == baseline[key], (check['script'], key)
            reruns.append({'script': check['script'], 'status': 'PASS'})
print(json.dumps({'status': 'PASS', 'files_verified': len(manifest['files']),
                  'receipts_verified': len(manifest['receipts']), 'reruns': reruns,
                  'scope': 'Byte integrity and finite regression evidence only; SOURCE_ONLY, not a Lean certificate or signed-gain theorem.'}, indent=2))
