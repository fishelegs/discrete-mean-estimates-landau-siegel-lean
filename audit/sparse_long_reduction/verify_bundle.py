#!/usr/bin/env python3
"""Verify public bytes and rerun finite checks; never compiles Lean."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
p=argparse.ArgumentParser()
p.add_argument('--repo',type=Path,help='Optional repository root for referenced-source checks')
p.add_argument('--require-accepted',action='store_true',help='Fail unless independent mathematical review accepted this scope')
a=p.parse_args(); root=Path(__file__).resolve().parent
manifest_bytes=(root/'MANIFEST.json').read_bytes()
expected=(root/'MANIFEST.sha256').read_text().split()[0]
assert hashlib.sha256(manifest_bytes).hexdigest()==expected,'MANIFEST.json digest mismatch'
m=json.loads(manifest_bytes)
expected_names={x['path'] for x in m['files']}
actual_names={x.name for x in root.iterdir() if x.is_file()}-{'MANIFEST.json','MANIFEST.sha256'}
assert expected_names==actual_names,'File inventory mismatch'
for item in m['files']:
 path=root/item['path']; data=path.read_bytes()
 assert path.is_file() and len(data)==item['bytes'],item['path']
 assert hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
for script,receipt in m['portable_checks'].items():
 result=subprocess.run([sys.executable,str(root/script)],check=True,capture_output=True,text=True,cwd=root)
 observed=json.loads(result.stdout); recorded=json.loads((root/receipt).read_text())
 for payload in (observed,recorded):
  if 'max_numerical_fourier_absolute_error' in payload:
   error=payload.pop('max_numerical_fourier_absolute_error')
   assert 0<=error<=5e-10,'Fourier numerical error exceeds tolerance'
 assert observed==recorded,script+' differs from stored result'
if a.repo:
 for item in json.loads((root/'SOURCE_HASHES.json').read_text())['repository_sources']:
  assert hashlib.sha256((a.repo/item['path']).read_bytes()).hexdigest()==item['sha256'],item['path']
 for item in json.loads((root/'SOURCE_HASHES.json').read_text())['public_dependencies']:
  assert hashlib.sha256((a.repo/item['path']).read_bytes()).hexdigest()==item['public_sha256'],item['path']
if a.require_accepted:
 assert m['status']=='source_only_independently_reviewed','Independent review has not accepted the candidate'
 assert (root/'INDEPENDENT_REVIEW.md').is_file(),'Missing independent review'
print(json.dumps({'integrity':'PASS','finite_checks':'PASS','repository_source_hashes':'PASS' if a.repo else 'not requested','mathematical_status':m['status'],'lean_certification':False,'strict_gain_proved':False},indent=2))
