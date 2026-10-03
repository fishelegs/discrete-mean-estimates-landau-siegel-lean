from pathlib import Path
import argparse,hashlib,json,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--repo',type=Path);args=p.parse_args()
root=Path(__file__).resolve().parent
read=lambda x:json.loads(x.read_text())
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
m=read(root/'MANIFEST.json')
assert m['status']=='source_only_independently_reviewed'
for x in m['files']:assert sha(root/x['path'])==x['sha256'],x['path']
if args.repo:
 for x in read(root/'SOURCE_HASHES.json')['repository_dependencies']:assert sha(args.repo/x['path'])==x['sha256'],x['path']
for script,receipt in [('check_author.py','AUTHOR_RERUN.json'),('check_independent.py','INDEPENDENT_RERUN.json')]:
 out=json.loads(subprocess.check_output([sys.executable,str(root/script)],text=True));expected=read(root/receipt)
 if 'largest_gauss_identity_error' in out:
  assert out.pop('largest_gauss_identity_error')<1e-10
  assert expected.pop('largest_gauss_identity_error')<1e-10
 assert out==expected,script
print('PASS: source package integrity, finite/rational checks and requested dependency pins; no Lean or signed-gain certificate')
