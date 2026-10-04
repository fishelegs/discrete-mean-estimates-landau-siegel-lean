from pathlib import Path
import hashlib,json,subprocess,tempfile,shutil,sys
base=Path(__file__).resolve().parent;repo=base.parents[1]
m=json.loads((base/'MANIFEST.json').read_text())
for item in m['files']:
 p=repo/item['path'];data=p.read_bytes()
 assert len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
v=json.loads((base/'VERIFICATION.json').read_text())
assert v['public_count']==19 and v['all_owned_count']==23 and not v['fresh_full_project_pass'] and not v['strict_gain_proved']
with tempfile.TemporaryDirectory(prefix='finite-mobius-check-') as directory:
 t=Path(directory);shutil.copyfile(base/'check_exact_semantics.py',t/'check_exact_semantics.py')
 run=subprocess.run([sys.executable,'-I',str(t/'check_exact_semantics.py')],cwd=t,check=True,capture_output=True,text=True)
 assert json.loads(run.stdout)==json.loads((base/'exact_semantics.json').read_text())
print('PASS: pinned source/audits/package and exact integer regressions; full-project recovery remains separate')
