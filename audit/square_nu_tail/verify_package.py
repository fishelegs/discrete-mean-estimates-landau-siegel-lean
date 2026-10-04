from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;r=b.parents[1]
for x in json.loads((b/'MANIFEST.json').read_text())['files']:
 p=r/x['path'];data=p.read_bytes();assert len(data)==x['bytes'] and hashlib.sha256(data).hexdigest()==x['sha256'],x['path']
for m,x in json.loads((b/'PROJECT_SOURCE_PINS.json').read_text()).items():
 assert hashlib.sha256((r/x['path']).read_bytes()).hexdigest()==x['sha256'],m
v=json.loads((b/'VERIFICATION.json').read_text());assert v['proof_owned']==155 and v['total_owned']==182 and v['source_explicit_public']==100
assert not v['fresh_full_project_pass'] and not v['strict_gain_proved']
print('PASS: final sources/audit/evidence and244project source pins; scoped arithmetic theorem only')
