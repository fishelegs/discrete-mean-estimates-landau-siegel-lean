from pathlib import Path
import hashlib,json
b=Path(__file__).resolve().parent;r=b.parent.parent
m=json.loads((b/'MANIFEST.json').read_text())
for x in m['files']:
 p=b/x['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256'],x['path']
for x in json.loads((b/'SOURCE_HASHES.json').read_text())['unchanged_referenced_Lean_sources']:
 assert hashlib.sha256((r/x['path']).read_bytes()).hexdigest()==x['sha256'],x['path']
print('PASS: public mathematical evidence and referenced Lean-source fingerprints')
