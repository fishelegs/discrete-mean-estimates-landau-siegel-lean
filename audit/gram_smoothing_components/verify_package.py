from pathlib import Path
import hashlib,json
b=Path(__file__).resolve().parent
r=b.parent.parent
m=json.loads((b/'MANIFEST.json').read_text())
for row in m['files']:
 p=r/row['path']
 assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],row['path']
print('PASS: %d published source/evidence file hashes'%len(m['files']))
