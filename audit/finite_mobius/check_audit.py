from pathlib import Path
import json,re,sys,hashlib
base=Path(__file__).resolve().parent
if len(sys.argv)!=2:raise SystemExit('Usage: python3 check_audit.py LOG')
s=Path(sys.argv[1]).read_text();expected=json.loads((base/'OWNED_DECLARATIONS.json').read_text())
rows=re.findall(r'^OWNER (\S+) DECL (\S+) AXIOMS #?\[([^\]]*)\]',s,re.M)
a={(o,n):sorted(x.strip() for x in axs.split(',') if x.strip()) for o,n,axs in rows}
e={(x['owner'],x['declaration']):sorted(x['axioms']) for x in expected['declarations']}
assert len(rows)==len(a)==23 and a==e
assert 'OWNERSHIP_PASS 23 PUBLIC 19' in s
mods=re.findall(r'^LOADED_MODULE (\S+)',s,re.M)
assert len(mods)==len(set(mods))==3293
assert ('\n'.join(sorted(mods))+'\n')==(base/'IMPORTED_MODULES.txt').read_text()
assert not re.search(r': error(?:\(|:)',s)
print('PASS: exact 23 owned,19 public,standard axioms and3293 loaded modules')
