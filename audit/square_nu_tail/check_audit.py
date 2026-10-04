from pathlib import Path
import json,re,sys,hashlib
b=Path(__file__).resolve().parent
if len(sys.argv)!=2:raise SystemExit('Usage: python3 check_audit.py LOG')
s=Path(sys.argv[1]).read_text();d=json.loads((b/'OWNED_DECLARATIONS.json').read_text())
rows=re.findall(r'^OWNER (\S+) DECL (\S+) AXIOMS #?\[([^\]]*)\]',s,re.M)
a={(o,n):sorted(x.strip() for x in axs.split(',') if x.strip()) for o,n,axs in rows}
e={(x['owner'],x['declaration']):sorted(x['axioms']) for x in d['declarations']}
assert len(rows)==len(a)==182 and a==e
assert 'OWNERSHIP_PASS PROOF 155 PUBLIC 100 TEST 27' in s
assert len(re.findall(r'^OWNED_TYPE ',s,re.M))==182
mods=re.findall(r'^LOADED_MODULE (\S+)',s,re.M);assert len(mods)==len(set(mods))==5998
joined='\n'.join(sorted(mods))+'\n'
v=json.loads((b/'VERIFICATION.json').read_text());assert hashlib.sha256(joined.encode()).hexdigest()==v['loaded_modules_sha256']
assert not re.search(r': error(?:\(|:)',s)
print('PASS:155proof+27test owners,100explicit public,all182types,standard axioms,5998modules')
