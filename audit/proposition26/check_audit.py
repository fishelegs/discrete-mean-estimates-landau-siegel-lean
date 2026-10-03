"""Check a captured `lake env lean audit/CloudProposition26Axioms.lean` log."""
from pathlib import Path
import collections,hashlib,json,re,sys
base=Path(__file__).resolve().parent
if len(sys.argv)!=2:raise SystemExit('Usage: python3 check_audit.py path/to/CloudProposition26Axioms.log')
text=Path(sys.argv[1]).read_text()
ver=json.loads((base.parent/'cloud_proposition26_verification.json').read_text())
owned=json.loads((base/'OWNED_DECLARATIONS.json').read_text())['declarations']
expected={(x['owner'],x['name']):set(x['axioms']) for x in owned}
records=re.findall(r'^OWNER (\S+) DECL (\S+) AXIOMS \[([^\]]*)\]',text,re.M)
actual={(m,n):set(a.strip() for a in axioms.split(',') if a.strip()) for m,n,axioms in records}
assert len(records)==len(actual)==437 and actual==expected
assert {m:int(n) for m,n in re.findall(r'^OWNER_COUNT (\S+) (\d+)',text,re.M)}==ver['owner_counts']
mods=re.findall(r'^LOADED_MODULE (\S+)',text,re.M)
assert len(mods)==len(set(mods))==7365
assert hashlib.sha256(('\n'.join(sorted(mods))+'\n').encode()).hexdigest()==ver['dependency_pins']['imported_module_names_sha256']
assert 'OWNERSHIP_PASS 437 PUBLIC 294' in text
assert not re.search(r': error(?:\(|:)',text)
print('PASS: exact 437 owners/axioms, 33 owner counts, 7365 module names and 294-public marker')
