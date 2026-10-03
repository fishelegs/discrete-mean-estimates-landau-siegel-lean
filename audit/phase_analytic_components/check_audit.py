"""Check a fresh CloudPhaseAnalyticAxioms log against the exact inventory."""
from pathlib import Path
import hashlib,json,re,sys
base=Path(__file__).resolve().parent
if len(sys.argv)!=2:raise SystemExit('Usage: python3 check_audit.py audit-log-path')
text=Path(sys.argv[1]).read_text()
ver=json.loads((base.parent/'cloud_phase_analytic_verification.json').read_text())
owned=json.loads((base/'OWNED_DECLARATIONS.json').read_text())['declarations']
expected={(x['owner'],x['declaration']):set(x['axioms']) for x in owned}
records=re.findall(r'^OWNER (\S+) DECL (\S+) AXIOMS #?\[([^\]]*)\]',text,re.M)
actual={(m,n):set(a.strip() for a in axs.split(',') if a.strip()) for m,n,axs in records}
assert len(records)==len(actual)==45 and actual==expected
assert {m:int(n) for m,n in re.findall(r'^OWNER_COUNT (\S+) (\d+)',text,re.M)}==ver['owner_counts']
mods=re.findall(r'^LOADED_MODULE (\S+)',text,re.M)
assert len(mods)==len(set(mods))==6877
assert hashlib.sha256(('\n'.join(sorted(mods))+'\n').encode()).hexdigest()==ver['dependency_pins']['imported_module_names_sha256']
assert 'OWNERSHIP_PASS 45 PUBLIC 29' in text
assert not re.search(r': error(?:\(|:)',text)
print('PASS: exact 45 owned/29 public, 2 owner counts, 6877 imported module names')
