from pathlib import Path
import json,re,sys,hashlib
root=Path(__file__).resolve().parent;source=sys.argv[1];tag=sys.argv[2]
src=root/'project'/source;log=root/'logs/lean-checks'/(tag+'.log');receipt=json.loads((root/'logs/lean-checks'/(tag+'.receipt.json')).read_text())
assert receipt['exit_code']==0,receipt
assert receipt['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest(),'Source changed after compiler receipt'
allowed={'propext','Classical.choice','Quot.sound'}
s=log.read_text(); found=[]
for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",s,re.S):
 axioms=[re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in m[2].split(',') if a.strip()];found.append({'declaration':m[1],'axioms':axioms,'allowed_only':set(axioms)<=allowed})
for m in re.finditer(r"'([^']+)' does not depend on any axioms",s):found.append({'declaration':m[1],'axioms':[],'allowed_only':True})
expected=re.findall(r'^#print axioms\s+(\S+)',src.read_text(),re.M)
assert len(found)==len(expected),(len(found),len(expected))
unmatched=list(found)
for name in expected:
 matches=[x for x in unmatched if x['declaration']==name or x['declaration'].endswith('.'+name)]
 assert len(matches)==1, ('Missing or ambiguous axiom declaration',name,matches)
 unmatched.remove(matches[0])
assert not unmatched, ('Unexpected axiom declarations',unmatched)
assert all(x['allowed_only'] for x in found),found
result={'source':source,'log':str(log.relative_to(root)),'declarations':found,'expected_count':len(expected),'verified_count':len(found),'all_axioms_subset_standard_three':True,'source_sha256':receipt['source_sha256']}
(root/'logs/lean-checks'/(tag+'.axioms.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
