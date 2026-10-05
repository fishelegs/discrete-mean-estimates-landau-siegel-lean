"""Read-only finite reconstruction of the two-constraint arithmetic ledger."""
import json
checks=[]
for gap,want in [(118,(516,397)),(113,(495,381))]:
    pairs=[(a,b) for a in range(1,601) for b in range(1,601)
           if a-b>gap and 153*a<=50*(4*b-9)]
    assert pairs[0]==want
    checks.append({'gap':gap,'minimum':list(pairs[0]),'valid_pairs_checked':len(pairs)})
assert [x['valid_pairs_checked'] for x in checks]==[883,1370]
print(json.dumps({'status':'PASS','exact_constraint_checks':checks,
                  'scope':'Finite supplementary arithmetic only'},indent=2))
