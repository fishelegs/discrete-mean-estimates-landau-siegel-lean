#!/usr/bin/env python3
"""Validate fresh central audit records. Does not compile or modify repository files."""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def require(test, message):
    if not test:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text())

def safe_join(root, relative):
    path = Path(relative)
    require(not path.is_absolute() and '..' not in path.parts, 'Expected relative path')
    result = (root / path).resolve()
    require(result.is_relative_to(root.resolve()), 'Path leaves specified root')
    return result

def parse_declarations(log, prefix):
    result = []
    for m in re.finditer(r'\b' + prefix + r'_DECL (\S+) (\S+) \[([^\]]*)\]', log):
        result.append({'module': m[1], 'name': m[2],
                       'axioms': sorted(a.strip() for a in m[3].split(',') if a.strip())})
    return result

def validate_declarations(records, expected, owners, label):
    expected_map = {(r['module'], r['name']): r for r in expected}
    actual_map = {(r['module'], r['name']): r for r in records}
    require(len(expected_map) == len(expected), label + ': duplicate expected name/owner')
    require(len(actual_map) == len(records), label + ': duplicate actual name/owner')
    require(len({r['name'] for r in records}) == len(records), label + ': duplicate name')
    missing = sorted(set(expected_map) - set(actual_map))
    extra = sorted(set(actual_map) - set(expected_map))
    require(not missing and not extra,
            f'{label}: inventory drift; missing={missing[:8]}, extra={extra[:8]}')
    actual_counts = collections.Counter(r['module'] for r in records)
    wanted_counts = collections.Counter(r['module'] for r in expected)
    require(set(actual_counts) == set(owners), label + ': missing or extra owner')
    require(actual_counts == wanted_counts, label + ': per-owner count mismatch')
    require(all(actual_counts[m] > 0 for m in owners), label + ': vacuous owner')
    for pair, row in actual_map.items():
        axs = set(row['axioms'])
        require(axs <= ALLOWED, label + ': unapproved axiom in ' + row['name'])
        require(axs == set(expected_map[pair]['frozen_axioms']),
                label + ': frozen axiom set changed in ' + row['name'])
    return actual_counts

def verify_run_record(path, repo, run_root, expected_driver, expected_hash):
    record = load(path)
    require(record.get('status') == 'passed' and record.get('exit_code') == 0,
            'Run record is not a successful compilation')
    require(record.get('source') == expected_driver, 'Unexpected driver source')
    before = record.get('source_sha256_before')
    after = record.get('source_sha256_after')
    require(before == after == expected_hash, 'Driver source hash changed or is unpinned')
    require(sha(safe_join(repo, expected_driver)) == expected_hash, 'Driver source bytes differ')
    obj = safe_join(run_root, record['olean'])
    log = safe_join(run_root, record['log'])
    require(obj.is_file() and obj.stat().st_size > 0, 'Missing or empty freshly produced object')
    require(sha(obj) == record['olean_sha256'], 'Driver object hash mismatch')
    require(sha(log) == record['log_sha256'], 'Driver log hash mismatch')
    text = log.read_text()
    require('error:' not in text and 'sorryAx' not in text, 'Audit log contains an error or sorryAx')
    return text

def validate_logs(public_log, owned_log, packet):
    public = load(packet / 'metadata/public_inventory.json')
    owned = load(packet / 'metadata/owned_inventory.json')
    owner_rows = load(packet / 'metadata/owner_counts.json')
    import_map = load(packet / 'metadata/import_map.json')
    own_by_name = {r['name']: r for r in owned}
    public = [{**r, 'frozen_axioms': own_by_name[r['name']]['frozen_axioms']} for r in public]
    owners = {r['module'] for r in owner_rows}
    require(len(public) == 412 and len(owned) == 689 and len(owners) == 65,
            'Expected inventory changed from frozen acceptance')
    require(public_log.count('CENTRAL_PUBLIC_AUDIT_PASS') == 1, 'Missing or duplicate public pass marker')
    require(owned_log.count('CENTRAL_OWNED_AUDIT_PASS') == 1, 'Missing or duplicate owned pass marker')
    public_actual = parse_declarations(public_log, 'PUBLIC')
    owned_actual = parse_declarations(owned_log, 'OWNED')
    pc = validate_declarations(public_actual, public, owners, 'public')
    declaration_owners = {r['module'] for r in owned}
    require(len(declaration_owners) == 67, 'Generated supplement owner drift')
    oc = validate_declarations(owned_actual, owned, declaration_owners, 'owned')
    for log, prefix, counter in [(public_log, 'PUBLIC', pc), (owned_log, 'OWNED', oc)]:
        rows = re.findall(r'\b' + prefix + r'_OWNER_COUNT (\S+) (\d+)', log)
        require(len(rows) == len(counter) and len(dict(rows)) == len(counter), prefix + ': incomplete owner totals')
        require({m: int(n) for m, n in rows} == dict(counter), prefix + ': incorrect owner totals')
    require(re.findall(r'\bPUBLIC_TOTAL (\d+) NEW (\d+) EXISTING (\d+) OWNERS (\d+)', public_log)
            == [('412', '278', '134', '65')], 'Public total/split drift')
    require(re.findall(r'\bOWNED_TOTAL (\d+) NEW (\d+) EXISTING (\d+) OWNERS (\d+)', owned_log)
            == [('689', '427', '262', '67')], 'Owned total/split drift')
    require(re.findall(r'\bOWNED_SCOPE (\d+) OWNERS (\d+) SUPPLEMENTS (\d+)', owned_log) == [('686','65','3')], 'Scoped/generated split drift')
    supplemental = load(packet / 'metadata/generated_equation_supplements.json')
    actual_supplemental = re.findall(r'\bGENERATED_SUPPLEMENT (\S+) (\S+)', owned_log)
    require(set(actual_supplemental) == {(r['module'],r['name']) for r in supplemental} and len(actual_supplemental) == 3, 'Generated supplement inventory drift')
    require(sum(r['module'] in owners for r in owned_actual) == 686, 'Scoped declaration coverage drift')
    require({m:oc[m] for m in owners} == {r['module']:r['owned'] for r in owner_rows}, 'Scoped owner count drift')
    new_owners = {r['module'] for r in owner_rows if r['installation'] == 'new'}
    require(len(new_owners) == 46 and len(owners - new_owners) == 19, 'Owner partition drift')
    require(sum(r['module'] in new_owners for r in public_actual) == 278, 'New public count drift')
    require(sum(r['module'] in new_owners for r in owned_actual) == 427, 'New owned count drift')
    # #print axioms must appear exactly once for every named public declaration.
    for row in public:
        pattern = (r"'" + re.escape(row['name']) +
                   r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
        hits = re.findall(pattern, public_log)
        require(len(hits) == 1, 'Missing or duplicate #print axioms result: ' + row['name'])
        axs = {a.strip() for a in hits[0].split(',') if a.strip()}
        require(axs == set(row['frozen_axioms']), '#print axioms drift: ' + row['name'])
    loaded = re.findall(r'\bLOADED_MODULE (\S+)', owned_log)
    require(len(loaded) == len(set(loaded)) == 6573, 'Loaded module count or uniqueness drift')
    loaded_hash = hashlib.sha256(('\n'.join(sorted(loaded)) + '\n').encode()).hexdigest()
    require(loaded_hash == import_map['module_names_sha256'], 'Closed imported module graph drift')
    require(not set(loaded) & set(import_map['flat_to_central']), 'Flat module leakage')
    refs = collections.defaultdict(set)
    for name, dep in re.findall(r'\bDECL_REF (\S+)\s+(\S+)', owned_log):
        refs[name].add(dep)
    def reaches(start, goal):
        stack = [start]
        seen = set()
        while stack:
            n = stack.pop()
            if n == goal:
                return True
            if n not in seen:
                seen.add(n)
                stack.extend(refs[n])
        return False
    chains = load(packet / 'metadata/source_chains.json')
    require(len(chains) == 17, 'Frozen source-chain scope changed')
    for start, goal in chains:
        require(reaches('ZhangLS.Spec.' + start, 'ZhangLS.Spec.' + goal),
                'Missing genuine source dependency: ' + start + ' -> ' + goal)
    return {'status': 'PASS_FRESH_CENTRAL_AUDITS', 'public': 412, 'owned': 689,
            'owners': 65, 'scoped_owned': 686, 'generated_supplements': 3, 'declaration_owners': 67, 'new_public': 278, 'existing_public': 134,
            'new_owned': 427, 'existing_owned': 262, 'loaded_modules': 6573,
            'source_chains': 17, 'axiom_union': sorted(ALLOWED)}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--run-root', type=Path, required=True)
    parser.add_argument('--public-record', type=Path, required=True)
    parser.add_argument('--owned-record', type=Path, required=True)
    args = parser.parse_args()
    packet = Path(__file__).resolve().parents[1]
    plan = load(packet / 'INSTALL_BUILD_PLAN.json')
    by_name = {Path(r['packet_path']).name: r for r in plan['audit_drivers']}
    logs = []
    for name, record in [('CloudLemma151CentralPublicAxioms.lean', args.public_record),
                         ('CloudLemma151CentralOwnedAxioms.lean', args.owned_record)]:
        driver = by_name[name]
        logs.append(verify_run_record(record, args.repo, args.run_root,
                    driver['repo_relative_destination'], driver['sha256']))
    print(json.dumps(validate_logs(logs[0], logs[1], packet), indent=2))

if __name__ == '__main__':
    main()
