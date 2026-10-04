#!/usr/bin/env python3
"""Check published evidence and a full successful MC6ThreeBridgesInventory log.

This verifier performs no compilation and writes no files. Full types and raw Expr
renderings remain in the supplied private log; both SHA256s are checked for each
of the 242 declarations. Optional --repo-root checks all 19 applied input files.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import sys


def digest(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode('utf-8')).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('--repo-root', type=Path)
    args = parser.parse_args()
    evidence = Path(__file__).resolve().parent
    package = evidence.parent.parent
    receipt = json.loads((evidence / 'receipt.json').read_text())
    # This manifest is integrity evidence, not an independent signature.
    manifest_lines = (evidence / 'SHA256SUMS').read_text().splitlines()
    manifested = {line.split('  ', 1)[1] for line in manifest_lines}
    require(len(manifested) == len(manifest_lines), 'Duplicate manifest path')
    sources = json.loads((evidence / 'sources.json').read_text())
    declared_inputs = {row['source'] for row in sources}
    require(len(sources) == len(declared_inputs) == 19, 'Wrong declared input path set')
    declared_builds = json.loads((evidence / 'proof-builds.json').read_text())
    declared_audits = json.loads((evidence / 'regressions.json').read_text())
    required_inputs = {row['source'] for row in declared_builds + declared_audits}
    require(declared_inputs == required_inputs, 'Proof/regression input path set changed')
    evidence_names = {'README.md', 'export-manifest.json', 'owners.json',
                      'proof-builds.json', 'receipt.json', 'regressions.json',
                      'repository-loaded-modules.txt', 'reproduce.py',
                      'sources.json', 'verify_evidence.py'}
    evidence_names.update(receipt['declaration_files'])
    evidence_names.update(receipt['reference_files'])
    evidence_names.update(receipt['dependency_validation']['loaded_module_list'])
    expected_paths = declared_inputs | {'audit/MC6ThreeBridgesInventory.lean'} | {
        'audit/three_bridges/' + name for name in evidence_names}
    require(manifested == expected_paths, 'Declared package manifest path set changed')
    observed_evidence = {str(path.relative_to(evidence)) for path in evidence.rglob('*')
                         if path.is_file() and path != evidence / 'SHA256SUMS'}
    require(observed_evidence == evidence_names, 'Bounded evidence directory file set changed')
    for line in manifest_lines:
        expected, name = line.split('  ', 1)
        require(digest((package / name).read_bytes()) == expected, 'Package SHA256 changed: ' + name)
    rows = []
    for name in receipt['declaration_files']:
        rows.extend(json.loads((evidence / name).read_text()))
    expected = {row['name']: row for row in rows}
    require(len(rows) == len(expected) == 242, 'Expected exactly 242 unique declarations')
    text = args.log.read_text()
    require('error:' not in text, 'Lean error in supplied log')
    marker = 'OWNERSHIP_TYPE_AXIOM_PASS 242 PUBLIC 138'
    require(text.splitlines().count(marker) == 1, 'Missing or repeated successful audit marker')
    actual_rows = [json.loads(line.removeprefix('DECLARATION_JSON '))
                   for line in text.splitlines() if line.startswith('DECLARATION_JSON ')]
    actual = {row['name']: row for row in actual_rows}
    require(len(actual_rows) == len(actual) == 242, 'Wrong actual declaration count or duplicate name')
    require(set(actual) == set(expected), 'Exact declaration name set changed')
    references = {}
    for name in receipt['reference_files']:
        for row in json.loads((evidence / name).read_text()):
            require(row['name'] not in references, 'Duplicate reference entry')
            references[row['name']] = row['used_constants']
    require(set(references) == set(expected), 'Incomplete reference inventory')
    for name, row in expected.items():
        got = actual[name]
        require(got['owner'] == row['owner'], 'Defining module changed: ' + name)
        require(got['public'] == row['source_public'], 'Source classification changed: ' + name)
        require(digest(got['type_pretty']) == row['type_pretty_sha256'], 'Full pretty type SHA256 changed: ' + name)
        require(digest(got['type_repr']) == row['type_raw_expression_sha256'], 'Raw type Expr SHA256 changed: ' + name)
        require(got['type_lean_hash64'] == row['type_pretty_lean_hash64'], 'Lean type fingerprint changed: ' + name)
        require(got['universe_parameters_repr'] == row['universe_parameters_repr'], 'Universe parameters changed: ' + name)
        require(sorted(got['axioms']) == row['axioms'], 'Transitive axiom set changed: ' + name)
        require(set(got['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'Nonstandard axiom: ' + name)
        require('⋯' not in got['type_pretty'] and '...' not in got['type_pretty'], 'Truncated full type: ' + name)
        require(sorted(got['used_constants']) == references[name], 'Direct reference set changed: ' + name)
    owners = json.loads((evidence / 'owners.json').read_text())
    require(dict(collections.Counter(row['owner'] for row in actual_rows)) == owners['owners'], 'Owner counts changed')
    require(sum(row['public'] for row in actual_rows) == 138, 'Explicit source declaration count changed')
    modules = [line.removeprefix('LOADED_MODULE ') for line in text.splitlines() if line.startswith('LOADED_MODULE ')]
    pinned_modules = ''.join((evidence / name).read_text() for name in receipt['dependency_validation']['loaded_module_list']).splitlines()
    require(len(modules) == len(set(modules)) == 6175, 'Loaded module count or uniqueness changed')
    require(modules == pinned_modules, 'Exact ordered imported module union changed')
    require([m for m in modules if m.startswith('ZhangLS.')] == (evidence / 'repository-loaded-modules.txt').read_text().splitlines(), 'Repository dependency inventory changed')
    sources = json.loads((evidence / 'sources.json').read_text())
    require(len(sources) == 19, 'Input source count changed')
    for root in [package] + ([args.repo_root] if args.repo_root else []):
        for row in sources:
            data = (root / row['source']).read_bytes()
            require(len(data) == row['bytes'] and digest(data) == row['sha256'], 'Input source changed: ' + row['source'])
    regressions = json.loads((evidence / 'regressions.json').read_text())
    require(len(regressions) == 5 and sum(row['examples'] for row in regressions) == 37, 'Regression count changed')
    require(all(row['exit_code'] == 0 for row in regressions), 'Failed recorded regression')
    builds = json.loads((evidence / 'proof-builds.json').read_text())
    require(len(builds) == 14 and all(row['exit_code'] == 0 for row in builds), 'Failed or incomplete recorded proof builds')
    print('PASS: 242 exact owners/names/full pretty and raw type SHA256s/universes/axiom sets/direct references; 138 explicit + 104 generated; 6175 exact imports; 19 input source hashes; 14 recorded proof builds and 37 regressions in 5 audit files')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
