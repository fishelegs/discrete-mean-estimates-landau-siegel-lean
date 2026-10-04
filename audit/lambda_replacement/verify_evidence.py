#!/usr/bin/env python3
"""Read-only, bounded verifier for the lambda-replacement evidence and a full audit log.
Accepts either this standalone package or the same files installed in a larger checkout.
No whole-repository traversal, compilation, network, or writes are performed.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import sys

EVIDENCE_FILES = {'README.md', 'INDEPENDENT_SCOPE_REVIEW.md', 'export-manifest.json',
    'outer-export-manifest.json', 'sources.json', 'prerequisites.json', 'declarations.json', 'dependency-sources.json',
    'repository-loaded-modules.txt', 'builds.json', 'receipt.json',
    'verify_evidence.py', 'reproduce.py'}


def sha(value):
    return hashlib.sha256(value if isinstance(value, bytes) else value.encode('utf-8')).hexdigest()


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
    read = lambda name: json.loads((evidence / name).read_text())
    sources, prerequisites = read('sources.json'), read('prerequisites.json')
    receipt, builds = read('receipt.json'), read('builds.json')
    require(len(sources) == 5 and len(prerequisites) == 2, 'Input counts changed')
    declared_sources = {r['source'] for r in sources}
    expected_sources = {'ZhangLS/Spec/FixedHLambdaReplacementLocal.lean',
        'ZhangLS/Spec/FixedHLambdaReplacement.lean', 'audit/FixedHLambdaReplacementRegression.lean',
        'ZhangLS/Spec/FixedHLambdaReplacementOuter.lean', 'audit/FixedHLambdaReplacementOuterRegression.lean'}
    require(declared_sources == expected_sources, 'Exact source set changed')
    require({r['source'] for r in prerequisites} == {
        'ZhangLS/Spec/AppendixBRoughPrimeLog.lean', 'ZhangLS/Spec/Lemma83FiniteShiftLambda.lean'},
        'Exact prerequisite set changed')
    required = declared_sources | {'audit/FixedHLambdaReplacementInventory.lean'} | {
        'audit/lambda_replacement/' + n for n in EVIDENCE_FILES}
    manifest = [line.split('  ', 1) for line in (evidence / 'SHA256SUMS').read_text().splitlines()]
    require(len(manifest) == len(required), 'Manifest entry count changed')
    require({name for _, name in manifest} == required, 'Exact bounded package file set changed')
    require({p.name for p in evidence.iterdir()} == EVIDENCE_FILES | {'SHA256SUMS'},
        'Unexpected file in bounded evidence directory')
    for expected, name in manifest:
        data = (package / name).read_bytes()
        require(len(data) <= 150000, 'Public file exceeds 150KB: ' + name)
        data.decode('utf-8')
        require(sha(data) == expected, 'Package checksum mismatch: ' + name)
    for root in [package] + ([args.repo_root] if args.repo_root else []):
        for row in sources:
            data = (root / row['source']).read_bytes()
            require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'Input source mismatch: ' + row['source'])
    exported = read('export-manifest.json')
    outer_export = read('outer-export-manifest.json')
    require(outer_export['commit'] == receipt['source_commit_from_export'] and outer_export['parent'] == exported['commit'] == receipt['product_commit_from_export'] and exported['base'] == receipt['source_base_from_export'], 'Export provenance drift')
    require({x['path']: x['sha256'] for x in exported['files'] + outer_export['files']} == {x['source']: x['sha256'] for x in sources}, 'Export byte identities differ')
    expected_rows = read('declarations.json')
    expected = {r['name']: r for r in expected_rows}
    require(len(expected_rows) == len(expected) == 68, 'Expected declaration set changed')
    log = args.log.read_text()
    require('error:' not in log, 'Lean error in supplied log')
    require(log.splitlines().count('OWNERSHIP_TYPE_AXIOM_PASS 68 PUBLIC 34') == 1, 'Missing or repeated successful marker')
    actual_rows = [json.loads(line.removeprefix('DECLARATION_JSON ')) for line in log.splitlines() if line.startswith('DECLARATION_JSON ')]
    actual = {r['name']: r for r in actual_rows}
    require(len(actual_rows) == len(actual) == 68 and set(actual) == set(expected), 'Exact declaration names changed')
    for name, want in expected.items():
        got = actual[name]
        require(got['owner'] == want['owner'], 'Defining module changed: ' + name)
        require(got['public'] == want['source_public'], 'Explicit/generated classification changed: ' + name)
        require(sha(got['type_pretty']) == want['type_pretty_sha256'], 'Full pretty type SHA256 changed: ' + name)
        require(sha(got['type_repr']) == want['type_raw_expression_sha256'], 'Raw type expression SHA256 changed: ' + name)
        require(got['type_lean_hash64'] == want['type_pretty_lean_hash64'], 'Lean type fingerprint changed: ' + name)
        require(got['universe_parameters_repr'] == want['universe_parameters_repr'], 'Universe parameters changed: ' + name)
        require(sorted(got['axioms']) == want['axioms'], 'Exact transitive axiom set changed: ' + name)
        require(set(got['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'Nonstandard axiom: ' + name)
        require('⋯' not in got['type_pretty'] and '...' not in got['type_pretty'], 'Truncated type: ' + name)
        refs = json.dumps(sorted(got['used_constants']), ensure_ascii=False, separators=(',', ':'))
        require(sha(refs) == want['used_constants_sha256'], 'Direct-reference SHA256 changed: ' + name)
    require(dict(collections.Counter(r['owner'] for r in actual_rows)) == receipt['owners'], 'Owner counts changed')
    require(sum(r['public'] for r in actual_rows) == 34, 'Explicit declaration count changed')
    require(sum(r['public'] for r in actual_rows if r['owner'].startswith('ZhangLS.')) == 22, 'Proof explicit count changed')
    modules = [l.removeprefix('LOADED_MODULE ') for l in log.splitlines() if l.startswith('LOADED_MODULE ')]
    require(len(modules) == len(set(modules)) == receipt['loaded_module_count'] == 6053, 'Loaded module count changed')
    require(sha('\n'.join(modules) + '\n') == receipt['loaded_module_list_sha256'], 'Ordered imported module union changed')
    repo_modules = [m for m in modules if m.startswith('ZhangLS.')]
    require(repo_modules == (evidence / 'repository-loaded-modules.txt').read_text().splitlines(), 'Repository dependency list changed')
    dependencies = read('dependency-sources.json')
    require(len(dependencies) == 286 and [r['module'] for r in dependencies] == repo_modules, 'Dependency source map changed')
    require(sum(r['validation'] == 'readonly baseline source matched' for r in dependencies) == 281, 'Baseline validation count changed')
    if args.repo_root:
        for row in dependencies + prerequisites:
            data = (args.repo_root / row['source']).read_bytes()
            require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'Dependency source mismatch: ' + row['source'])
    require(len(builds) == 7 and all(r['exit_code'] == 0 and r['threads'] == 1 and r['memory_mib'] == 4096 for r in builds), 'Build receipt failure')
    require(collections.Counter(r['kind'] for r in builds) == {'proof': 3, 'prerequisite': 2, 'regression': 2}, 'Build scope changed')
    require(receipt['inventory_build']['exit_code'] == 0 and receipt['regression_lemmas'] == 12, 'Audit receipt failure')
    require(sha((package / 'audit/FixedHLambdaReplacementInventory.lean').read_bytes()) == receipt['inventory_source_sha256'], 'Inventory source drift')
    print('PASS: 68 exact owners/names/full pretty and raw type SHA256s/universes/axiom sets/reference hashes; 22 proof declarations + 31 generated, 12 regressions + 3 generated; 6053 ordered imports; 286 repository dependency source hashes; 3 fresh proofs, 2 prerequisite builds, 12 regressions')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
