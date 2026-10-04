#!/usr/bin/env python3
"""Read-only integrity and complete private-log verifier for the six uniform modules.

The bounded evidence directory is checked exactly. Other files in an installed
repository are allowed. SHA256SUMS is integrity evidence, not a signature.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import sys

SUFFIXES = ['Geometry', 'Envelopes', 'Substitution', 'Assembly', 'Budget', 'LittleO']
MODULES = ['ZhangLS.Spec.ActualGramUniform' + suffix for suffix in SUFFIXES]
SOURCE_PATHS = {module.replace('.', '/') + '.lean' for module in MODULES}
EVIDENCE_NAMES = {'README.md', 'declarations-01.json', 'declarations-02.json',
                  'owners.json', 'proof-builds.json', 'receipt.json', 'sources.json',
                  'verify_evidence.py', 'reproduce_audit.py'}
INVENTORY_PATH = 'audit/ActualGramUniformInventory.lean'


def digest(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode('utf-8')).hexdigest()


def canonical(value):
    return json.dumps(value, ensure_ascii=False, separators=(',', ':'))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate_package(repo_root=None):
    evidence = Path(__file__).resolve().parent
    package = evidence.parent.parent
    all_entries = list(evidence.rglob('*'))
    require(not any(path.is_symlink() for path in all_entries), 'Symlink in bounded evidence directory')
    observed = {path.relative_to(evidence).as_posix() for path in all_entries if path.is_file()}
    require(observed == EVIDENCE_NAMES | {'SHA256SUMS'}, 'Bounded evidence directory file set changed')
    lines = (evidence / 'SHA256SUMS').read_text(encoding='utf-8').splitlines()
    manifest = {}
    for line in lines:
        match = re.fullmatch(r'([0-9a-f]{64})  ([^\r\n]+)', line)
        require(match is not None, 'Malformed manifest line')
        value, name = match.groups()
        require(name not in manifest, 'Duplicate manifest path')
        manifest[name] = value
    expected_paths = SOURCE_PATHS | {INVENTORY_PATH} | {'audit/gram_uniform/' + name for name in EVIDENCE_NAMES}
    require(set(manifest) == expected_paths, 'Declared package manifest path set changed')
    for name, value in manifest.items():
        data = (package / name).read_bytes()
        require(len(data) <= 150000, 'Public file exceeds 150 KB: ' + name)
        data.decode('utf-8')
        require(digest(data) == value, 'Package SHA256 changed: ' + name)
    load = lambda name: json.loads((evidence / name).read_text(encoding='utf-8'))
    receipt = load('receipt.json')
    require(receipt['status'] == 'passed' and receipt['lean_version'] == '4.30.0', 'Receipt status/toolchain changed')
    require(receipt['owned_declarations'] == 133 and receipt['source_public_declarations'] == 38 and receipt['generated_declarations'] == 95, 'Receipt counts changed')
    require(receipt['declaration_files'] == ['declarations-01.json', 'declarations-02.json'], 'Declaration file set changed')
    require(receipt['inventory_source'] == INVENTORY_PATH, 'Inventory path changed')
    require(receipt['inventory_source_sha256'] == manifest[INVENTORY_PATH], 'Inventory source hash mismatch')
    require(receipt['inventory_run']['exit_code'] == 0, 'Recorded inventory did not pass')
    sources = load('sources.json')
    require(len(sources) == 6 and {row['source'] for row in sources} == SOURCE_PATHS, 'Wrong source path set')
    require([row['module'] for row in sources] == MODULES, 'Source module order changed')
    for root in [package] + ([Path(repo_root).resolve()] if repo_root is not None else []):
        for row in sources:
            data = (root / row['source']).read_bytes()
            require(len(data) == row['bytes'] and digest(data) == row['sha256'], 'Source changed: ' + row['source'])
            original, count = re.subn(rb'(?m)^import ZhangLS\.Spec\.(ActualGramUniform\w+)\r?$', rb'import \1', data)
            require(count == row['qualified_import_count'], 'Import qualification count changed: ' + row['source'])
            require(digest(original) == row['frozen_original_sha256'], 'Import-only frozen source mapping failed: ' + row['source'])
    builds = load('proof-builds.json')
    require(len(builds) == 6 and [row['module'] for row in builds] == MODULES, 'Recorded proof build set/order changed')
    for build, source in zip(builds, sources):
        require(build['exit_code'] == 0 and build['source'] == source['source'] and build['source_sha256'] == source['sha256'], 'Build/source mismatch')
        require(build['lean_flags'] == ['-j1', '-M6144'], 'Recorded build resource flags changed')
    rows = [row for name in receipt['declaration_files'] for row in load(name)]
    require(len(rows) == 133 and len({row['name'] for row in rows}) == 133, 'Wrong or duplicate expected declaration set')
    require({row['owner'] for row in rows} == set(MODULES), 'Wrong expected owner set')
    owners = load('owners.json')
    require(dict(collections.Counter(row['owner'] for row in rows)) == owners['owners'], 'Expected owner counts mismatch')
    require(sum(row['source_public'] for row in rows) == 38, 'Expected explicit count mismatch')
    return receipt, rows, owners


def validate_log(log_path, receipt, rows, owners):
    text = Path(log_path).read_text(encoding='utf-8')
    lines = text.splitlines()
    require('error:' not in text, 'Lean error in supplied log')
    require(lines.count('OWNERSHIP_TYPE_AXIOM_PASS 133 PUBLIC 38') == 1, 'Missing or repeated successful audit marker')
    actual_rows = [json.loads(line.removeprefix('DECLARATION_JSON ')) for line in lines if line.startswith('DECLARATION_JSON ')]
    actual = {row['name']: row for row in actual_rows}
    expected = {row['name']: row for row in rows}
    require(len(actual_rows) == len(actual) == 133 and set(actual) == set(expected), 'Exact declaration name set changed')
    allowed = {'Classical.choice', 'Quot.sound', 'propext'}
    for name, row in expected.items():
        got = actual[name]
        require(got['owner'] == row['owner'], 'Defining module changed: ' + name)
        require(type(got['public']) is bool and got['public'] == row['source_public'], 'Source classification changed: ' + name)
        require(digest(got['type_pretty']) == row['type_pretty_sha256'], 'Full pretty type SHA256 changed: ' + name)
        require(digest(got['type_repr']) == row['type_raw_expression_sha256'], 'Full raw type Expr SHA256 changed: ' + name)
        require(got['type_lean_hash64'] == row['type_pretty_lean_hash64'], 'Lean type fingerprint changed: ' + name)
        require(got['universe_parameters_repr'] == row['universe_parameters_repr'], 'Universe parameters changed: ' + name)
        require(sorted(got['axioms']) == row['axioms'] and set(got['axioms']) <= allowed, 'Transitive axiom set changed: ' + name)
        for field in ['type_pretty', 'type_repr']:
            require('⋯' not in got[field] and '...' not in got[field], 'Truncated full type: ' + name)
        references = sorted(got['used_constants'])
        require(len(references) == len(set(references)) == row['direct_reference_count'], 'Direct reference count changed: ' + name)
        require(digest(canonical(references)) == row['direct_references_sha256'], 'Direct reference SHA256 changed: ' + name)
    require(dict(collections.Counter(row['owner'] for row in actual_rows)) == owners['owners'], 'Actual owner counts changed')
    require(dict(collections.Counter(row['owner'] for row in actual_rows if row['public'])) == owners['explicit_by_owner'], 'Actual explicit owner counts changed')
    printed_owners = [line.split(' ', 2)[1:] for line in lines if line.startswith('OWNER_COUNT ')]
    require(len(printed_owners) == 6 and {name: int(count) for name, count in printed_owners} == owners['owners'], 'Printed owner counts changed')
    modules = [line.removeprefix('LOADED_MODULE ') for line in lines if line.startswith('LOADED_MODULE ')]
    dependency = receipt['dependency_validation']
    require(len(modules) == len(set(modules)) == dependency['ordered_loaded_module_count'] == 6969, 'Loaded module count changed')
    require(digest('\n'.join(modules) + '\n') == dependency['ordered_loaded_modules_sha256'], 'Exact ordered loaded module union changed')
    repository = [module for module in modules if module.startswith('ZhangLS.')]
    require(len(repository) == dependency['repository_module_count'] == 867, 'Repository module count changed')
    require(digest('\n'.join(repository) + '\n') == dependency['ordered_repository_modules_sha256'], 'Exact repository import union changed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('--repo-root', type=Path)
    args = parser.parse_args()
    validate_log(args.log, *validate_package(args.repo_root))
    print('PASS: 133 exact owners/names/full pretty and raw type SHA256s/universes/axiom sets/direct-reference hashes; 38 explicit + 95 generated; 6969 exact imports; six import-only source mappings and six successful recorded central builds')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, UnicodeError, json.JSONDecodeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
