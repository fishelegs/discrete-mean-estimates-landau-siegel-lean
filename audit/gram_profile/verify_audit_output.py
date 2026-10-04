#!/usr/bin/env python3
"""Verify every published declaration/type SHA and the exact imported module union.

Run from any directory with a successful log produced by CloudGramProfileInventory.lean.
Optionally pass --repo-root to verify all sixteen source SHA256s as well.
This verifier performs no compilation and writes no files.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def digest(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('--repo-root', type=Path)
    args = parser.parse_args()
    evidence = Path(__file__).resolve().parent
    expected = json.loads((evidence / 'declarations.json').read_text())
    text = args.log.read_text()
    require('error:' not in text, 'Lean error in supplied log')
    marker = 'OWNERSHIP_TYPE_AXIOM_PASS 154 PUBLIC 92 FULL_TYPE_FINGERPRINTS 154'
    require(text.splitlines().count(marker) == 1, 'Missing or repeated successful audit marker')
    rows = [json.loads(line.removeprefix('DECLARATION_JSON '))
            for line in text.splitlines() if line.startswith('DECLARATION_JSON ')]
    require(len(rows) == 154, 'Expected exactly 154 declaration rows')
    found = {row['name']: row for row in rows}
    require(len(found) == 154, 'Duplicate declaration name')
    require(set(found) == {row['name'] for row in expected}, 'Exact declaration-name set changed')
    for row in expected:
        actual = found[row['name']]
        name = row['name']
        require(actual['owner'] == row['owner'], 'Owner changed: ' + name)
        require(actual['public'] == row['source_public'], 'Public classification changed: ' + name)
        require(digest(actual['type_pretty']) == row['type_pretty_sha256'], 'Full type rendering SHA256 changed: ' + name)
        require(digest(actual['type_repr']) == row['type_raw_expression_sha256'], 'Raw type expression SHA256 changed: ' + name)
        require(actual['type_lean_hash64'] == row['type_pretty_lean_hash64'], 'Lean type fingerprint changed: ' + name)
        require(actual['universe_parameters_repr'] == row['universe_parameters_repr'], 'Universe parameters changed: ' + name)
        require(sorted(actual['axioms']) == row['axioms'], 'Transitive axiom set changed: ' + name)
        require(set(actual['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'Nonstandard axiom: ' + name)
        require('⋯' not in actual['type_pretty'] and '...' not in actual['type_pretty'], 'Truncated type: ' + name)
    modules = [line.removeprefix('LOADED_MODULE ') for line in text.splitlines()
               if line.startswith('LOADED_MODULE ')]
    receipt = json.loads((evidence / 'receipt.json').read_text())
    expected_modules = ''.join((evidence / name).read_text() for name in receipt['dependency_validation']['loaded_module_list']).splitlines()
    require(len(modules) == len(set(modules)) == 6964, 'Loaded module count or uniqueness changed')
    require(modules == expected_modules, 'Exact ordered imported-module union changed')
    public = sum(row['public'] for row in rows)
    require(public == 92, 'Source-public count changed')
    if args.repo_root:
        for source in json.loads((evidence / 'sources.json').read_text()):
            data = (args.repo_root / source['source']).read_bytes()
            require(hashlib.sha256(data).hexdigest() == source['source_sha256'],
                    'Source SHA256 changed: ' + source['module'])
    print('PASS: 154 exact owners/names/full type SHA256s/universe lists/axiom sets; 92 public; 6964 exact loaded modules' +
          ('; 16 source SHA256s' if args.repo_root else ''))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
