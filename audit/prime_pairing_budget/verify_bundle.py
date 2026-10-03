#!/usr/bin/env python3
"""Verify curated mathematical evidence, dependency pins and exhaustive receipts.

Uses only Python's standard library. It does not write files or run a compiler.
Historical byte identities are records, not claims to reconstruct omitted files.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import math
import posixpath
import re
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def load(path):
    return json.loads(path.read_text(encoding='utf-8'))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe(base, relative):
    require(not PurePosixPath(relative).is_absolute(), 'Absolute public path: '+relative)
    path=(base/relative).resolve()
    require(path.is_relative_to(base), 'Path escapes its public root: '+relative)
    return path


def get(data, pointer):
    for key in pointer.split('/'):
        data=data[int(key)] if isinstance(data,list) else data[key]
    return data


def drop(data, pointer):
    parts=pointer.split('/')
    parent=get(data,'/'.join(parts[:-1])) if len(parts)>1 else data
    return parent.pop(parts[-1])


def compare(left, right, errors, prefix=''):
    """Literal recursive comparison except specifically named raw errors."""
    if prefix in errors:
        tol=errors[prefix]
        for val in (left,right):
            require(isinstance(val,(int,float)) and not isinstance(val,bool), 'Nonnumeric error: '+prefix)
            require(math.isfinite(val) and 0<=val<tol, 'Original numerical tolerance: '+prefix)
        return
    require(type(left) is type(right), 'Receipt type mismatch: '+prefix)
    if isinstance(left,dict):
        require(left.keys()==right.keys(), 'Receipt fields differ: '+prefix)
        for key in left:compare(left[key],right[key],errors,prefix+'/'+key if prefix else key)
    elif isinstance(left,list):
        require(len(left)==len(right), 'Receipt list length differs: '+prefix)
        for i,(a,b) in enumerate(zip(left,right)):compare(a,b,errors,prefix+'/'+str(i))
    else:
        require(left==right, 'Receipt value differs: '+prefix)


def strings(data):
    if isinstance(data,str):yield data
    elif isinstance(data,dict):
        for key,value in data.items():
            yield key
            yield from strings(value)
    elif isinstance(data,list):
        for value in data:yield from strings(value)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',required=True,type=Path,help='Checkout with the exact pinned public dependencies')
    args=parser.parse_args()
    repo=args.repo.resolve(); root=Path(__file__).resolve().parent
    manifest=load(root/'MANIFEST.json')
    require(manifest['status']=='source_only_independently_reviewed','Source-only manifest status')
    actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}
    listed={row['path'] for row in manifest['files']}
    require(len(listed)==len(manifest['files']) and actual==listed,'Incomplete or duplicate public inventory')
    for row in manifest['files']:
        p=safe(root,row['path'])
        require(sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],'Public bytes changed: '+row['path'])
    pins={row['path']:row['sha256'] for row in load(root/'SOURCE_HASHES.json')['repository_dependencies']}
    for path,digest in pins.items():require(sha(safe(repo,path))==digest,'Dependency bytes changed: '+path)

    histories=load(root/'SOURCE_HISTORY.json')['historical_sources']
    history={row['source_id']:row for row in histories}
    require(len(history)==len(histories),'Duplicate historical identifier')
    public_mappings=0
    for row in histories:
        require(re.fullmatch(r'[0-9a-f]{64}',row['original_sha256']) is not None,'Historical SHA256')
        require(row['original_bytes']>=0,'Historical byte count')
        if 'bundle_path' in row:
            require(sha(safe(root,row['bundle_path']))==row['curated_sha256'],'Curated equivalent changed')
            public_mappings+=1
        elif 'repository_path' in row:
            require(pins[row['repository_path']]==row['public_sha256'],'Unpinned public equivalent')
            if row['mapping']=='identical_bytes':
                require(row['original_sha256']==row['public_sha256'],'Identical byte mapping differs')
                require(safe(repo,row['repository_path']).stat().st_size==row['original_bytes'],'Identical byte size differs')
            else:
                carrier=row['historical_evidence_path']
                require(pins[carrier]==row['historical_evidence_sha256'],'Unpinned historical carrier')
                require(row['original_sha256'] in set(strings(load(safe(repo,carrier)))),'Historical identity missing from public carrier')
            public_mappings+=1
        else:
            require(row['mapping']=='historical_context_only' and row['role']=='nonmathematical_context_fingerprint','Unmapped mathematical input')
    manifest_counts={}
    for name in ('AUTHOR_SOURCE_MANIFEST.json','INDEPENDENT_SOURCE_MANIFEST.json'):
        record=load(root/name)
        carriers=[r for r in histories if r.get('bundle_path')==name]
        require(len(carriers)==1 and record['original_manifest_sha256']==carriers[0]['original_sha256'],'Historical manifest identity')
        require(record['original_manifest_bytes']==carriers[0]['original_bytes'],'Historical manifest byte count')
        count=0
        for field in ('files','inputs','artifacts'):
            for item in record.get(field,[]):
                source=history[item['source_id']]
                require(item['sha256']==source['original_sha256'],'Historical input identity')
                if 'bytes' in item:require(item['bytes']==source['original_bytes'],'Historical input byte count')
                count+=1
        manifest_counts[name]=count

    # All relative Markdown links are checked against this package or pinned files.
    link_count=0
    for doc in root.rglob('*.md'):
        prose=doc.read_text(encoding='utf-8')
        prose=re.sub(r'```.*?```','',prose,flags=re.S)
        prose=re.sub(r'`[^`\n]*`','',prose)
        for href in re.findall(r'\]\(([^)]+)\)',prose):
            if href.startswith(('https://','http://','#')):continue
            href=href.split('#',1)[0]
            logical=posixpath.normpath('audit/'+root.name+'/'+str(doc.parent.relative_to(root))+'/'+href)
            prefix='audit/'+root.name+'/'
            if logical.startswith(prefix):
                require(safe(root,logical[len(prefix):]).is_file(),'Missing local link: '+href)
            else:
                require(logical in pins,'Unpinned linked public file: '+logical)
                require(safe(repo,logical).is_file(),'Missing public link: '+logical)
            link_count+=1

    # Integrity metadata is checked here instead of in mathematical checkers.
    runs=load(root/'COMPARISON.json')['runs']
    outputs={}
    for run in runs:
        original=load(root/run['original']); saved=load(root/run['rerun'])
        fresh=json.loads(subprocess.check_output([sys.executable,'-I',str(safe(root,run['script']))],text=True))
        errors=dict(run.get('float_errors',{}))
        for pointer,tol in run.get('float_error_maps',{}).items():
            keys=get(original,pointer).keys()
            require(keys==get(saved,pointer).keys()==get(fresh,pointer).keys(),'Raw error map keys differ')
            for key in keys:errors[pointer+'/'+key]=tol
        for pointer,rule in run.get('integrity_fields',{}).items():
            val=get(original,pointer)
            if rule['operation']=='length':
                require(val==len(load(root/rule['manifest'])[rule['list']]),'Historical verified-entry count differs')
            elif rule['operation']=='author_identity':
                author=load(root/'AUTHOR_SOURCE_MANIFEST.json')
                require(val=={'manifest_sha256':author['original_manifest_sha256'],'matching_files':len(author['files'])},'Historical author identity differs')
            elif rule['operation']=='history_hash_map':
                for source_id,digest in val.items():require(history[source_id]['original_sha256']==digest,'Historical receipt source hash differs')
            else:raise AssertionError('Unknown integrity comparison')
            drop(original,pointer)
        for pointer in run.get('identity_fields',[]):
            # Explicit metadata only: the historical checker fingerprint is still checked.
            checker_sources=[r for r in histories if r.get('bundle_path')==run['script']]
            if pointer=='checker_sha256':
                require(len(checker_sources)==1 and get(original,pointer)==checker_sources[0]['original_sha256'],'Original checker fingerprint')
            elif pointer=='checker_path':
                require(len(checker_sources)==1 and get(original,pointer)=='historical:'+checker_sources[0]['source_id'],'Historical checker identifier')
            drop(original,pointer)
        compare(original,saved,errors)
        compare(saved,fresh,errors)
        outputs[run['script']]=fresh

    # The historical final review receipt is also checked, including its math totals.
    if (root/'INDEPENDENT_REVIEW_RECEIPT.json').exists():
        receipt=load(root/'INDEPENDENT_REVIEW_RECEIPT.json')
        review=load(root/'INDEPENDENT_SOURCE_MANIFEST.json')
        author=load(root/'AUTHOR_SOURCE_MANIFEST.json')
        algebra=outputs['algebra/check_algebra.py']
        require(receipt['status']=='PASS' and receipt['source_review_decision']=='ACCEPT','Review decision')
        require(receipt['manifest_sha256']==review['original_manifest_sha256'],'Final review manifest hash')
        require(receipt['matching_manifest_entries']==manifest_counts['INDEPENDENT_SOURCE_MANIFEST.json'],'Final review entry count')
        require(receipt['frozen_candidate_entries']==len(author['files']),'Final review input count')
        require(receipt['independent_rational_and_finite_status']==outputs['check_independent.py']['status'],'Final finite status')
        require(receipt['independent_algebra_assertions']==algebra['assertion_count'],'Final algebra assertion count')
        for value in (receipt['maximum_normalized_algebra_error'],max(algebra['maximum_normalized_errors'].values())):
            require(math.isfinite(value) and 0<=value<algebra['normalized_absolute_tolerance'],'Final algebra error tolerance')
    print(json.dumps({'status':'PASS','package':root.name,'curated_files_verified':len(listed),'repository_dependency_pins_verified':len(pins),'historical_sources_mapped':len(history),'public_equivalents_verified':public_mappings,'historical_manifest_entries':manifest_counts,'local_markdown_links_verified':link_count,'portable_mathematical_checkers_rerun':len(runs),'scope':'Source integrity, finite mathematical regressions and exact rational budgets; no Lean certification, actual signed strict-half bound, or exponent-2024 theorem.'},indent=2))


if __name__=='__main__':main()
