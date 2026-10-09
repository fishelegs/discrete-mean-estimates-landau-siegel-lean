#!/usr/bin/env python3
"""Kernel-check the exact formal-entry bridge against the pinned upstream API."""
import argparse, fcntl, hashlib, json, os, re, subprocess
from pathlib import Path
from replay import code

ROOT=Path(__file__).resolve().parents[1]
PIN='adc7f1241b42e322a6451854ab7e4b4c146bf78a'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--verification-root',required=True,type=Path)
    ap.add_argument('--checkpoint-verification',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path)
    a=ap.parse_args();r=a.verification_root.resolve();cp=a.checkpoint_verification.resolve();out=a.out.resolve()
    for p in [r,cp,ROOT]:assert out!=p and p not in out.parents and out not in p.parents
    out.mkdir(parents=True,exist_ok=True)
    subprocess.run(['python3',str(ROOT/'scripts/audit_upstream.py'),
        '--verification-root',str(r),'--out',str(out/'upstream')],check=True)
    upstream=json.loads((out/'upstream/upstream-audit.json').read_text())
    assert upstream['status']=='passed' and upstream['upstream_pin']==PIN
    receipt=json.loads((cp/'replay-receipt.json').read_text())
    assert receipt['status']=='passed'
    for name,h in receipt['source_hashes'].items():assert sha(ROOT/name)==h,name
    for check in receipt['checks']:
        assert check['passed'] and sha(cp/'logs'/(check['module']+'.log'))==check['log_sha256']
        if not check['expected_failure']:
            dest=cp/'lib/lean'/Path(*check['module'].split('.')).with_suffix('.olean')
            assert sha(dest)==check['olean_sha256']
    lean=r/'elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
    assert sha(lean)==receipt['lean_sha256']
    source=ROOT/'checks/UpstreamFormalEntryBridge.lean'
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_cmd|initialize)\b',code(source.read_text()))
    env=os.environ.copy();env.update(LEAN_PATH=str(cp/'lib/lean')+':'+
        json.loads((r/'receipts/ordinary-build-plan.json').read_text())['LEAN_PATH'],LEAN_NUM_THREADS='1')
    slots=Path('/tmp/mc6-lean-slots');slots.mkdir(exist_ok=True)
    lock=(slots/'8gib.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
    dest=out/'UpstreamFormalEntryBridge.olean';log=out/'UpstreamFormalEntryBridge.log'
    argv=[str(lean),'-j1','-M8192','-DautoImplicit=false','-o',str(dest),str(source)]
    with log.open('wb') as f:proc=subprocess.run(argv,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
    assert proc.returncode==0 and dest.is_file(),log.read_text()
    reports=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log.read_text(),re.S))
    assert set(reports)=={'FixedQuadratic.UpstreamBridge.entry_specialization'}
    axioms={}
    for name,s in reports.items():
        used={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in s.split(',') if x.strip()}
        assert used<=ALLOWED,(name,used);axioms[name]=sorted(used)
    result=dict(status='passed',scope='Exact entry equality against pinned upstream; no pi finiteness theorem.',
        upstream_pin=PIN,prior_successful_checks_revalidated=upstream['prior_successful_checks_revalidated'],
        upstream_audit_sha256=sha(out/'upstream/upstream-audit.json'),
        checkpoint_receipt_sha256=sha(cp/'replay-receipt.json'),source_sha256=sha(source),
        argv=argv,exit_code=proc.returncode,olean_sha256=sha(dest),log_sha256=sha(log),axiom_audit=axioms)
    (out/'entry-bridge-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: exact pinned upstream entry bridge; one additional type/axiom audit.')

if __name__=='__main__':main()
