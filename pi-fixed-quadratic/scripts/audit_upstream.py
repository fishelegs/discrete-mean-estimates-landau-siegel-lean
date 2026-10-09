#!/usr/bin/env python3
"""Revalidate prior PiExponent receipts and print the actual upstream interfaces.
This reuses the audited compiled closure, rather than rebuilding 869 modules.
"""
import argparse, fcntl, hashlib, json, os, re, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PIN='adc7f1241b42e322a6451854ab7e4b4c146bf78a'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--verification-root',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path)
    a=ap.parse_args();r=a.verification_root.resolve();out=a.out.resolve()
    assert r not in out.parents and ROOT not in out.parents
    out.mkdir(parents=True,exist_ok=True)
    old=json.loads((r/'receipts/ordinary-verification-result.json').read_text())
    trusted=json.loads((r/'receipts/trusted-statement-result.json').read_text())
    final=json.loads((r/'receipts/final-result.json').read_text())
    assert old['status']=='ordinary_lean_checks_passed' and old['source_revision']==PIN
    assert final['status']=='ordinary_lean_main_trusted_type_and_axiom_checks_passed'
    assert trusted['literal_statement_matches_challenge']
    assert subprocess.check_output(['git','-C',str(r/'source'),'rev-parse','HEAD'],text=True).strip()==PIN
    validated=[]
    for x in old['checks']+trusted['checks']:
        assert x['exit_code']==0
        assert sha(x['argv'][-1])==x['source_sha256'], x['module']
        assert sha(x['log'])==x['log_sha256'], x['module']
        dest=x['argv'][x['argv'].index('-o')+1]
        assert sha(dest)==x['olean_sha256'], x['module']
        validated.append(x['module'])
    lean=r/'elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
    assert sha(lean)==old['lean_sha256']
    env=os.environ.copy();env.update(LEAN_PATH=json.loads((r/'receipts/ordinary-build-plan.json').read_text())['LEAN_PATH'],LEAN_NUM_THREADS='1')
    lockdir=Path('/tmp/mc6-lean-slots');lockdir.mkdir(exist_ok=True)
    lock=(lockdir/'8gib.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
    source=ROOT/'checks/UpstreamAudit.lean';dest=out/'UpstreamAudit.olean';log=out/'UpstreamAudit.log'
    argv=[str(lean),'-j1','-M8192','-DautoImplicit=false','-o',str(dest),str(source)]
    start=time.monotonic()
    with log.open('wb') as f:proc=subprocess.run(argv,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
    assert proc.returncode==0,log.read_text()
    reports=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log.read_text(),re.S))
    assert len(reports)==6
    axioms={}
    for n,s in reports.items():
        used={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in s.split(',') if x.strip()}
        assert used<=ALLOWED,(n,used);axioms[n]=sorted(used)
    result=dict(status='passed',upstream_pin=PIN,prior_successful_checks_revalidated=len(validated),new_compiler_invocations=1,
        scope='Reused prior ordinary Lean closure with all source, output and log hashes checked; exact upstream API and six axiom audits freshly printed. Not a fixed-field theorem.',
        previous_receipt_hashes={str(p.relative_to(r)):sha(p) for p in [r/'receipts/ordinary-verification-result.json',r/'receipts/trusted-statement-result.json',r/'receipts/final-result.json']},
        source_sha256=sha(source),argv=argv,exit_code=proc.returncode,olean_sha256=sha(dest),log_sha256=sha(log),axiom_audit=axioms,elapsed_seconds=round(time.monotonic()-start,3))
    (out/'upstream-audit.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS: prior',len(validated),'checks revalidated; six upstream axiom reports.')
if __name__=='__main__':main()
