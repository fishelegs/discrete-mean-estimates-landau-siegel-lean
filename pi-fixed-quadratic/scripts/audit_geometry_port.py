#!/usr/bin/env python3
"""Replay the geometry-only extraction and actual fixed-field minor existence.
Uses the exact, hash-revalidated upstream closure and core arithmetic replay.
"""
import argparse,fcntl,json,os,re,subprocess,time,shutil
from pathlib import Path
from audit_entry_bridge import ROOT,PIN,ALLOWED,sha
from replay import code

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--verification-root',required=True,type=Path)
    ap.add_argument('--checkpoint-verification',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path)
    a=ap.parse_args();r=a.verification_root.resolve();cp=a.checkpoint_verification.resolve();out=a.out.resolve()
    for p in [r,cp,ROOT]:assert p!=out and p not in out.parents and out not in p.parents
    out.mkdir(parents=True,exist_ok=True)
    subprocess.run(['python3',str(ROOT/'scripts/audit_entry_bridge.py'),
        '--verification-root',str(r),'--checkpoint-verification',str(cp),'--out',str(out/'entry')],check=True)
    entry=json.loads((out/'entry/entry-bridge-audit.json').read_text());assert entry['status']=='passed'
    lib=out/'lib/lean';lib.mkdir(parents=True,exist_ok=True);logs=out/'logs';logs.mkdir(exist_ok=True)
    # Lean resolves a module root from the first path containing that root.
    # Copy the already hash-validated core closure beside the new geometry root.
    shutil.copytree(cp/'lib/lean/FixedQuadratic',lib/'FixedQuadratic',dirs_exist_ok=True)
    lean=r/'elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
    env=os.environ.copy();env.update(LEAN_PATH=':'.join([str(lib),str(cp/'lib/lean'),
        json.loads((r/'receipts/ordinary-build-plan.json').read_text())['LEAN_PATH']]),LEAN_NUM_THREADS='1')
    slots=Path('/tmp/mc6-lean-slots');slots.mkdir(exist_ok=True)
    lock=(slots/'8gib.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
    order=json.loads((ROOT/'scripts/geometry-order.json').read_text())
    provenance=json.loads((ROOT/'FixedQuadratic/GeometryPort/provenance.json').read_text())
    assert provenance['upstream_pin']==PIN
    for item in provenance['ported_wrappers']:
        assert sha(r/'source'/item['upstream'])==item['upstream_sha256']
        assert sha(ROOT/item['ported'])==item['ported_sha256']
    work=['FixedQuadratic.GeometryPort.'+n for n in order]
    work+=['checks.'+n for n in ['GeometryAggregate','GeometryRegression','GeometryAudit',
        'ExpectedFailureGeometryTail','ExpectedFailureGeometryConclusionField']]
    neg={'checks.ExpectedFailureGeometryTail':['unsolved goals','⊢ False'],
         'checks.ExpectedFailureGeometryConclusionField':['Unknown constant','FixedFieldGeometryData.jet_surjective']}
    checks=[]
    for n in work:
        source=ROOT/Path(*n.split('.')).with_suffix('.lean');text=code(source.read_text())
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_cmd|initialize)\b',text),n
        for imp in re.findall(r'^import (.+)$',text,re.M):
            assert all(x.startswith(('FixedQuadratic.','checks.','OAI.NumberTheory.PiExponent.')) for x in imp.split())
        dest=lib/Path(*n.split('.')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        log=logs/(n+'.log');negative=n in neg
        if dest.exists():dest.unlink()
        argv=[str(lean),'-j1','-M8192','-DautoImplicit=false','-o',str(dest),str(source)]
        start=time.monotonic()
        with log.open('wb') as stream:proc=subprocess.run(argv,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        output=log.read_text()
        passed=(proc.returncode!=0 and not dest.exists() and all(x in output for x in neg[n])) if negative else proc.returncode==0 and dest.is_file()
        assert passed,output
        check=dict(module=n,source_sha256=sha(source),log_sha256=sha(log),argv=argv,
            exit_code=proc.returncode,expected_failure=negative,passed=passed,elapsed_seconds=round(time.monotonic()-start,3))
        if not negative:check['olean_sha256']=sha(dest)
        checks.append(check);print(n,'PASS',flush=True)
    audit=code((ROOT/'checks/GeometryAudit.lean').read_text())
    names=set(re.findall(r'^#check @(.+)$',audit,re.M))
    assert names==set(re.findall(r'^#print axioms (.+)$',audit,re.M))
    output=(logs/'checks.GeometryAudit.log').read_text()
    reports=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output,re.S))
    reports.update({x:'' for x in re.findall(r"'([^']+)' does not depend on any axioms",output)})
    assert set(reports)==names,(set(reports)^names)
    axioms={}
    for name,s in reports.items():
        used={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in s.split(',') if x.strip()}
        assert used<=ALLOWED,(name,used);axioms[name]=sorted(used)
    # The exact record is also printed in the audit log. No geometric conclusion is a field.
    data=code((ROOT/'FixedQuadratic/GeometryPort/Data.lean').read_text()).split('namespace FixedFieldGeometryData')[0]
    assert not re.search(r'\b(IsAmple|Surjective|det|jet_surjective)\b',data)
    result=dict(status='passed',scope='Proved geometry/compactification/blowup/ampleness/jet-surjectivity and cofinal actual nonzero minors for explicit geometric inputs. Not final pi finiteness; exceptional-set parameter selection and complete analytic determinant comparison remain.',
        upstream_pin=PIN,entry_audit_sha256=sha(out/'entry/entry-bridge-audit.json'),
        core_receipt_sha256=sha(cp/'replay-receipt.json'),checks=checks,axiom_audit=axioms,ordinary_lean_only=True)
    (out/'geometry-port-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS:',len(checks),'new compiler checks;',len(axioms),'actual type/axiom audits.')
if __name__=='__main__':main()
