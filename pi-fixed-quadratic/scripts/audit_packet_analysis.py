#!/usr/bin/env python3
"""Ordinary Lean replay of actual packet arithmetic and fixed-field row scalars.
Reuses the exact pinned upstream closure and the fully replayed core checkpoint.
"""
import argparse,fcntl,json,os,re,subprocess
from pathlib import Path
from audit_entry_bridge import ROOT, PIN, ALLOWED, sha
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
    lib=out/'lib/lean';(lib/'checks').mkdir(parents=True,exist_ok=True)
    (lib/'checks/UpstreamFormalEntryBridge.olean').write_bytes((out/'entry/UpstreamFormalEntryBridge.olean').read_bytes())
    lean=r/'elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
    env=os.environ.copy();env.update(LEAN_PATH=':'.join([str(lib),str(cp/'lib/lean'),
        json.loads((r/'receipts/ordinary-build-plan.json').read_text())['LEAN_PATH']]),LEAN_NUM_THREADS='1')
    slots=Path('/tmp/mc6-lean-slots');slots.mkdir(exist_ok=True)
    lock=(slots/'8gib.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
    modules=['UpstreamPacketArithmetic','UpstreamAnalysisBridge','ExpectedFailureCeilingCost']
    names={};checks=[];axioms={}
    for n in modules:
        source=ROOT/'checks'/f'{n}.lean';text=code(source.read_text())
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_cmd|initialize)\b',text),n
        for imp in re.findall(r'^import (.+)$',text,re.M):
            assert all(x.startswith(('FixedQuadratic.','checks.','OAI.NumberTheory.PiExponent.')) for x in imp.split())
        negative=n.startswith('ExpectedFailure')
        dest=lib/'checks'/f'{n}.olean';log=out/f'{n}.log'
        if dest.exists():dest.unlink()
        argv=[str(lean),'-j1','-M8192','-DautoImplicit=false','-o',str(dest),str(source)]
        with log.open('wb') as stream:proc=subprocess.run(argv,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        output=log.read_text()
        passed=(proc.returncode!=0 and not dest.exists() and all(x in output for x in ['Type mismatch','Real.exp'])) if negative else proc.returncode==0 and dest.is_file()
        assert passed,output
        check=dict(module='checks.'+n,source_sha256=sha(source),log_sha256=sha(log),argv=argv,
            exit_code=proc.returncode,expected_failure=negative,passed=passed)
        if not negative:
            check['olean_sha256']=sha(dest)
            ns='FixedQuadratic.'+('UpstreamPacketArithmetic' if n=='UpstreamPacketArithmetic' else 'UpstreamAnalysis')
            expected={ns+'.'+x for x in re.findall(r'^(?:noncomputable )?(?:theorem|def) (\w+)',text,re.M)}
            reports=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output,re.S))
            reports.update({x:'' for x in re.findall(r"'([^']+)' does not depend on any axioms",output)})
            assert set(reports)==expected,(set(reports),expected)
            assert set(re.findall(r'^#check @(.+)$',text,re.M))==expected
            for name,s in reports.items():
                used={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in s.split(',') if x.strip()}
                assert used<=ALLOWED,(name,used)
                axioms[name]=sorted(used)
        checks.append(check);print(n,'PASS',flush=True)
    result=dict(status='passed',scope='Actual packet arithmetic/counts and row scalar transfer. No global interpolation, analytic aggregate or pi finiteness theorem.',
        upstream_pin=PIN,entry_audit_sha256=sha(out/'entry/entry-bridge-audit.json'),
        core_receipt_sha256=sha(cp/'replay-receipt.json'),checks=checks,axiom_audit=axioms,ordinary_lean_only=True)
    (out/'packet-analysis-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS:',len(checks),'new compiler checks;',len(axioms),'actual type/axiom audits.')
if __name__=='__main__':main()
