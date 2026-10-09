#!/usr/bin/env python3
"""Ordinary kernel replay of complete fixed-field analytic transfer and comparison.
Revalidates the passed core, geometry and arithmetic bridges; no hidden conclusions.
"""
import argparse,fcntl,json,os,re,subprocess,time,shutil
from pathlib import Path
from audit_entry_bridge import ROOT,PIN,ALLOWED,sha
from replay import code

def public_names(files):
    names=[]
    for f in files:
        stack=[]
        for line in code(f.read_text()).splitlines():
            line=re.sub(r'^@\[[^]]+\]\s*','',line.strip())
            m=re.match(r'namespace (\S+)',line)
            if m:stack.append(('namespace',m[1]));continue
            m=re.match(r'(?:noncomputable )?section(?:\s+(\S+))?$',line)
            if m:stack.append(('section',m[1]));continue
            m=re.match(r'end(?:\s+(\S+))?$',line)
            if m:
                kind,n=stack.pop();assert n==m[1],(f,n,m[1]);continue
            m=re.match(r'(?:noncomputable )?(?:theorem|lemma|def|abbrev|instance|structure) (\w+)',line)
            if m:names.append('.'.join([n for k,n in stack if k=='namespace']+[m[1]]))
        assert not stack,(f,stack)
    assert len(names)==len(set(names));return set(names)

def revalidate(v,receipt,logdir):
    assert receipt['status']=='passed' and receipt.get('upstream_pin',PIN)==PIN
    for check in receipt['checks']:
        n=check['module'];source=ROOT/Path(*n.split('.')).with_suffix('.lean')
        assert check['passed'] and sha(source)==check['source_sha256']
        log=v/logdir/(n+'.log' if logdir=='logs' else n.split('.')[-1]+'.log')
        assert sha(log)==check['log_sha256']
        dest=v/'lib/lean'/Path(*n.split('.')).with_suffix('.olean')
        if not check['expected_failure']:assert sha(dest)==check['olean_sha256']
        else:assert not dest.exists()
    for n,used in receipt['axiom_audit'].items():assert set(used)<=ALLOWED,(n,used)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in ['verification-root','checkpoint-verification','geometry-verification','packet-verification','out']:
        ap.add_argument('--'+n,required=True,type=Path)
    a=ap.parse_args();r=a.verification_root.resolve();cp=a.checkpoint_verification.resolve()
    geo=a.geometry_verification.resolve();packet=a.packet_verification.resolve();out=a.out.resolve()
    for p in [r,cp,geo,packet,ROOT]:assert p!=out and p not in out.parents and out not in p.parents
    out.mkdir(parents=True,exist_ok=True)
    subprocess.run(['python3',str(ROOT/'scripts/audit_upstream.py'),'--verification-root',str(r),
        '--out',str(out/'upstream')],check=True)
    core=json.loads((cp/'replay-receipt.json').read_text());assert core['status']=='passed'
    for name,h in core['source_hashes'].items():assert sha(ROOT/name)==h
    for c in core['checks']:
        assert c['passed'] and sha(cp/'logs'/(c['module']+'.log'))==c['log_sha256']
        if not c['expected_failure']:assert sha(cp/'lib/lean'/Path(*c['module'].split('.')).with_suffix('.olean'))==c['olean_sha256']
    gr=json.loads((geo/'geometry-port-audit.json').read_text());pr=json.loads((packet/'packet-analysis-audit.json').read_text())
    revalidate(geo,gr,'logs');revalidate(packet,pr,'')
    assert gr['core_receipt_sha256']==sha(cp/'replay-receipt.json')==pr['core_receipt_sha256']
    lib=out/'lib/lean';logs=out/'logs';logs.mkdir(exist_ok=True,parents=True)
    shutil.copytree(geo/'lib/lean',lib,dirs_exist_ok=True)
    shutil.copytree(packet/'lib/lean/checks',lib/'checks',dirs_exist_ok=True)
    lean=r/'elan/toolchains/leanprover--lean4---v4.34.1/bin/lean';assert sha(lean)==core['lean_sha256']
    env=os.environ.copy();env.update(LEAN_PATH=':'.join([str(lib),
        json.loads((r/'receipts/ordinary-build-plan.json').read_text())['LEAN_PATH']]),LEAN_NUM_THREADS='1')
    slots=Path('/tmp/mc6-lean-slots');slots.mkdir(exist_ok=True)
    lock=(slots/'8gib.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
    order=json.loads((ROOT/'scripts/analysis-order.json').read_text())
    work=['FixedQuadratic.AnalysisPort.'+n for n in order]+['checks.'+n for n in
      ['AnalysisAggregate','AnalysisRegression','AnalysisAudit','ExpectedFailureAnalysisMissingMargins','ExpectedFailureAnalysisConclusionField']]
    expected=public_names([ROOT/'FixedQuadratic/AnalysisPort'/f'{n}.lean' for n in order]+[ROOT/'checks/AnalysisRegression.lean'])
    expected.add('OAI.PiExponent.FixedFieldAnalyticData.mk')
    audit=code((ROOT/'checks/AnalysisAudit.lean').read_text())
    assert expected==set(re.findall(r'^#check @(.+)$',audit,re.M))==set(re.findall(r'^#print axioms (.+)$',audit,re.M))
    neg={'checks.ExpectedFailureAnalysisMissingMargins':['Type mismatch','False'],
         'checks.ExpectedFailureAnalysisConclusionField':['Unknown constant','FixedFieldAnalyticData.analytic_bound']}
    checks=[]
    for n in work:
        source=ROOT/Path(*n.split('.')).with_suffix('.lean');text=code(source.read_text())
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_cmd|initialize)\b',text),n
        dest=lib/Path(*n.split('.')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        log=logs/(n+'.log');negative=n in neg
        if dest.exists():dest.unlink()
        argv=[str(lean),'-j1','-M8192','-DautoImplicit=false','-o',str(dest),str(source)];start=time.monotonic()
        with log.open('wb') as f:proc=subprocess.run(argv,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
        output=log.read_text()
        passed=(proc.returncode!=0 and not dest.exists() and all(x in output for x in neg[n])) if negative else proc.returncode==0 and dest.is_file()
        assert passed,output
        c=dict(module=n,source_sha256=sha(source),log_sha256=sha(log),argv=argv,exit_code=proc.returncode,
            expected_failure=negative,passed=passed,elapsed_seconds=round(time.monotonic()-start,3))
        if not negative:c['olean_sha256']=sha(dest)
        checks.append(c);print(n,'PASS',flush=True)
    output=(logs/'checks.AnalysisAudit.log').read_text()
    reports=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output,re.S))
    reports.update({x:'' for x in re.findall(r"'([^']+)' does not depend on any axioms",output)})
    assert set(reports)==expected,(set(reports)^expected);axioms={}
    for name,s in reports.items():
        used={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in s.split(',') if x.strip()}
        assert used<=ALLOWED,(name,used);axioms[name]=sorted(used)
    data=code((ROOT/'FixedQuadratic/AnalysisPort/Data.lean').read_text()).split('namespace FixedFieldAnalyticData')[0]
    assert not re.search(r'\b(det|Surjective|analytic_bound|IsAmple|Tendsto)\b',data)
    result=dict(status='passed',scope='Complete literal analytic expansion, scalar transfer, collision, determinant summation, vanishing real-degree remainders, same-minor arithmetic and geometry connection. Explicit geometry/strict scalar margins still remain in no_geometric_packet; final exceptional-set finiteness is not proved.',
        upstream_pin=PIN,core_receipt_sha256=sha(cp/'replay-receipt.json'),
        geometry_receipt_sha256=sha(geo/'geometry-port-audit.json'),packet_receipt_sha256=sha(packet/'packet-analysis-audit.json'),
        checks=checks,axiom_audit=axioms,ordinary_lean_only=True)
    (out/'analysis-port-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS:',len(checks),'new compiler checks;',len(axioms),'actual type/axiom audits.')
if __name__=='__main__':main()
