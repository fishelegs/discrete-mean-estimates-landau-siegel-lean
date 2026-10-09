#!/usr/bin/env python3
"""Ordinary kernel replay of the end-to-end fixed-real-quadratic pi theorem.
All geometric/analytic/arithmetic conclusions and scalar margins are discharged.
"""
import argparse,fcntl,json,os,re,subprocess,time,shutil
from pathlib import Path
from audit_entry_bridge import ROOT,PIN,ALLOWED,sha
from audit_analysis_port import public_names,revalidate
from replay import code

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in ['verification-root','checkpoint-verification','geometry-verification','packet-verification','analysis-verification','out']:
        ap.add_argument('--'+n,required=True,type=Path)
    a=ap.parse_args();r=a.verification_root.resolve();cp=a.checkpoint_verification.resolve()
    geo=a.geometry_verification.resolve();packet=a.packet_verification.resolve();analysis=a.analysis_verification.resolve();out=a.out.resolve()
    for p in [r,cp,geo,packet,analysis,ROOT]:assert p!=out and p not in out.parents and out not in p.parents
    out.mkdir(parents=True,exist_ok=True)
    subprocess.run(['python3',str(ROOT/'scripts/audit_upstream.py'),'--verification-root',str(r),
        '--out',str(out/'upstream')],check=True)
    core=json.loads((cp/'replay-receipt.json').read_text());assert core['status']=='passed'
    for name,h in core['source_hashes'].items():assert sha(ROOT/name)==h
    for c in core['checks']:
        assert c['passed'] and sha(cp/'logs'/(c['module']+'.log'))==c['log_sha256']
        if not c['expected_failure']:assert sha(cp/'lib/lean'/Path(*c['module'].split('.')).with_suffix('.olean'))==c['olean_sha256']
    gr=json.loads((geo/'geometry-port-audit.json').read_text());pr=json.loads((packet/'packet-analysis-audit.json').read_text());ar=json.loads((analysis/'analysis-port-audit.json').read_text())
    revalidate(geo,gr,'logs');revalidate(packet,pr,'');revalidate(analysis,ar,'logs')
    assert gr['core_receipt_sha256']==pr['core_receipt_sha256']==ar['core_receipt_sha256']==sha(cp/'replay-receipt.json')
    assert ar['geometry_receipt_sha256']==sha(geo/'geometry-port-audit.json') and ar['packet_receipt_sha256']==sha(packet/'packet-analysis-audit.json')
    lib=out/'lib/lean';logs=out/'logs';logs.mkdir(exist_ok=True,parents=True)
    shutil.copytree(analysis/'lib/lean',lib,dirs_exist_ok=True)
    shutil.copytree(cp/'lib/lean',lib,dirs_exist_ok=True)
    lean=r/'elan/toolchains/leanprover--lean4---v4.34.1/bin/lean';assert sha(lean)==core['lean_sha256']
    env=os.environ.copy();env.update(LEAN_PATH=':'.join([str(lib),
        json.loads((r/'receipts/ordinary-build-plan.json').read_text())['LEAN_PATH']]),LEAN_NUM_THREADS='1')
    slots=Path('/tmp/mc6-lean-slots');slots.mkdir(exist_ok=True)
    lock=(slots/'8gib.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
    order=json.loads((ROOT/'scripts/parameter-order.json').read_text())
    work=['FixedQuadratic.ParameterPort.'+n for n in order]+['FixedQuadraticFixedFieldPi']+['checks.'+n for n in
      ['FinitenessRegression','FinitenessAudit','ExpectedFailureFinitenessMissingExponent','ExpectedFailureFinitenessWrongFieldDegree']]
    expected=public_names([ROOT/'FixedQuadratic/ParameterPort'/f'{n}.lean' for n in order]+[ROOT/'checks/FinitenessRegression.lean'])
    audit=code((ROOT/'checks/FinitenessAudit.lean').read_text())
    assert expected==set(re.findall(r'^#check @(.+)$',audit,re.M))==set(re.findall(r'^#print axioms (.+)$',audit,re.M))
    neg={'checks.ExpectedFailureFinitenessMissingExponent':['Type mismatch','2 < nu'],
         'checks.ExpectedFailureFinitenessWrongFieldDegree':['Application type mismatch','= 4','= 2']}
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
    output=(logs/'checks.FinitenessAudit.log').read_text()
    reports=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output,re.S))
    reports.update({x:'' for x in re.findall(r"'([^']+)' does not depend on any axioms",output)})
    assert set(reports)==expected,(set(reports)^expected);axioms={}
    for name,s in reports.items():
        used={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in s.split(',') if x.strip()}
        assert used<=ALLOWED,(name,used);axioms[name]=sorted(used)
    result=dict(status='passed',scope='End-to-end fixed real quadratic field finiteness for degree-exactly-two approximants at primitive integer minpoly maximum coefficient height, nu>2. No varying-field theorem, degree-exact lower exponent, BA/non-BA or K1--K3 claim.',
        theorem='FixedQuadratic.ParameterPort.fixed_real_quadratic_pi_finite_explicit',upstream_pin=PIN,
        core_receipt_sha256=sha(cp/'replay-receipt.json'),geometry_receipt_sha256=sha(geo/'geometry-port-audit.json'),
        packet_receipt_sha256=sha(packet/'packet-analysis-audit.json'),analysis_receipt_sha256=sha(analysis/'analysis-port-audit.json'),
        checks=checks,axiom_audit=axioms,ordinary_lean_only=True)
    (out/'finiteness-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS:',len(checks),'new compiler checks;',len(axioms),'actual type/axiom audits; end-to-end fixed-field theorem.')
if __name__=='__main__':main()
