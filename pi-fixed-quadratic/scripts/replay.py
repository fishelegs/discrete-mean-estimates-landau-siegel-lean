#!/usr/bin/env python3
"""Serial ordinary Lean verification against the exact 4.34.1/mathlib pins.
Does not run Lake hooks, install packages, or write to dependency checkouts.
"""
import argparse, fcntl, hashlib, json, os, re, subprocess, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = ['Resultant', 'Mahler', 'MinorBudget', 'Comparison', 'Conjugation',
           'Envelope', 'MultiEnvelope', 'Clearing', 'Height', 'Weights']
NEGATIVE = {
    'ExpectedFailureMissingConjugate': ('Type mismatch', '→'),
    'ExpectedFailureMissingCoefficient': ('Type mismatch', 'coefficientL1'),
    'ExpectedFailureCartesian': ('Type mismatch', 'x + -x'),
    'ExpectedFailureDegreeEquality': ('unsolved goals', '⊢ False'),
    'ExpectedFailurePiFiniteness': ('Unknown identifier', 'pi_fixed_field_finite'),
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def code(s):
    # Conservatively remove nested comments; executable tokens are audited.
    out, i, depth = [], 0, 0
    while i < len(s):
        if s[i:i+2] == '/-': depth += 1; i += 2
        elif depth and s[i:i+2] == '-/': depth -= 1; i += 2
        elif depth: i += 1
        elif s[i:i+2] == '--':
            e = s.find('\n', i); i = len(s) if e < 0 else e
        else: out.append(s[i]); i += 1
    assert depth == 0, 'unclosed comment'
    return ''.join(out)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', required=True, type=Path)
    ap.add_argument('--mathlib', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--packages-dir', type=Path)
    a = ap.parse_args()
    lean, mathlib, out = a.lean.resolve(), a.mathlib.resolve(), a.out.resolve()
    for protected in [ROOT, mathlib]:
        assert out != protected and protected not in out.parents and out not in protected.parents
    pins = json.loads((ROOT/'dependency-pins.json').read_text())
    version = subprocess.check_output([str(lean),'--version'], text=True).strip()
    assert re.search(r'version 4\.34\.1(?:,|\))', version), version
    assert (ROOT/'lean-toolchain').read_text().strip() == pins['toolchain']
    declared = json.loads((ROOT/'lake-manifest.json').read_text())
    assert {p['name']: p['rev'] for p in declared['packages']} == {p['name']:p['rev'] for p in pins['packages']}
    dependencies, libs = {}, []
    for item in pins['packages']:
        packages = a.packages_dir.resolve() if a.packages_dir else mathlib/'.lake/packages'
        p = mathlib if item['name']=='mathlib' else packages/item['name']
        head = subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
        assert head == item['rev'], (item['name'],head)
        assert not subprocess.check_output(['git','-C',str(p),'status','--porcelain'])
        libs.append(p/'.lake/build/lib/lean')
        dependencies[item['name']] = {'revision':head,'source':str(p)}
    sources = [ROOT/'FixedQuadratic'/f'{n}.lean' for n in MODULES]
    sources += [ROOT/'FixedQuadratic.lean',ROOT/'checks/Regression.lean',ROOT/'checks/Audit.lean']
    sources += [ROOT/'checks'/f'{n}.lean' for n in NEGATIVE]
    for p in sources:
        text = code(p.read_text())
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_cmd|initialize)\b',text), p
        for line in re.findall(r'^import (.+)$',text,re.M):
            for name in line.split():
                assert name.startswith(('Mathlib.', 'FixedQuadratic.', 'checks.')) or name=='FixedQuadratic', name
    names = []
    for p in sources[:len(MODULES)]:
        names.extend('FixedQuadratic.'+n for n in re.findall(r'^(?:noncomputable )?(?:theorem|def) (\w+)',code(p.read_text()),re.M))
    names.extend('FixedQuadratic.Regression.'+n for n in re.findall(r'^theorem (\w+)',code((ROOT/'checks/Regression.lean').read_text()),re.M))
    audit_source=(ROOT/'checks/Audit.lean').read_text()
    assert set(re.findall(r'^#print axioms (.+)$',audit_source,re.M))==set(names)
    out.mkdir(parents=True,exist_ok=True)
    build, logs = out/'lib/lean', out/'logs'
    build.mkdir(parents=True,exist_ok=True); logs.mkdir(exist_ok=True)
    env=os.environ.copy();env.update(LEAN_PATH=':'.join(map(str,[build]+libs)),LEAN_NUM_THREADS='1')
    lockdir=Path('/tmp/mc6-lean-slots');lockdir.mkdir(exist_ok=True)
    lock=(lockdir/'8gib.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
    checks=[]
    work=[('FixedQuadratic.'+n,False) for n in MODULES]
    work += [('FixedQuadratic',False),('checks.Regression',False),('checks.Audit',False)]
    work += [('checks.'+n,True) for n in NEGATIVE]
    for name, negative in work:
        source=ROOT/Path(*name.split('.')).with_suffix('.lean')
        dest=build/Path(*name.split('.')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        log=logs/(name+'.log')
        if dest.exists(): dest.unlink()
        argv=[str(lean),'-j1','-M8192','-DautoImplicit=false','-o',str(dest),str(source)]
        start=time.monotonic()
        with log.open('wb') as stream:
            proc=subprocess.run(argv,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        text=log.read_text()
        passed = (proc.returncode!=0 and not dest.exists() and all(x in text for x in NEGATIVE[name.split('.')[-1]])) if negative else (proc.returncode==0 and dest.is_file())
        rec=dict(module=name,argv=argv,source_sha256=sha(source),log_sha256=sha(log),exit_code=proc.returncode,expected_failure=negative,passed=passed,elapsed_seconds=round(time.monotonic()-start,3))
        if dest.exists(): rec['olean_sha256']=sha(dest)
        checks.append(rec);(out/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
        print(name, 'PASS' if passed else 'FAIL',flush=True)
        if not passed: print(text);raise SystemExit(1)
    audit=(logs/'checks.Audit.log').read_text()
    reports=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",audit,re.S))
    reports.update({n:'' for n in re.findall(r"'([^']+)' does not depend on any axioms",audit)})
    assert set(reports)==set(names), (set(names)-set(reports),set(reports)-set(names))
    axioms={}
    for name,body in reports.items():
        used={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in body.split(',') if x.strip()}
        assert used <= ALLOWED,(name,used)
        axioms[name]=sorted(used)
    direct={}
    for p in sources:
        for line in re.findall(r'^import (.+)$',p.read_text(),re.M):
            for name in line.split():
                if name.startswith('Mathlib.'):
                    f=mathlib/Path(*name.split('.')).with_suffix('.lean')
                    o=mathlib/'.lake/build/lib/lean'/Path(*name.split('.')).with_suffix('.olean')
                    direct[name]=dict(source_sha256=sha(f),olean_sha256=sha(o))
    result=dict(status='passed',scope='Partial arithmetic and determinant checkpoint. No fixed-field pi finiteness theorem.',lean_version=version,lean_sha256=sha(lean),dependencies=dependencies,direct_mathlib_imports=direct,checks=checks,axiom_audit=axioms,source_hashes={str(p.relative_to(ROOT)):sha(p) for p in sources},ordinary_lean_only=True)
    (out/'replay-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: {len(checks)} compiler checks, {len(axioms)} declaration audits.',flush=True)
if __name__=='__main__': main()
