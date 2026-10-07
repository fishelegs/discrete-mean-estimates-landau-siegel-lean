#!/usr/bin/env python3
"""Replay this polynomial-family extension using an existing pinned Lean/mathlib cache.
No network, installation, Lake hook, or dependency build is invoked. Coordinate
exclusive compiler access before running; this script uses one -j1 -M4096 compiler.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean', required=True, type=Path)
p.add_argument('--existing-mathlib-project', required=True, type=Path)
p.add_argument('--out', required=True, type=Path, help='Private output directory, outside source/dependency trees')
a = p.parse_args()
lean, project, out = a.lean.resolve(), a.existing_mathlib_project.resolve(), a.out.resolve()
if out == project or project in out.parents or out == ROOT or ROOT in out.parents:
    p.error('--out must be outside the source and dependency trees')
if ROOT in out.parents or out in ROOT.parents or out in project.parents:
    p.error('--out must not contain source or dependency trees')
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
pins = json.loads((ROOT/'dependency-pins.json').read_text())
manifest = json.loads((project/'lake-manifest.json').read_text())
expected = {q['name']:q['rev'] for q in pins['packages']}
actual = {q['name']:q['rev'] for q in manifest['packages']}
for name, rev in expected.items():
    if actual.get(name) != rev: p.error(f'Wrong dependency pin: {name}')
if (project/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.1':
    p.error('Wrong project toolchain pin')
version = subprocess.check_output([str(lean), '--version'], text=True).strip()
if not re.search(r'version 4\.34\.1(?:,|\))', version): p.error(f'Wrong Lean executable: {version}')
source_hashes = json.loads((ROOT/'verification/family-reversal-source-hashes.json').read_text())
for rel, h in source_hashes.items():
    if sha(ROOT/rel) != h: p.error(f'Source hash mismatch: {rel}')
attestation = json.loads((ROOT/'verification/family-reversal-dependency-attestation.json').read_text())
imports = {}
for module, old in attestation['direct_imports'].items():
    rel = Path(*module.split('.'))
    source = project/'.lake/packages/mathlib'/rel.with_suffix('.lean')
    cached = project/'.lake/packages/mathlib/.lake/build/lib/lean'/rel.with_suffix('.olean')
    if not source.is_file() or sha(source) != old['source_sha256']:
        p.error(f'Dependency source mismatch: {module}')
    if not cached.is_file(): p.error(f'Missing cached dependency: {module}; no dependencies are built')
    imports[module] = {'source_sha256':sha(source), 'olean_sha256':sha(cached)}
libs = sorted((project/'.lake/packages').glob('*/.lake/build/lib/lean'))
if not libs: p.error('No precompiled package caches found')
for d in ['build','logs','home','cache']: (out/d).mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env.update(LEAN_PATH=':'.join(map(str,[out/'build']+libs)), LEAN_NUM_THREADS='1',
           LAKE_JOBS='1', HOME=str(out/'home'), XDG_CACHE_HOME=str(out/'cache'))
modules = [('PiFamilyReversal',False), ('PiFamilyReversalAudit',False),
           ('PiFamilyReversalRegression',False), ('ExpectedFailureFamilyAtTwo',True)]
checks = []
for name, fail in modules:
    source, output = ROOT/'src'/(name+'.lean'), out/'build'/(name+'.olean')
    if output.exists(): output.unlink()
    cmd = [str(lean),'-j1','-M4096','-DautoImplicit=false','-DwarningAsError=true',
           '-o',str(output),source.name]
    start = time.monotonic()
    run = subprocess.run(cmd,cwd=ROOT/'src',env=env,text=True,
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log = out/'logs'/(name+'.log'); log.write_text(run.stdout)
    passed = (run.returncode == 0 and output.exists()) if not fail else (
        run.returncode == 1 and run.stdout.count('error:') == 1 and
        'error: unsolved goals\n⊢ False' in run.stdout and not output.exists())
    check = dict(module=name,source_sha256=sha(source),exit_code=run.returncode,
                 expected_failure=fail,passed=passed,log_sha256=sha(log),
                 elapsed_seconds=round(time.monotonic()-start,3))
    if output.exists(): check['olean_sha256'] = sha(output)
    checks.append(check)
    print(f'{name}: {"PASS" if passed else "FAIL"}',flush=True)
    if not passed: print(run.stdout,file=sys.stderr); sys.exit(1)
main = (ROOT/'src/PiFamilyReversal.lean').read_text()
names = re.findall(r'^(?:theorem|lemma) (\w+)\b',main,re.M)
all_sources = '\n'.join((ROOT/'src'/(name+'.lean')).read_text() for name,_ in modules)
if len(names) != 14 or re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',all_sources):
    raise SystemExit('Unexpected declaration count or prohibited proof construct')
audit = (out/'logs/PiFamilyReversalAudit.log').read_text()
printed = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",audit,re.S))
if set(printed) != {'PiFamilyReversal.'+n for n in names}: raise SystemExit('Incomplete axiom audit')
axioms = {}
for name,body in printed.items():
    got = {re.sub(r'\.\{[^}]*\}','',v.strip()) for v in body.split(',')}
    if not got <= {'propext','Classical.choice','Quot.sound'}:
        raise SystemExit(f'Unexpected axioms for {name}: {got}')
    axioms[name] = sorted(got)
report = dict(status='passed',lean_version=version,lean_sha256=sha(lean),
              dependency_manifest_sha256=sha(project/'lake-manifest.json'),
              mathlib_revision=expected['mathlib'],direct_imports=imports,
              declaration_count=14,checks=checks,axiom_audit=axioms,
              exact_exponent_division=True,actual_pi_used=True,cutoff_N=3,
              determinant_identification_formalized=False,source_separation_formalized=False,
              N2_gain_formalized=False,normalized_limit_formalized=False,
              pi_bad_approximability_formalized=False)
(out/'family-reversal-replay-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print('All 14 declaration audits, positive regressions, and the N=2 excluded-precondition test passed.',flush=True)
