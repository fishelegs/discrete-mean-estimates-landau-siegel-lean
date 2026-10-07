#!/usr/bin/env python3
"""Replay the prescribed-point gap using an existing pinned Lean/mathlib cache.
No network, installation, Lake hook, or dependency build is invoked. Coordinate
exclusive compiler access before running; compilation is sequential, -j1 -M4096.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean', required=True, type=Path)
p.add_argument('--existing-mathlib-project', required=True, type=Path)
p.add_argument('--out', required=True, type=Path, help='Fresh private output directory outside source/dependency trees')
a = p.parse_args()
lean, project, out = a.lean.resolve(), a.existing_mathlib_project.resolve(), a.out.resolve()
for protected in (ROOT, project, lean.parent.parent):
    if out == protected or protected in out.parents or out in protected.parents:
        p.error('--out must be outside and must not contain source/dependency/toolchain trees')
if out.exists() and any(out.iterdir()): p.error('--out must be absent or empty')
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
pins = json.loads((ROOT/'verification/normal-family-gap-dependency-pins.json').read_text())
repository_pins = ROOT/'dependency-pins.json'
if repository_pins.exists() and json.loads(repository_pins.read_text()) != pins:
    p.error('Existing repository dependency pins differ from this additive stage')
manifest = json.loads((project/'lake-manifest.json').read_text())
expected = {q['name']:q['rev'] for q in pins['packages']}
actual = {q['name']:q['rev'] for q in manifest['packages']}
if actual != expected: p.error('Dependency package set or revisions do not match')
if (project/'lean-toolchain').read_text().strip() != pins['toolchain']:
    p.error('Wrong project toolchain pin')
version = subprocess.check_output([str(lean), '--version'], text=True).strip()
if not re.search(r'version 4\.34\.1(?:,|\))', version): p.error(f'Wrong Lean executable: {version}')
source_hashes = json.loads((ROOT/'verification/normal-family-gap-source-hashes.json').read_text())
for rel, h in source_hashes.items():
    if sha(ROOT/rel) != h: p.error(f'Source hash mismatch: {rel}')
attestation = json.loads((ROOT/'verification/normal-family-gap-dependency-attestation.json').read_text())
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
env.update(LEAN_PATH=os.pathsep.join(map(str,[out/'build']+libs)), LEAN_NUM_THREADS='1',
           LAKE_JOBS='1', HOME=str(out/'home'), XDG_CACHE_HOME=str(out/'cache'))
modules = [('NormalFamilyPointwiseGap',False), ('NormalFamilyPointwiseGapAudit',False),
           ('NormalFamilyPointwiseGapRegression',False), ('ExpectedFailureUniformPointwiseBound',True)]
checks = []
for name, fail in modules:
    source, output = ROOT/'src'/(name+'.lean'), out/'build'/(name+'.olean')
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
main = (ROOT/'src/NormalFamilyPointwiseGap.lean').read_text()
names = re.findall(r'^(?:theorem|lemma) (\w+)\b',main,re.M)
all_sources = '\n'.join((ROOT/'src'/(name+'.lean')).read_text() for name,_ in modules)
if len(names) != 15 or re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',all_sources):
    raise SystemExit('Unexpected declaration count or prohibited proof construct')
audit = (out/'logs/NormalFamilyPointwiseGapAudit.log').read_text()
printed = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",audit,re.S))
if set(printed) != {'NormalFamilyPointwiseGap.'+n for n in names}:
    raise SystemExit('Incomplete axiom audit')
axioms = {}
for name,body in printed.items():
    got = {re.sub(r'\.\{[^}]*\}','',v.strip()) for v in body.split(',') if v.strip()}
    if not got <= {'propext','Classical.choice','Quot.sound'}:
        raise SystemExit(f'Unexpected axioms for {name}: {got}')
    axioms[name] = sorted(got)
for rel, h in source_hashes.items():
    if sha(ROOT/rel) != h: raise SystemExit(f'Source changed during replay: {rel}')
report = dict(status='passed',lean_version=version,lean_sha256=sha(lean),
              dependency_manifest_sha256=sha(project/'lake-manifest.json'),
              existing_repository_dependency_pins_sha256=(sha(repository_pins) if repository_pins.exists() else None),
              mathlib_revision=expected['mathlib'],direct_imports=imports,
              declaration_count=15,checks=checks,axiom_audit=axioms,
              actual_complex_polynomials=True,all_nonconstant_coefficient_bounds=True,
              entire_analyticity=True,uniform_fixed_disk_bound=True,target='3/4',
              exact_target_values=True,individual_target_nonvanishing=True,
              target_convergence_to_zero=True,no_uniform_positive_pointwise_bound=True,
              determinant_identification_formalized=False,
              interval_supremum_lemma_disproved=False,
              pi_bad_approximability_formalized=False,
              dependencies_rebuilt=False,complete_transitive_cache_reaudited=False)
(out/'normal-family-gap-replay-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print('All 15 declaration audits, positive regressions, and the rejected uniform-bound strengthening passed.',flush=True)
