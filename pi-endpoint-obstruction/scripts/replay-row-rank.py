#!/usr/bin/env python3
"""Replay the finite weighted-row extension against an existing pinned mathlib cache.
No Lake hooks, installs, network operations, or dependency builds are invoked.
Coordinate compiler use externally before running this serial script.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lean', required=True, type=Path, help='Existing Lean 4.34.1 executable')
parser.add_argument('--existing-mathlib-project', required=True, type=Path,
                    help='Existing project with the pinned lake-manifest.json and populated .lake/packages caches')
parser.add_argument('--out', type=Path, default=ROOT/'.replay')
args = parser.parse_args()
lean = args.lean.resolve()
project = args.existing_mathlib_project.resolve()
out = args.out.resolve()
if out == project or project in out.parents:
    parser.error('--out must not be inside the read-only dependency project')
if out == ROOT or out == ROOT/'src' or ROOT/'src' in out.parents:
    parser.error('--out must not overwrite source files')

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

pins = json.loads((ROOT/'dependency-pins.json').read_text())
actual = json.loads((project/'lake-manifest.json').read_text())
expected_revs = {p['name']:p['rev'] for p in pins['packages']}
actual_revs = {p['name']:p['rev'] for p in actual['packages']}
for name, rev in expected_revs.items():
    if actual_revs.get(name) != rev:
        parser.error(f'dependency pin mismatch: {name}')
if (project/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.1':
    parser.error('dependency project has the wrong Lean toolchain pin')
source_hashes = json.loads((ROOT/'verification/row-rank-source-hashes.json').read_text())
for rel, expected in source_hashes.items():
    if sha(ROOT/rel) != expected:
        parser.error(f'source hash mismatch: {rel}')
version = subprocess.check_output([str(lean),'--version'],text=True).strip()
if not re.search(r'version 4\.34\.1(?:,|\))', version):
    parser.error(f'wrong executable version: {version}')
libs = sorted((project/'.lake/packages').glob('*/.lake/build/lib/lean'))
if not libs:
    parser.error('no precompiled package caches found')
for module in ['Mathlib.Basic.Real.Basic', 'Mathlib.Algebra.Order.BigOperators.Group.Finset',
               'Mathlib.LinearAlgebra.Matrix.Determinant.Basic', 'Mathlib.Tactic.NormDet',
               'Mathlib.Tactic.Ring', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic',
               'Mathlib.Tactic.FinCases']:
    dep = project/'.lake/packages/mathlib/.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
    if not dep.is_file():
        parser.error(f'missing cached dependency: {module}; this script never builds dependencies')
for child in ['build','logs','home','cache']:
    (out/child).mkdir(parents=True,exist_ok=True)
env = os.environ.copy()
env.update(LEAN_PATH=':'.join(map(str,[out/'build']+libs)), LEAN_NUM_THREADS='1',
           LAKE_JOBS='1', HOME=str(out/'home'), XDG_CACHE_HOME=str(out/'cache'))
checks = []
modules = [
    ('PiRowRank',None),
    ('PiQualityFreeExample',None),
    ('PiRowRankAudit',None),
    ('PiRowRankRegression',None),
    ('ExpectedFailureWeakDecrease','⊢ False'),
    ('ExpectedFailureMissingMovement','⊢ False'),
    ('ExpectedFailureZeroCenter','⊢ False'),
]
for name, signature in modules:
    source = ROOT/'src'/(name+'.lean')
    output = out/'build'/(name+'.olean')
    if output.exists(): output.unlink()
    cmd = [str(lean),'-j1','-M4096','-DautoImplicit=false','-DwarningAsError=true',
           '-o',str(output),source.name]
    start = time.monotonic()
    run = subprocess.run(cmd,cwd=ROOT/'src',env=env,text=True,
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log = out/'logs'/(name+'.log')
    log.write_text(run.stdout)
    passed = (run.returncode == 0 and output.exists()) if signature is None else (
        run.returncode == 1 and 'error:' in run.stdout and signature in run.stdout and not output.exists())
    check = dict(module=name,source_sha256=sha(source),exit_code=run.returncode,
                 expected_failure=signature is not None,passed=passed,
                 elapsed_seconds=round(time.monotonic()-start,3),log_sha256=sha(log))
    if output.exists(): check['olean_sha256']=sha(output)
    checks.append(check)
    print(f'{name}: {"PASS" if passed else "FAIL"}',flush=True)
    if not passed:
        print(run.stdout,file=sys.stderr)
        sys.exit(1)
source = '\n'.join((ROOT/'src'/name).read_text() for name in
    ['PiRowRank.lean','PiQualityFreeExample.lean'])
names = re.findall(r'^theorem (\w+)\b',source,re.M)
all_extension_sources = '\n'.join((ROOT/'src'/(name+'.lean')).read_text() for name,_ in modules)
if len(names) != 8 or re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',all_extension_sources):
    raise SystemExit('Unexpected theorem count or prohibited proof construct')
audit = (out/'logs/PiRowRankAudit.log').read_text()
printed = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",audit,re.S))
if set(printed) != {'PiRowRank.'+n for n in names}:
    raise SystemExit('Incomplete theorem axiom audit')
axioms = {}
for name,body in printed.items():
    got = {re.sub(r'\.\{[^}]*\}','',v.strip()) for v in body.split(',')}
    if not got <= {'propext','Classical.choice','Quot.sound'}:
        raise SystemExit(f'Unexpected axioms for {name}: {got}')
    axioms[name]=sorted(got)
report = dict(status='passed',source_attachment_formalized=False,
              actual_period_example_formalized=True,main_theorem_count=8,lean_version=version,mathlib_revision=expected_revs['mathlib'],
              checks=checks,axiom_audit=axioms)
(out/'row-rank-replay-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print('All 8 main theorem audits, positive regressions, and three expected failures passed.',flush=True)
