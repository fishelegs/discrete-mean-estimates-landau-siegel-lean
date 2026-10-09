#!/usr/bin/env python3
"""Fresh ordinary Lean replay of the exact final-target import closure.
Only the pinned mathlib dependency artifacts may be reused. No old OAI/local
artifacts, receipt prerequisites, upstream Lake hooks, or source patching.
"""
import argparse
import json
import os
import re
import subprocess
import time
from pathlib import Path
from replay import ROOT, ALLOWED, code, sha
from audit_analysis_port import public_names

NEGATIVE = {
    'checks.ExpectedFailureFinitenessMissingExponent': ['Type mismatch', '2 < nu'],
    'checks.ExpectedFailureFinitenessWrongFieldDegree': ['Application type mismatch', '= 4', '= 2'],
}
FORBIDDEN = r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_cmd|initialize)\b'

def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()

def import_names(path):
    text = code(path.read_text())
    assert not re.search(FORBIDDEN, text), path
    return [n for line in re.findall(r'^(?:public )?import (.+)$', text, re.M) for n in line.split()]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ['lean', 'mathlib', 'packages-dir', 'upstream', 'out']:
        ap.add_argument('--' + name, required=True, type=Path)
    ap.add_argument('--plan-only', action='store_true')
    ap.add_argument('--memory-mb', type=int, default=8192)
    a = ap.parse_args()
    lean, mathlib, packages, upstream, out = [getattr(a, n).resolve() for n in ['lean', 'mathlib', 'packages_dir', 'upstream', 'out']]
    pins = json.loads((ROOT/'dependency-pins.json').read_text())
    manifest = json.loads((ROOT/'scripts/full-target-closure.json').read_text())
    assert manifest['upstream_pin'] == pins['upstream_math']
    assert git(upstream, 'rev-parse', 'HEAD') == pins['upstream_math']
    assert not git(upstream, 'status', '--porcelain'), 'upstream source must be clean'
    assert (ROOT/'lean-toolchain').read_text().strip() == pins['toolchain']
    declared = json.loads((ROOT/'lake-manifest.json').read_text())
    assert {p['name']: p['rev'] for p in declared['packages']} == {p['name']: p['rev'] for p in pins['packages']}
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    assert re.search(r'version 4\.34\.1(?:,|\))', version), version
    deps, libs = {}, []
    for item in pins['packages']:
        p = mathlib if item['name'] == 'mathlib' else packages/item['name']
        assert git(p, 'rev-parse', 'HEAD') == item['rev'], item
        assert not git(p, 'status', '--porcelain'), item
        lib = p/'.lake/build/lib/lean'
        if item['name'] == 'mathlib': assert lib.is_dir(), lib
        libs.append(lib)
        deps[item['name']] = dict(revision=item['rev'], source=str(p), artifact_policy='pinned mathlib official cache allowed')
    for protected in [ROOT, upstream, mathlib, packages]:
        assert protected != out and protected not in out.parents and out not in protected.parents
    sources, order, active = {}, [], set()
    def visit(name):
        if name in sources: return
        assert name not in active, ('import cycle', name)
        active.add(name)
        base = upstream/'lean' if name.startswith('OAI.') else ROOT
        assert name.startswith(('OAI.NumberTheory.PiExponent.', 'FixedQuadratic.', 'checks.')) or name in {'FixedQuadratic', 'FixedQuadraticFixedFieldPi'}, name
        p = base/Path(*name.split('.')).with_suffix('.lean')
        imports = import_names(p)
        ds = []
        for n in imports:
            if n.startswith(('Mathlib.', 'Lean.')) or n in {'Mathlib', 'Lean'}: continue
            visit(n); ds.append(n)
        sources[name] = dict(module=name, source_sha256=sha(p), dependencies=ds)
        order.append(name); active.remove(name)
    for n in manifest['targets']: visit(n)
    assert [sources[n] for n in order] == manifest['modules'], 'closure/source drift: regenerate and review manifest'
    param_order = json.loads((ROOT/'scripts/parameter-order.json').read_text())
    expected = public_names([ROOT/'FixedQuadratic/ParameterPort'/f'{n}.lean' for n in param_order] + [ROOT/'checks/FinitenessRegression.lean'])
    audit_source = code((ROOT/'checks/FinitenessAudit.lean').read_text())
    assert expected == set(re.findall(r'^#check @(.+)$', audit_source, re.M)) == set(re.findall(r'^#print axioms (.+)$', audit_source, re.M))
    summary = dict(total=len(order), upstream=sum(n.startswith('OAI.') for n in order), local=sum(not n.startswith('OAI.') for n in order), expected_failures=len(NEGATIVE))
    print('Validated fresh-target plan:', summary, flush=True)
    if a.plan_only: return
    # Refuse to mix any earlier build with this replay, even on a rerun.
    out.mkdir(parents=True, exist_ok=False)
    lib, logs = out/'lib/lean', out/'logs'
    lib.mkdir(parents=True); logs.mkdir()
    env = os.environ.copy()
    env.update(LEAN_PATH=':'.join(map(str, [lib] + libs)), LEAN_NUM_THREADS='1')
    checks = []
    result = dict(status='running', compiler=version, lean_sha256=sha(lean), upstream_pin=pins['upstream_math'], repository_head=git(ROOT, 'rev-parse', 'HEAD'), closure_manifest_sha256=sha(ROOT/'scripts/full-target-closure.json'), dependency_pins_sha256=sha(ROOT/'dependency-pins.json'), counts=summary, dependencies=deps, ordinary_lean_only=True, fresh_sources={'OAI': True, 'local': True}, reused_artifacts='Only official cache artifacts for the exact mathlib dependency pins; no OAI/local oleans or old verification receipts.', checks=checks)
    def save():
        (out/'full-target-receipt.json').write_text(json.dumps(result, indent=2)+'\n')
    save()
    for i, n in enumerate(order):
        base = upstream/'lean' if n.startswith('OAI.') else ROOT
        source = base/Path(*n.split('.')).with_suffix('.lean')
        dest = lib/Path(*n.split('.')).with_suffix('.olean')
        assert not dest.exists()
        dest.parent.mkdir(parents=True, exist_ok=True)
        log = logs/(n+'.log')
        argv = [str(lean), '-j1', '-M'+str(a.memory_mb), '-DautoImplicit=false', '-o', str(dest), str(source)]
        start = time.monotonic()
        with log.open('wb') as stream:
            proc = subprocess.run(argv, cwd=base, env=env, stdout=stream, stderr=subprocess.STDOUT)
        output = log.read_text(); negative = n in NEGATIVE
        passed = (proc.returncode != 0 and not dest.exists() and all(s in output for s in NEGATIVE[n])) if negative else (proc.returncode == 0 and dest.is_file())
        check = dict(module=n, source_sha256=sha(source), log_sha256=sha(log), argv=argv, exit_code=proc.returncode, expected_failure=negative, passed=passed, elapsed_seconds=round(time.monotonic()-start, 3))
        if dest.exists(): check['olean_sha256'] = sha(dest)
        checks.append(check)
        if not passed: result['status'] = 'failed'
        save(); print(f'{i+1}/{len(order)} {n}: '+('PASS' if passed else 'FAIL'), flush=True)
        if not passed: raise SystemExit(output)
    output = (logs/'checks.FinitenessAudit.log').read_text()
    reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S))
    reports.update({n: '' for n in re.findall(r"'([^']+)' does not depend on any axioms", output)})
    assert set(reports) == expected
    axioms = {}
    for name, body in reports.items():
        used = {re.sub(r'\.\{[^}]*\}', '', s.strip()) for s in body.split(',') if s.strip()}
        assert used <= ALLOWED, (name, used)
        axioms[name] = sorted(used)
    theorem = 'FixedQuadratic.ParameterPort.fixed_real_quadratic_pi_finite_explicit'
    actual_type = output.split('theorem '+theorem+' : ', 1)[1].split(' :=', 1)[0].strip()
    # Preserve the actual kernel-accepted statement, not a paraphrased interface.
    for token in ['IntermediateField', 'FiniteDimensional', 'Module.finrank', '2 nu', 'Set.Finite', 'minpoly', 'primitiveMinpolyHeight', 'Real.pi']:
        assert token in actual_type, (token, actual_type)
    result.update(status='passed', axiom_audit=axioms, theorem=theorem, actual_theorem_type=actual_type, scope='Fixed real quadratic field, degree-exactly-two elements, primitive integer minimal-polynomial maximum coefficient height, every nu>2. No varying-field or degree-exact lower-exponent claim.')
    save()
    print('PASS: fresh full target;', summary, ';', len(axioms), 'actual type/axiom audits.', flush=True)

if __name__ == '__main__': main()
