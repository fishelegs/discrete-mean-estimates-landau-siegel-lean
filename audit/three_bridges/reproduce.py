#!/usr/bin/env python3
"""Rebuild the 14 MC6 modules and five audits, then check the pinned inventory.

Requires an existing Lean 4.30.0 checkout and its already available dependency
objects. Never calls lake, downloads dependencies, or writes into the checkout.
All objects, full logs and run receipts are written to --work-dir. Every Lean
process acquires the caller-supplied shared --lock-file. Pass the same shared lock
used by other proof workers; it is released between files.
"""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo-root', required=True, type=Path)
    p.add_argument('--work-dir', required=True, type=Path)
    p.add_argument('--lean', required=True, type=Path)
    p.add_argument('--base-lean-path', required=True)
    p.add_argument('--lock-file', required=True, type=Path)
    a = p.parse_args()
    evidence = Path(__file__).resolve().parent
    package = evidence.parent.parent
    root = a.repo_root.resolve()
    work = a.work_dir.resolve()
    if work == root or root in work.parents or work == package or package in work.parents:
        raise ValueError('Use a private work directory outside the repository and public package')
    for row in json.loads((evidence / 'sources.json').read_text()):
        data = (root / row['source']).read_bytes()
        if hashlib.sha256(data).hexdigest() != row['sha256']:
            raise ValueError('Repository source mismatch: ' + row['source'])
    work.mkdir(parents=True, exist_ok=True)
    objects = work / 'objects'
    objects.mkdir(exist_ok=True)
    builds = json.loads((evidence / 'proof-builds.json').read_text())
    reserved_stems = {row['source'].removesuffix('.lean') for row in builds}
    project_prefixes = {row['module'].split('.')[0] for row in builds}

    def reserved(relative):
        name = relative.as_posix()
        return any(name == stem or name.startswith(stem + '.') for stem in reserved_stems)

    # Lean selects a project prefix from the first search-path root containing
    # it. Populate that root with read-only links for unchanged dependencies,
    # preserving base-path precedence and reserving every fresh output suffix.
    for base_name in a.base_lean_path.split(os.pathsep):
        base = Path(base_name).resolve()
        for prefix in sorted(project_prefixes):
            source_tree = base / prefix
            if not source_tree.is_dir():
                continue
            for source in source_tree.rglob('*'):
                if not source.is_file():
                    continue
                relative = source.relative_to(base)
                if reserved(relative):
                    continue
                target = objects / relative
                if target.exists() or target.is_symlink():
                    continue
                target.parent.mkdir(parents=True, exist_ok=True)
                target.symlink_to(source.resolve())
    for prefix in project_prefixes:
        for path in (objects / prefix).rglob('*'):
            if path.is_symlink() and reserved(path.relative_to(objects)):
                raise ValueError('Reserved output is a symlink; use a fresh private work directory: ' + str(path))
    environment = dict(os.environ, LEAN_PATH=str(objects) + ':' + a.base_lean_path, LEAN_NUM_THREADS='1')
    receipts = []

    def run(label, source, source_root, memory, output=None):
        command = [str(a.lean.resolve()), '-j1', '-M' + str(memory), '-R', str(source_root)]
        if output:
            output.parent.mkdir(parents=True, exist_ok=True)
            command += ['-o', str(output)]
        command += [str(source)]
        log = work / (label + '.log')
        with a.lock_file.open('a+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            started = datetime.datetime.now(datetime.timezone.utc).isoformat()
            tick = time.monotonic()
            with log.open('w') as out:
                result = subprocess.run(command, cwd=root, env=environment, stdout=out, stderr=subprocess.STDOUT)
            row = {'label': label, 'command': command, 'started_utc': started,
                   'ended_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   'seconds': time.monotonic() - tick, 'exit_code': result.returncode,
                   'cumulative_peak_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                   'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
            receipts.append(row)
            (work / 'receipts.json').write_text(json.dumps(receipts, indent=2) + '\n')
            fcntl.flock(lock, fcntl.LOCK_UN)
        print(label + (' PASS' if result.returncode == 0 else ' FAIL'), flush=True)
        if result.returncode:
            raise RuntimeError('Lean failed; inspect ' + str(log))

    for i, row in enumerate(builds, 1):
        run('proof-' + str(i).zfill(2), root / row['source'], root, 4096,
            objects / row['source'].replace('.lean', '.olean'))
    for row in json.loads((evidence / 'regressions.json').read_text()):
        run(Path(row['source']).stem, package / row['source'], package, 4096)
    run('inventory', package / 'audit/MC6ThreeBridgesInventory.lean', package, 6144)
    subprocess.run([sys.executable, str(evidence / 'verify_evidence.py'), str(work / 'inventory.log'),
                    '--repo-root', str(root)], check=True)
    print('REPRODUCTION_PASS: 14 proof builds, 5 original audits, 37 regressions, exact 242-declaration inventory')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
