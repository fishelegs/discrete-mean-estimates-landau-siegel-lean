#!/usr/bin/env python3
"""Rebuild only this bridge and its two missing prerequisites in a private overlay.
Needs installed Lean 4.30.0 and existing immutable dependency objects. Never invokes
Lake, downloads dependencies, or writes into the checkout or shared build cache.
Use the same --lock-file as the other proof workers.
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
    p.add_argument('--repo-root', type=Path, required=True)
    p.add_argument('--work-dir', type=Path, required=True)
    p.add_argument('--lean', type=Path, required=True)
    p.add_argument('--base-lean-path', required=True)
    p.add_argument('--lock-file', type=Path, required=True)
    a = p.parse_args()
    evidence = Path(__file__).resolve().parent
    package = evidence.parent.parent
    root, work = a.repo_root.resolve(), a.work_dir.resolve()
    if work == root or root in work.parents or work == package or package in work.parents:
        raise ValueError('Choose a private work directory outside the checkout and evidence package')
    read = lambda name: json.loads((evidence / name).read_text())
    for row in read('sources.json') + read('dependency-sources.json') + read('prerequisites.json'):
        data = (root / row['source']).read_bytes()
        if hashlib.sha256(data).hexdigest() != row['sha256']:
            raise ValueError('Repository source mismatch: ' + row['source'])
    builds = read('builds.json')
    reserved = {r['source'].removesuffix('.lean') for r in builds} | {'audit/FixedHLambdaReplacementInventory'}
    objects = work / 'objects'
    objects.mkdir(parents=True, exist_ok=True)
    def is_reserved(relative):
        name = relative.as_posix()
        return any(name == stem or name.startswith(stem + '.') for stem in reserved)
    # Traverse only the installed project-object subtrees; reserve every output
    # suffix so no compiler output can follow a link into a shared cache.
    for base in map(Path, a.base_lean_path.split(os.pathsep)):
        for prefix in ['ZhangLS', 'audit']:
            tree = base / prefix
            if not tree.is_dir():
                continue
            for directory, _, files in os.walk(tree):
                for name in files:
                    source = Path(directory) / name
                    relative = source.relative_to(base)
                    if is_reserved(relative):
                        continue
                    target = objects / relative
                    if target.exists() or target.is_symlink():
                        continue
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.symlink_to(source.resolve())
    for stem in reserved:
        prefix = objects / stem
        if prefix.parent.exists():
            for path in prefix.parent.iterdir():
                if path.name == prefix.name or path.name.startswith(prefix.name + '.'):
                    raise ValueError('Reserved output exists; choose a fresh work directory: ' + str(path))
    environment = dict(os.environ, LEAN_PATH=str(objects) + ':' + a.base_lean_path, LEAN_NUM_THREADS='1')
    receipts = []
    def run(label, source, source_root, output=None):
        command = [str(a.lean.resolve()), '-j1', '-M4096', '-R', str(source_root)]
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
            receipts.append({'label': label, 'command': command, 'started_utc': started,
                'ended_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                'seconds': time.monotonic() - tick, 'exit_code': result.returncode,
                'cumulative_peak_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
            (work / 'receipts.json').write_text(json.dumps(receipts, indent=2) + '\n')
            fcntl.flock(lock, fcntl.LOCK_UN)
        print(label + (' PASS' if result.returncode == 0 else ' FAIL'), flush=True)
        if result.returncode:
            raise RuntimeError('Lean failed; inspect ' + str(log))
    for i, row in enumerate(builds, 1):
        run('build-' + str(i).zfill(2), root / row['source'], root,
            objects / row['source'].replace('.lean', '.olean'))
    run('inventory', package / 'audit/FixedHLambdaReplacementInventory.lean', package)
    subprocess.run([sys.executable, str(evidence / 'verify_evidence.py'), str(work / 'inventory.log'),
        '--repo-root', str(root)], check=True)
    print('REPRODUCTION_PASS: 3 bridge modules, 2 prerequisites, 12 regressions, complete exact inventory')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
