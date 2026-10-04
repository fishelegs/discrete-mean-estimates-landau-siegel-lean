#!/usr/bin/env python3
"""Rerun the pinned inventory with existing compiled objects, without cache writes.

This is an audit-only reproducer, not a six-module build script. Supply a complete
read-only LEAN_PATH containing the six modules and their existing dependencies.
No object output, dependency download, Lake invocation, or file overlay is made.
Use the same shared lock file as other proof workers. All new logs stay private.
"""
import argparse
import datetime
import fcntl
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

sys.dont_write_bytecode = True
from verify_evidence import digest, validate_package, validate_log


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', required=True, type=Path)
    parser.add_argument('--work-dir', required=True, type=Path)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--lean-path', required=True)
    parser.add_argument('--lock-file', required=True, type=Path)
    args = parser.parse_args()
    evidence = Path(__file__).resolve().parent
    package = evidence.parent.parent
    root = args.repo_root.resolve()
    work = args.work_dir.resolve()
    for protected in [root, package]:
        if work == protected or protected in work.parents:
            raise ValueError('Use a private work directory outside the repository/public package')
    verified = validate_package(root)
    if not args.lean_path or any(not Path(part).is_absolute() or not Path(part).is_dir() for part in args.lean_path.split(os.pathsep)):
        raise ValueError('Supply existing absolute LEAN_PATH directories')
    work.mkdir(parents=True, exist_ok=True)
    log = work / 'ActualGramUniformInventory.log'
    receipt_path = work / 'ActualGramUniformInventory.receipt.json'
    if log.exists() or receipt_path.exists():
        raise ValueError('Use fresh private output names; an audit log/receipt already exists')
    source = package / 'audit/ActualGramUniformInventory.lean'
    command = [str(args.lean.resolve()), '-j1', '-M6144', '-R', str(package), str(source)]
    environment = dict(os.environ, LEAN_PATH=args.lean_path, LEAN_NUM_THREADS='1')
    with args.lock_file.open('a+') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        version = subprocess.check_output([str(args.lean.resolve()), '--version'], text=True, env=environment)
        if not version.startswith('Lean (version 4.30.0,'):
            raise ValueError('Expected Lean 4.30.0, got: ' + version.strip())
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        tick = time.monotonic()
        with log.open('w', encoding='utf-8') as output:
            result = subprocess.run(command, cwd=package, env=environment, stdout=output, stderr=subprocess.STDOUT)
        receipt = {'command': command, 'started_utc': started,
                   'ended_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   'seconds': time.monotonic() - tick, 'exit_code': result.returncode,
                   'peak_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                   'source_sha256': digest(source.read_bytes()), 'full_log_sha256': digest(log.read_bytes()),
                   'mode': 'audit only; reused objects read only; no object output'}
        receipt_path.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    if result.returncode:
        raise ValueError('Lean audit failed; inspect ' + str(log))
    validate_log(log, *verified)
    print('PASS: pinned central inventory reproduced and all public hashes verified')
    print('Private full log: ' + str(log))
    print('Private run receipt: ' + str(receipt_path))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, UnicodeError, subprocess.SubprocessError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
