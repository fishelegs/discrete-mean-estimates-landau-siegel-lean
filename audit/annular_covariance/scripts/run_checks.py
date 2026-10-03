#!/usr/bin/env python3
"""Run portable finite checks; optionally verify a separately supplied source TeX."""
from pathlib import Path
import argparse, os, subprocess, sys

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,help='External source TeX to hash; no bundled paper is required for algebra checks')
args=parser.parse_args()
source=args.source.resolve() if args.source is not None else None
root=Path(__file__).resolve().parents[1]
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
names=['annular','independent','fixed_log_author','fixed_log_windows']
for name in names:
    command=[sys.executable,'-B',str(root/'scripts'/('check_'+name+'.py'))]
    output='RERUN_'+name.upper()+'.txt'
    if name=='independent' and source is not None:
        command.extend(['--source',str(source)])
        output='RERUN_INDEPENDENT_WITH_EXTERNAL_SOURCE.txt'
    p=subprocess.run(command,capture_output=True,text=True,env=env)
    if p.returncode:
        print(p.stdout,end=''); print(p.stderr,end='',file=sys.stderr); raise SystemExit(p.returncode)
    assert p.stdout==(root/'results'/output).read_text(),'Regression output differs: '+name
    print('PASS: '+name+'; output matches recorded rerun')
if source is None:
    print('SKIPPED: external source-file SHA256 check; supply --source to reproduce it')
else:
    print('PASS: external source-file SHA256 matches the originally audited input')
print('All finite algebra checks passed. Uniform analytic estimates require the written reports and reviews.')
