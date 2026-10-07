"""Resolve Lake's exact child environment privately, under the replay guards."""
from pathlib import Path
import json,sys
from guarded_process import run_guarded

def resolve_compiler_environment(root,project,env):
    logs=root/'logs';logs.mkdir(parents=True,exist_ok=True)
    command=[str(root/'toolchain/bin/lake'),'env',sys.executable,'-c','import json,os; print(json.dumps(dict(os.environ)))']
    result=run_guarded(command,project,env,logs/'environment-resolution.stderr.log',capture_stdout=True)
    captured=result.pop('_captured_stdout')
    # No environment content is written to these diagnostic files.
    (logs/'environment-resolution.resources.json').write_text(json.dumps(result.pop('samples'),indent=2)+'\n')
    (logs/'environment-resolution.receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    if result['exit_code']!=0:raise RuntimeError('Guarded Lake environment resolution failed; see its receipt')
    resolved=json.loads(captured)
    if not isinstance(resolved,dict) or not all(isinstance(k,str) and isinstance(v,str) for k,v in resolved.items()):
        raise RuntimeError('Lake returned an invalid child environment')
    if Path(resolved['LEAN']).resolve()!=(root/'toolchain/bin/lean').resolve():
        raise RuntimeError('Lake selected a different Lean executable')
    return resolved
