from pathlib import Path
import subprocess,os,json,datetime,hashlib,resource,sys,re
from guarded_process import available_memory,run_guarded,RSS_GUARD_BYTES
from compiler_environment import resolve_compiler_environment

root=Path(__file__).resolve().parent;project=root/'project'
filename=sys.argv[1];cap=int(sys.argv[2]) if len(sys.argv)>2 else 6144;tag=sys.argv[3] if len(sys.argv)>3 else Path(filename).stem
assert 1<=cap<=8192
src=(project/filename).resolve(strict=True)
relative=src.relative_to(project.resolve())
assert src.suffix=='.lean' and src.is_file(), 'Expected a local Lean source file'
assert re.fullmatch(r'[A-Za-z0-9_.-]+',tag), 'Invalid receipt tag'
out=project/'.lake/build/lib/lean'/relative.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
logs=root/'logs/lean-checks';logs.mkdir(parents=True,exist_ok=True)
if available_memory()<8*1024**3:raise RuntimeError('Measured headroom below 8 GiB')

# Resolve exactly the environment Lake gives its child. Retain it only in memory:
# it may contain inherited credentials, so never write the full JSON to a log.
env=os.environ.copy()
if env.get('DETERMINANT_LAKE_ENV_READY')!='1':
    env=resolve_compiler_environment(root,project,env)
if Path(env.get('LEAN','')).resolve()!=(root/'toolchain/bin/lean').resolve():
    raise RuntimeError('Compiler environment selected a different Lean executable')
if Path(env.get('LEAN_SYSROOT','')).resolve()!=(root/'toolchain').resolve():
    raise RuntimeError('Compiler environment selected a different Lean sysroot')
lean=str(root/'toolchain/bin/lean')
cmd=[lean,'-j1',f'-M{cap}','-DautoImplicit=false']
if filename.startswith('PrimeNumberTheoremAnd/'):cmd.append('-DrelaxedAutoImplicit=false')
cmd+=['-o',str(out),str(src)]
safe_keys=['LEAN','LEAN_SYSROOT','LEAN_PATH','LEAN_SRC_PATH','LEAN_AR','LEAN_CC','LEAN_GITHASH','LAKE','LAKE_HOME','LEAN_NUM_THREADS']
record={'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':filename,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'command':cmd,'rss_guard_bytes':RSS_GUARD_BYTES,'cgroup_limit':'not configured; sampled process-tree RSS watchdog only','compiler_environment':{key:env[key] for key in safe_keys if key in env},'launcher':'direct pinned Lean after completed Lake environment resolution'}
result=run_guarded(cmd,project,env,logs/(tag+'.log'))
samples=result.pop('samples');record.update(result)
record['max_child_rss_kib']=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
if record['exit_code']==0:record['olean_sha256']=hashlib.sha256(out.read_bytes()).hexdigest()
(logs/(tag+'.resources.json')).write_text(json.dumps(samples,indent=2)+'\n')
(logs/(tag+'.receipt.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2),flush=True)
print((logs/(tag+'.log')).read_text(),flush=True)
sys.exit(record['exit_code'])
