#!/usr/bin/env python3
"""Isolated Linux/x86_64 replay; all writes stay under this extracted directory."""
from pathlib import Path
import os,sys,argparse,subprocess,json,hashlib,re,shutil,time
from compiler_environment import resolve_compiler_environment
R=Path(__file__).resolve().parent; P=R/'project'
a=argparse.ArgumentParser(description=__doc__)
a.add_argument('--setup',action='store_true',help='Download exact official toolchain and nine pinned git packages, then restore official mathlib cache')
a.add_argument('--build',action='store_true',help='Serially compile selected local targets and their full local dependency closure')
a.add_argument('--memory-mb',type=int,default=6656)
a.add_argument('--trim-download-cache',action='store_true',help='After successful setup stages, remove this replay directory\'s verified Lean archive and restored compressed .ltar cache files')
a.add_argument('targets',nargs='*',default=['EffectiveConstantSearch','RawDeterminantAudit','FullRawTypeReceipt','Splice.AnalyticAudit'])
args=a.parse_args()
if not 1<=args.memory_mb<=8192: a.error('memory cap must be at most 8192 MB')
if args.trim_download_cache and not args.setup: a.error('--trim-download-cache requires --setup')
if not args.setup and not args.build: a.print_help();sys.exit(0)
for d in ['downloads','toolchain','logs','home','cache/mathlib','elan','tmp']: (R/d).mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env.update(PATH=str(R/'toolchain/bin')+os.pathsep+env['PATH'],HOME=str(R/'home'),XDG_CACHE_HOME=str(R/'cache'),MATHLIB_CACHE_DIR=str(R/'cache/mathlib'),ELAN_HOME=str(R/'elan'),TMPDIR=str(R/'tmp'),MATHLIB_NO_CACHE_ON_UPDATE='1',LEAN_NUM_THREADS='1',LAKE_JOBS='1')
for key in ['MATHLIB_CACHE_GET_URL','MATHLIB_CACHE_BASE_URL','MATHLIB_CACHE_FROM','MATHLIB_CACHE_DEBUG_USE_LEGACY']:
 env.pop(key,None)
resource_records=[]
def run(cmd,cwd=P):
 print('+',subprocess.list2cmdline([str(x) for x in cmd]),flush=True)
 if not args.setup:
  subprocess.run([str(x) for x in cmd],cwd=cwd,env=env,check=True)
  return
 initial=shutil.disk_usage(R).free;minimum=initial
 process=subprocess.Popen([str(x) for x in cmd],cwd=cwd,env=env)
 while process.poll() is None:
  minimum=min(minimum,shutil.disk_usage(R).free);time.sleep(1)
 final=shutil.disk_usage(R).free;minimum=min(minimum,final)
 resource_records.append({'command':[str(x) for x in cmd],'initial_free_bytes':initial,'minimum_sampled_free_bytes':minimum,'final_free_bytes':final,'exit_code':process.returncode})
 (R/'logs/setup-resources.json').write_text(json.dumps(resource_records,indent=2)+'\n')
 if process.returncode:raise subprocess.CalledProcessError(process.returncode,cmd)
if args.setup:
 archive=R/'downloads/lean-4.34.1-linux.tar.zst'
 if not archive.exists():run(['curl','--fail','--location','--retry','2','--output',archive,'https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst'])
 expected='47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4'
 assert hashlib.sha256(archive.read_bytes()).hexdigest()==expected,'Lean archive hash mismatch'
 if not (R/'toolchain/bin/lean').exists():run(['tar','--zstd','-xf',archive,'-C',R/'toolchain','--strip-components=1'])
 version=subprocess.check_output(['lean','--version'],cwd=P,env=env,text=True)
 assert 'version 4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version, version
 print(version,flush=True);run(['lake','--version'])
 (R/'logs/toolchain.json').write_text(json.dumps({'version':version.strip(),'archive_sha256':expected},indent=2)+'\n')
 if args.trim_download_cache:
  archive.unlink();print('Removed verified Lean download archive after extraction and version check',flush=True)
 for pkg in json.loads((P/'lake-manifest.json').read_text())['packages']:
  dest=P/'.lake/packages'/pkg['name'];dest.parent.mkdir(parents=True,exist_ok=True)
  if not (dest/'.git').exists():
   run(['git','init','-q',dest]);run(['git','-C',dest,'remote','add','origin',pkg['url']]);run(['git','-C',dest,'fetch','--depth','1','origin',pkg['rev']]);run(['git','-C',dest,'checkout','--detach','FETCH_HEAD'])
  got=subprocess.check_output(['git','-C',str(dest),'rev-parse','HEAD'],text=True,env=env).strip()
  assert got==pkg['rev'],f"Wrong revision in {dest}: {got}"
 run([sys.executable,R/'build-cache-tool.py'])
 run(['lake','env','lean','-j1','-M4096','-R','.lake/packages/mathlib','--run','.lake/packages/mathlib/Cache/Main.lean','get','Mathlib','--cache-from=master,legacy'])
 if args.trim_download_cache:
  entries=list((R/'cache/mathlib').glob('*.ltar'))
  for entry in entries:entry.unlink()
  print(f'Removed {len(entries)} compressed cache files after successful restoration',flush=True)
if args.build:
 for target in args.targets:
  if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',target):
   raise ValueError(f'Invalid local target module: {target}')
  if not (P/(target.replace('.','/')+'.lean')).is_file():
   raise FileNotFoundError(f'Requested local target does not exist: {target}')
 seen=set();active=set();order=[]
 def visit(m):
  if m in seen:return
  source=P/(m.replace('.','/')+'.lean')
  if not source.exists():return # External imports are provided by the pinned cache.
  assert m not in active,f'import cycle at {m}'
  active.add(m)
  for dep in re.findall(r'^(?:public\s+)?import\s+([A-Za-z0-9_.]+)',source.read_text(),re.M):visit(dep)
  active.remove(m);seen.add(m);order.append(m)
 for t in args.targets:visit(t)
 assert order, 'No local modules selected for verification'
 # Finish the Lake wrapper once before any heavy proof import. The complete
 # child environment remains private in memory; never persist it to a log.
 env=resolve_compiler_environment(R,P,env)
 env['DETERMINANT_LAKE_ENV_READY']='1'
 for i,m in enumerate(order,1):
  file=m.replace('.','/')+'.lean';tag='replay-'+m
  print(f'[{i}/{len(order)}] {m}',flush=True)
  run([sys.executable,R/'compile-one-guarded.py',file,str(args.memory_mb),tag])
  log=(R/'logs/lean-checks'/(tag+'.log')).read_text()
  assert 'sorryAx' not in log,f'sorryAx in {m}'
  if '#print axioms' in (P/file).read_text():run([sys.executable,R/'check-axiom-log.py',file,tag])
 print('All selected local source targets compiled successfully; historical evidence is summarized under verification/.')
