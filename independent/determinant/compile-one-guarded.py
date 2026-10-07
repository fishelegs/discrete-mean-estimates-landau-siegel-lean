from pathlib import Path
import subprocess,os,json,time,datetime,hashlib,resource,signal,sys,re
root=Path(__file__).resolve().parent;project=root/'project'
filename=sys.argv[1];cap=int(sys.argv[2]) if len(sys.argv)>2 else 6144;tag=sys.argv[3] if len(sys.argv)>3 else Path(filename).stem
assert 1<=cap<=8192
src=(project/filename).resolve(strict=True)
relative=src.relative_to(project.resolve())
assert src.suffix=='.lean' and src.is_file(), 'Expected a local Lean source file'
assert re.fullmatch(r'[A-Za-z0-9_.-]+',tag), 'Invalid receipt tag'
out=project/'.lake/build/lib/lean'/relative.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
logs=root/'logs/lean-checks';logs.mkdir(exist_ok=True)
cmd=['lake','env','lean','-j1',f'-M{cap}','-DautoImplicit=false','-o',str(out),str(src)]
if filename.startswith('PrimeNumberTheoremAnd/'):
 cmd.insert(6, '-DrelaxedAutoImplicit=false')
record={'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':filename,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'command':cmd,'rss_guard_bytes':int(7.25*1024**3),'cgroup_limit':'not configured; sampled process-tree RSS watchdog only'}
def available():return next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
def tree(pid):
 procs={}
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   d={a:b.strip() for a,b in (l.split(':',1) for l in (p/'status').read_text().splitlines() if ':' in l)}
   procs[int(p.name)]=(int(d['PPid']),int(d.get('VmRSS','0 kB').split()[0])*1024)
  except (FileNotFoundError,ProcessLookupError,PermissionError):continue
 ids={pid}
 while True:
  found={p for p,(pp,r) in procs.items() if pp in ids}
  if found<=ids:break
  ids|=found
 return sum(procs.get(p,(0,0))[1] for p in ids)
if available()<8*1024**3:raise RuntimeError('Measured headroom below8GiB')
start=time.monotonic();peak=0;samples=[]
with (logs/(tag+'.log')).open('w') as log:
 p=subprocess.Popen(cmd,cwd=project,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  rss=tree(p.pid);avail=available();peak=max(peak,rss);samples.append({'seconds':round(time.monotonic()-start,2),'rss':rss,'available':avail})
  if rss>record['rss_guard_bytes'] or avail<1024**3:
   record['watchdog_stopped']='RSS or available-memory guard';os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=10)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
   break
  time.sleep(1)
 code=p.wait()
record.update(exit_code=code,seconds=round(time.monotonic()-start,3),peak_process_tree_rss_bytes=peak,max_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
if code==0:record['olean_sha256']=hashlib.sha256(out.read_bytes()).hexdigest()
(logs/(tag+'.resources.json')).write_text(json.dumps(samples,indent=2)+'\n')
(logs/(tag+'.receipt.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2),flush=True)
print((logs/(tag+'.log')).read_text(),flush=True)
sys.exit(code)
