from pathlib import Path
import subprocess, re, os, datetime
root=Path(__file__).resolve().parent; project=root/'project'; packages=project/'.lake/packages'
pkgroots={'Cache':packages/'mathlib','Batteries':packages/'batteries'}
seen=set(); order=[]
def dfs(mod):
    if mod in seen:return
    seen.add(mod)
    top=mod.split('.')[0]
    if top not in pkgroots:return
    src=pkgroots[top]/(mod.replace('.','/')+'.lean')
    for imp in re.findall(r'^(?:public\s+)?import\s+(\S+)',src.read_text(),re.M):dfs(imp)
    order.append((mod,src,pkgroots[top]))
dfs('Cache.Main')
(root/'logs/cache-tool-order.txt').write_text('\n'.join(m for m,s,p in order)+'\n')
for mod,src,pkg in order:
    out=pkg/'.lake/build/lib/lean'/(mod.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
    cmd=['lake','env','lean','-j1','-M4096','-R',str(pkg),'-o',str(out),str(src)]
    print(datetime.datetime.now(datetime.timezone.utc).isoformat(),subprocess.list2cmdline(cmd),flush=True)
    subprocess.run(cmd,cwd=project,check=True)
print('CACHE_TOOL_MODULES_COMPILED',len(order),flush=True)
