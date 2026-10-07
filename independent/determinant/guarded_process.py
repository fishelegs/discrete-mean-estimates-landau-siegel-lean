"""Linux process-tree measurement and bounded cleanup for the Lean replay."""
from pathlib import Path
import json,os,signal,subprocess,time

RSS_GUARD_BYTES=int(7.25*1024**3)
AVAILABLE_FLOOR_BYTES=1024**3

def available_memory():
    return next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))

def process_table():
    result={}
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():continue
        try:
            status=dict(line.split(':',1) for line in (path/'status').read_text().splitlines() if ':' in line)
            fields=(path/'stat').read_text().rsplit(')',1)[1].split()
            item={'pid':int(path.name),'ppid':int(fields[1]),'pgid':int(fields[2]),'session':int(fields[3]),'start_time_ticks':int(fields[19]),'state':fields[0],'name':status['Name'].strip(),'threads':int(status['Threads'])}
            for name in ['VmRSS','VmHWM','RssAnon','RssFile','RssShmem']:
                item[name+'_bytes']=int(status.get(name,'0 kB').split()[0])*1024
            result[item['pid']]=item
        except (FileNotFoundError,ProcessLookupError,PermissionError,KeyError,ValueError):pass
    return result

def owned_processes(root_pid,known):
    table=process_table()
    ids={pid for pid,start in known.items() if pid in table and table[pid]['start_time_ticks']==start}
    # start_new_session=True gives this invocation its own session/process group.
    ids.update(pid for pid,item in table.items() if item['session']==root_pid)
    if root_pid in table and (root_pid not in known or table[root_pid]['start_time_ticks']==known[root_pid]):ids.add(root_pid)
    while True:
        children={pid for pid,item in table.items() if item['ppid'] in ids}
        if children<=ids:break
        ids|=children
    result=[table[pid] for pid in sorted(ids) if pid in table]
    for item in result:known[item['pid']]=item['start_time_ticks']
    return result

def running(items):
    return [item for item in items if item['state'] not in ['Z','X']]

def signal_owned(root_pid,known,sig):
    items=owned_processes(root_pid,known)
    # Signal the owned group even if its leader has already exited.
    if any(item['pgid']==root_pid for item in items):
        try:os.killpg(root_pid,sig)
        except ProcessLookupError:pass
    for item in items:
        if item['pgid']==root_pid or item['state'] in ['Z','X']:continue
        latest=process_table().get(item['pid'])
        if latest and latest['start_time_ticks']==item['start_time_ticks']:
            try:os.kill(item['pid'],sig)
            except ProcessLookupError:pass

def stop_owned(process,known,grace_seconds=3):
    signal_owned(process.pid,known,signal.SIGTERM)
    end=time.monotonic()+grace_seconds
    while time.monotonic()<end:
        process.poll()
        if not running(owned_processes(process.pid,known)):break
        time.sleep(0.1)
    signal_owned(process.pid,known,signal.SIGKILL)
    try:process.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:pass
    end=time.monotonic()+grace_seconds
    while time.monotonic()<end:
        items=owned_processes(process.pid,known)
        if not running(items):return items
        time.sleep(0.1)
    return owned_processes(process.pid,known)

def run_guarded(command,cwd,env,log_path,*,rss_guard=RSS_GUARD_BYTES,available_floor=AVAILABLE_FLOOR_BYTES,available_reader=available_memory,interval=1.0,grace_seconds=3,capture_stdout=False):
    started=time.monotonic();known={};samples=[];peak=0;reason=None
    output=[];output_size=0;stdout_eof=False;monitor_error=None
    with Path(log_path).open('w') as log:
        process=subprocess.Popen(command,cwd=cwd,env=env,stdout=subprocess.PIPE if capture_stdout else log,stderr=log if capture_stdout else subprocess.STDOUT,start_new_session=True)
        if capture_stdout:
            os.set_blocking(process.stdout.fileno(),False)
        def drain_stdout():
            nonlocal output_size,stdout_eof
            if not capture_stdout or stdout_eof:return
            # Bounded, nonblocking capture avoids pipe deadlock and credential logs.
            for _ in range(16):
                try:chunk=os.read(process.stdout.fileno(),65536)
                except BlockingIOError:return
                if not chunk:stdout_eof=True;return
                output_size+=len(chunk)
                if output_size>4*1024**2:raise RuntimeError('captured stdout exceeded bounded limit')
                output.append(chunk)
        def interrupted(signum,frame):raise InterruptedError('guard interrupted')
        old_handlers={sig:signal.getsignal(sig) for sig in [signal.SIGTERM,signal.SIGINT]}
        for sig in old_handlers:signal.signal(sig,interrupted)
        try:
            while True:
                drain_stdout()
                items=owned_processes(process.pid,known)
                rss=sum(item['VmRSS_bytes'] for item in items);peak=max(peak,rss)
                available=available_reader()
                samples.append({'seconds':round(time.monotonic()-started,3),'rss':rss,'available':available,'processes':items})
                if rss>rss_guard:reason='process_tree_rss_limit'
                elif available<available_floor:reason='available_memory_floor'
                code=process.poll()
                if reason or code is not None:break
                time.sleep(interval)
        except BaseException as error:
            reason='monitor_interrupted_or_failed';monitor_error=type(error).__name__
        # A second termination signal must not interrupt bounded child cleanup.
        for sig in old_handlers:signal.signal(sig,signal.SIG_IGN)
        try:
            live_before_cleanup=running(owned_processes(process.pid,known))
            if reason is None and live_before_cleanup:reason='owned_descendant_after_leader_exit'
            if reason or live_before_cleanup:
                survivors=stop_owned(process,known,grace_seconds)
            else:
                process.wait(timeout=grace_seconds);survivors=owned_processes(process.pid,known)
            if capture_stdout:
                try:drain_stdout()
                except RuntimeError:reason='capture_stdout_limit'
                if not stdout_eof and reason is None:reason='capture_pipe_not_closed'
                process.stdout.close()
        finally:
            for sig,handler in old_handlers.items():signal.signal(sig,handler)
    live=running(survivors)
    if live and reason is None:reason='owned_process_survivor'
    # A watchdog event is always a failed invocation, even if the leader exits 0.
    exit_code=124 if reason else process.returncode
    result={'exit_code':exit_code,'child_exit_code':process.returncode,'seconds':round(time.monotonic()-started,3),'peak_process_tree_rss_bytes':peak,'watchdog_stopped':reason,'monitor_error':monitor_error,'surviving_owned_processes':live,'terminated_zombies':survivors,'samples':samples}
    if capture_stdout:result['_captured_stdout']=b''.join(output)
    return result
