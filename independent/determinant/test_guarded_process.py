import os,sys,tempfile,time,unittest,signal
from unittest.mock import patch
import guarded_process
from pathlib import Path
from guarded_process import run_guarded,process_table,RSS_GUARD_BYTES

class GuardTests(unittest.TestCase):
    def run_command(self,code,**kwargs):
        with tempfile.TemporaryDirectory() as directory:
            return run_guarded([sys.executable,'-c',code],directory,os.environ.copy(),Path(directory)/'test.log',interval=0.05,grace_seconds=0.25,**kwargs)

    def test_success(self):
        result=self.run_command('print(42)')
        self.assertEqual(result['exit_code'],0)
        self.assertFalse(result['watchdog_stopped'])
        self.assertFalse(result['surviving_owned_processes'])

    def test_child_nonzero_is_failure(self):
        result=self.run_command('raise SystemExit(7)')
        self.assertEqual(result['exit_code'],7)

    def test_guard_event_never_counts_as_success(self):
        result=self.run_command('import time; time.sleep(30)',available_reader=lambda:0)
        self.assertEqual(result['exit_code'],124)
        self.assertEqual(result['watchdog_stopped'],'available_memory_floor')
        self.assertFalse(result['surviving_owned_processes'])

    def test_live_child_is_killed_after_leader_exits(self):
        code='import os,signal,time; pid=os.fork(); signal.signal(signal.SIGTERM,signal.SIG_IGN) if pid==0 else None; time.sleep(30) if pid==0 else time.sleep(0.2)'
        result=self.run_command(code)
        self.assertFalse(result['surviving_owned_processes'])
        self.assertEqual(result['exit_code'],124)
        child_pids={item['pid'] for sample in result['samples'] for item in sample['processes'] if item['ppid']!=os.getpid()}
        self.assertTrue(child_pids)
        table=process_table()
        self.assertTrue(all(pid not in table or table[pid]['state'] in ['Z','X'] for pid in child_pids))

    def test_budget_unchanged(self):
        self.assertEqual(RSS_GUARD_BYTES,7784628224)

    def test_capture_stdout_is_not_written_to_log(self):
        with tempfile.TemporaryDirectory() as directory:
            log=Path(directory)/'private.log'
            result=run_guarded([sys.executable,'-c','print("SENTINEL_PRIVATE_ENV_VALUE")'],directory,os.environ.copy(),log,capture_stdout=True,interval=0.05)
            self.assertEqual(result['exit_code'],0)
            self.assertIn(b'SENTINEL_PRIVATE_ENV_VALUE',result['_captured_stdout'])
            self.assertNotIn('SENTINEL_PRIVATE_ENV_VALUE',log.read_text())

    def test_monitor_exception_cleans_up(self):
        def broken_reader():raise ValueError('synthetic monitor fault')
        result=self.run_command('import time; time.sleep(30)',available_reader=broken_reader)
        self.assertEqual(result['exit_code'],124)
        self.assertFalse(result['surviving_owned_processes'])

    def test_repeated_termination_does_not_interrupt_cleanup(self):
        original=guarded_process.signal_owned
        calls=[]
        def repeated_signal(root_pid,known,sig):
            if sig==signal.SIGTERM:
                calls.append(sig)
                os.kill(os.getpid(),signal.SIGTERM)
                os.kill(os.getpid(),signal.SIGTERM)
            return original(root_pid,known,sig)
        with patch('guarded_process.signal_owned',side_effect=repeated_signal):
            result=self.run_command('import time; time.sleep(30)',available_reader=lambda:0)
        self.assertTrue(calls)
        self.assertEqual(result['exit_code'],124)
        self.assertFalse(result['surviving_owned_processes'])

    def test_guard_failure_when_terminated_child_exits_zero(self):
        calls=0
        def memory():
            nonlocal calls
            calls+=1
            return 16*1024**3 if calls<5 else 0
        code='import signal,sys,time; signal.signal(signal.SIGTERM,lambda *_:sys.exit(0)); time.sleep(30)'
        result=self.run_command(code,available_reader=memory)
        self.assertEqual(result['child_exit_code'],0)
        self.assertEqual(result['exit_code'],124)

    def test_capture_with_surviving_child_is_bounded(self):
        code='import os,signal,time; pid=os.fork(); signal.signal(signal.SIGTERM,signal.SIG_IGN) if pid==0 else None; time.sleep(30) if pid==0 else time.sleep(0.2)'
        start=time.monotonic()
        result=self.run_command(code,capture_stdout=True)
        self.assertLess(time.monotonic()-start,3)
        self.assertEqual(result['exit_code'],124)
        self.assertFalse(result['surviving_owned_processes'])

    def test_capture_size_is_bounded(self):
        result=self.run_command('import sys; sys.stdout.write("X"*(5*1024**2))',capture_stdout=True)
        self.assertEqual(result['exit_code'],124)
        self.assertLessEqual(len(result['_captured_stdout']),4*1024**2)

if __name__=='__main__':unittest.main()
