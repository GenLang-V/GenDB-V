"""Unpaid subprocess regression of the generated author Bash guardian (activity_shell.py).

Usage: python3 activity_shell_test.py <call>/author-shell/gendb-author-bash (the installed guardian; its sibling
activity-config.json names the activity lock). No provider is involved."""
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

wrapper = Path(sys.argv[1])
root = wrapper.parent
lock = Path(json.loads((root / 'activity-config.json').read_text())['activity_lock'])
started = time.monotonic()


def until(check):
    deadline = time.monotonic() + 5
    while not check():
        assert time.monotonic() < deadline, 'subprocess deadline'
        time.sleep(.01)


def events():
    return [json.loads(line) for p in (root / 'tool-activity').glob('*.jsonl')
            for line in p.read_text().splitlines()]


def spawn(command):
    return subprocess.Popen([str(wrapper), '-c', command], cwd=root,
                            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)


def held():
    with lock.open('a') as fd:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return False
        except BlockingIOError:
            return True


# Exact argv, stdin, separate stdout/stderr and exit; child does not recurse.
value = "literal ' \" $() ;\nsecond line"
env = dict(os.environ, CLAUDE_CODE_SHELL=str(wrapper), CLAUDE_CODE_SHELL_PREFIX='bad-prefix')
p = subprocess.run([str(wrapper), '-c', 'printf "%s" "$1"; cat; printf err >&2; test "$SHELL" = /bin/bash; test -z "${CLAUDE_CODE_SHELL:-}"; exit 7', 'arg0', value],
                   input=b'input\x00bytes', capture_output=True, env=env, timeout=5)
assert (p.returncode, p.stdout, p.stderr) == (7, value.encode()+b'input\x00bytes', b'err')
assert subprocess.run([str(wrapper), '-c', 'if'], capture_output=True, timeout=5).returncode == 2
signalled = subprocess.run([str(wrapper), '-c', 'trap -p PIPE; kill -PIPE $$; printf survived'],
                          capture_output=True, timeout=5)
assert (signalled.returncode, signalled.stdout, signalled.stderr) == (-signal.SIGPIPE, b'', b'')

# A remote provider can keep running while an exclusive benchmark lease is
# held. Only its Bash subprocess queues; no tool body executes before release.
marker = root / 'queued-body'
with lock.open('a') as fd:
    fcntl.flock(fd, fcntl.LOCK_EX)
    before = len(events())
    p = spawn('printf ran > queued-body')
    until(lambda: len(events()) > before)
    time.sleep(.08)
    assert not marker.exists() and p.poll() is None
assert p.communicate(timeout=5) == (b'', b'') and p.returncode == 0
assert marker.read_text() == 'ran'

# Two tools can overlap under SH. EX remains refused until BOTH finish.
p = spawn('touch first-start; while ! test -e first-stop; do sleep .02; done')
q = spawn('touch second-start; while ! test -e second-stop; do sleep .02; done')
until(lambda: (root/'first-start').exists() and (root/'second-start').exists())
assert held()
(root/'first-stop').touch()
p.communicate(timeout=5)
assert held()
(root/'second-stop').touch()
q.communicate(timeout=5)
until(lambda: not held())

# Background child closes inherited fds, creates a new session, and outlives
# the shell. Guardian subreaping, rather than fd inheritance alone, holds SH.
child_script = root / 'background.py'
child_script.write_text('import os,time,pathlib\nos.setsid()\nos.closerange(3,256)\np=pathlib.Path(__file__).parent\n(p/"background-start").touch()\nwhile not (p/"background-stop").exists(): time.sleep(.01)\n')
p = spawn('/usr/bin/python3 background.py > /dev/null 2>&1 & exit 9')
until(lambda: (root/'background-start').exists())
assert p.poll() is None and held()
(root/'background-stop').touch()
p.communicate(timeout=5)
assert p.returncode == 9
until(lambda: not held())

# Cancellation during lock wait never starts the body, including SIGKILL of
# the entire CLI-owned shell proxy process group.
for sig in (signal.SIGTERM, signal.SIGKILL):
    with lock.open('a') as fd:
        fcntl.flock(fd, fcntl.LOCK_EX)
        before = len(events())
        p = spawn('touch must-not-run')
        until(lambda: len(events()) > before)
        os.killpg(p.pid, sig)
        p.communicate(timeout=5)
    assert not (root/'must-not-run').exists()

# Killing the proxy while a detached child ignores TERM and closes descriptors
# still kills/reaps the child BEFORE releasing the benchmark lease.
child_script.write_text('import os,time,pathlib,signal\nos.setsid()\nos.closerange(3,256)\nsignal.signal(signal.SIGTERM,signal.SIG_IGN)\np=pathlib.Path(__file__).parent\n(p/"cancel-child-pid").write_text(str(os.getpid()))\nwhile True: time.sleep(.01)\n')
p = spawn('/usr/bin/python3 background.py > /dev/null 2>&1 & wait')
until(lambda: (root/'cancel-child-pid').exists())
child_pid = int((root/'cancel-child-pid').read_text())
assert held()
os.killpg(p.pid, signal.SIGKILL)
p.communicate(timeout=5)
until(lambda: not held())
assert not Path('/proc/%d' % child_pid).exists()

# The shell sees its own call group and provider, and runs with crash dumps contained (inherited filter 0).
p = subprocess.run([str(wrapper), '-c', 'test "$GENDB_BASH_CALL_GROUP" = "$(ps -o pgid= -p $$ | tr -d " ")" && test "$GENDB_AUTHOR_PROVIDER_PID" = "$PPID_OF_TEST"; cat /proc/self/coredump_filter'],
                   capture_output=True, timeout=5, env=dict(os.environ, PPID_OF_TEST=str(os.getpid())))
assert (p.returncode, p.stdout) == (0, b'00000000\n'), p

# A call moved to the background keeps its group: TERM to that group stops the whole call, and the guardian kills
# and reaps a detached child that ignores TERM before releasing the lease (the author's exact-group stop route).
(root/'group_child.py').write_text(child_script.read_text().replace('cancel-child-pid', 'group-child-pid'))
p = spawn('echo $GENDB_BASH_CALL_GROUP > call-group; /usr/bin/python3 group_child.py > /dev/null 2>&1 & wait')
until(lambda: (root/'group-child-pid').exists() and (root/'call-group').exists())
child_pid = int((root/'group-child-pid').read_text())
assert held()
os.killpg(int((root/'call-group').read_text()), signal.SIGTERM)
p.communicate(timeout=5)
assert p.returncode == 143, p.returncode
until(lambda: not held())
assert not Path('/proc/%d' % child_pid).exists()

# Outer author timeout kills the provider group, whereas Claude's shell is
# detached. Parent-death handling must close the proxy even in this case.
child_script.write_text(child_script.read_text().replace('cancel-child-pid', 'provider-child-pid'))
provider = subprocess.Popen(['/usr/bin/python3', '-c',
    'import subprocess,sys,time; subprocess.Popen([sys.argv[1],"-c","/usr/bin/python3 background.py > /dev/null 2>&1 & wait"],start_new_session=True); time.sleep(60)',
    str(wrapper)], cwd=root, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
    stderr=subprocess.DEVNULL, start_new_session=True)
until(lambda: (root/'provider-child-pid').exists())
child_pid = int((root/'provider-child-pid').read_text())
assert held()
os.killpg(provider.pid, signal.SIGKILL)
provider.wait(timeout=5)
until(lambda: not held())
assert not Path('/proc/%d' % child_pid).exists()

# Bash never receives scheduling authority from command text. Exact, quoted,
# expanded and compound forms all retain the same shared reservation. The actual
# typed MCP client is a sibling process and can acquire EX once Bash quiesces.
tool = root / 'framework-tool-fixture'
tool.write_text('#!/usr/bin/python3\nimport fcntl,json,pathlib\np=pathlib.Path(__file__).parent\nf=open(json.loads((p/"activity-config.json").read_text())["activity_lock"],"a")\ntry:\n fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);print("exclusive")\nexcept BlockingIOError: print("shared")\n')
tool.chmod(0o700)
config = json.loads((root/'activity-config.json').read_text())
(root/'activity-config.json').write_text(json.dumps(config))
command = str(tool) + ' author-tools trial context candidate work'
p = spawn(command)
assert p.communicate(timeout=5) == (b'shared\n',b'') and p.returncode == 0
p = spawn(command + '; true')
assert p.communicate(timeout=5) == (b'shared\n',b'') and p.returncode == 0
# Quoting and expansion cannot change the lease.
for action in ('check', 'compile', 'trial', 'profile'):
    p = spawn(str(tool) + ' author-tools ' + action + ' context candidate "$TMPDIR/work"')
    assert p.communicate(timeout=5) == (b'shared\n',b'') and p.returncode == 0
    p = spawn(str(tool) + ' author-tools ' + action + ' context candidate "' + str(root/'literal work') + '"')
    assert p.communicate(timeout=5) == (b'shared\n',b'') and p.returncode == 0
assert all(e.get('scheduling_owner') == 'bash_shared_activity' and e.get('coredump_filter') == '00000000'
           for e in events() if e.get('phase') == 'acquired')
# Model the sibling structured-tool process: no wrapper/client shared lease.
assert subprocess.run([str(tool)],capture_output=True,timeout=5).stdout == b'exclusive\n'

records = events()
assert any(e.get('wait_ns', 0) > 50_000_000 for e in records)
assert any(e.get('cancelled') for e in records)
assert all(not set(e).intersection({'argv', 'command', 'environment', 'stdout', 'stderr'}) for e in records)
print(json.dumps({'status':'passed','cases':13,'elapsed_seconds':time.monotonic()-started,
                  'events':str(root/'tool-activity'), 'paid_calls':0}))
