#!/usr/bin/python3
"""GenDB's Bash guardian for one author call (Linux). Arguments and stdio belong to /bin/bash.

Claude Code runs every Bash tool call through this file (CLAUDE_CODE_SHELL). Three processes cooperate:

- the proxy: the process Claude Code starts. It dies with the provider (PR_SET_PDEATHSIG), forwards the shell's exit
  status, and on SIGTERM/SIGINT/SIGHUP (or its own death) cancels the guardian through a pipe;
- the guardian: in its own session (a process-group kill of the provider's shell does not reach it) and a child
  subreaper, so background grandchildren that close inherited descriptors or call setsid stay its descendants. It
  queues for a SHARED lease on the run's activity lock, runs the shell, reaps every descendant, and only then
  releases the lease. On cancellation (the proxy's pipe closing, or SIGTERM to the guardian itself, for example
  `kill -TERM -- -<group>` of the call's process group) it never starts the shell, or kills and reaps every
  descendant first;
- the shell: /bin/bash with the original arguments, in the guardian's process group, with GENDB_BASH_CALL_GROUP (that
  group, which a call moved to the background by the provider keeps) and GENDB_AUTHOR_PROVIDER_PID (the provider
  process: the author's own process tree starts there).

Crash dumps: the guardian writes 0 to /proc/self/coredump_filter before the shell starts (inherited across fork and
exec, this process tree only), so a crash is still reported by the host's crash handler but its dump holds no memory
mappings. The value read back, or the error, is recorded in the `acquired` event.

Bash is an untyped subprocess boundary: it always holds the conservative shared lease and never gains scheduling
authority from its command text. Structured local jobs use the sibling MCP transport and take their own leases.
Only lifecycle metadata is recorded, never shell arguments or environment.
"""
import ctypes
import fcntl
import json
import os
from pathlib import Path
import select
import signal
import sys
import time

PR_SET_PDEATHSIG = 1
PR_SET_CHILD_SUBREAPER = 36
EXIT_GUARDIAN_FAILURE = 125
EXIT_CANCELLED = 143
LIBC = ctypes.CDLL(None, use_errno=True)


def exit_like(code):
    """Exit with a shell-style status: a negative code re-raises that signal."""
    if code < 0:
        signal.signal(-code, signal.SIG_DFL)
        os.kill(os.getpid(), -code)
    os._exit(code if code >= 0 else 128 - code)


def main():
    # Kill this proxy with the provider even though Claude Code detaches its shell from the provider's process group
    # (the outer author wall guard kills only that group). Fork clears PDEATHSIG, so the guardian survives the proxy.
    provider = os.getppid()
    if LIBC.prctl(PR_SET_PDEATHSIG, signal.SIGKILL, 0, 0, 0) != 0:
        return EXIT_GUARDIAN_FAILURE
    if os.getppid() != provider:  # the provider died before the death signal was armed
        return EXIT_CANCELLED
    shell_dir = Path(__file__).resolve().parent
    config = json.loads((shell_dir / 'activity-config.json').read_text())
    watch, alive = os.pipe2(os.O_CLOEXEC)
    guardian = os.fork()
    if guardian:
        os.close(watch)
        return proxy(guardian, alive)
    os.close(alive)
    guard(shell_dir, config['activity_lock'], watch, provider)


def proxy(guardian, alive):
    """Wait for the guardian and return its status. Closing `alive` cancels it: the kernel closes it when this
    process is killed; ordinary termination signals close it here."""
    open_fds = [alive]

    def cancel(signum, frame):
        if open_fds:
            os.close(open_fds.pop())
    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(sig, cancel)
    _, status = os.waitpid(guardian, 0)
    if open_fds:
        os.close(open_fds.pop())
    return os.waitstatus_to_exitcode(status)


class EventLog:
    """One JSON-lines file of lifecycle events for this Bash invocation."""

    def __init__(self, directory):
        path = directory / ('%d-%d.jsonl' % (os.getpid(), time.time_ns()))
        self.file = path.open('x', buffering=1)

    def record(self, phase, **fields):
        self.file.write(json.dumps(dict(phase=phase, unix_ns=time.time_ns(), monotonic_ns=time.monotonic_ns(),
                                        pid=os.getpid(), **fields)) + '\n')

    def close(self):
        self.file.close()


TERMINATED = []


def on_terminate(signum, frame):
    TERMINATED.append(signum)


def cancelled(watch):
    return bool(TERMINATED) or bool(select.select([watch], [], [], 0)[0])


def contain_crash_dumps():
    """Dump no memory mappings on a crash of this process tree; returns (value read back, error)."""
    path = Path('/proc/self/coredump_filter')
    try:
        path.write_text('0')
        return path.read_text().strip(), None
    except OSError as error:
        return None, str(error)


def guard(shell_dir, activity_lock, watch, provider):
    os.setsid()  # a process-group kill of the provider's shell must not release the lease early
    if LIBC.prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) != 0:
        os._exit(EXIT_GUARDIAN_FAILURE)
    signal.signal(signal.SIGTERM, on_terminate)  # a TERM to this call's group stops the call like a cancellation
    coredump_filter, coredump_error = contain_crash_dumps()
    log = EventLog(shell_dir / 'tool-activity')
    queued = time.monotonic_ns()
    log.record('queued')
    lease = acquire_shared_lease(activity_lock, watch, log, queued)
    acquired = time.monotonic_ns()
    log.record('acquired', wait_ns=acquired - queued, scheduling_owner='bash_shared_activity',
               coredump_filter=coredump_filter, coredump_filter_error=coredump_error)
    # The inherited descriptor is an additional safeguard; the guardian owns the lease lifetime even when a
    # Python/compiler child closes unrelated descriptors.
    os.set_inheritable(lease, True)
    shell = os.fork()
    if shell == 0:
        os.close(watch)
        log.close()
        exec_bash(sys.argv[1:], provider)
    shell_status, stopped = reap_all_descendants(shell, watch)
    result = EXIT_CANCELLED if stopped else shell_status if shell_status is not None else EXIT_GUARDIAN_FAILURE
    log.record('finished', execution_ns=time.monotonic_ns() - acquired,
               shell_exit_code=shell_status, exit_code=result, cancelled=stopped)
    # Closing (never an explicit LOCK_UN) releases the lease only when every inherited owner has exited too; every
    # descendant has been reaped above.
    os.close(lease)
    exit_like(result)


def acquire_shared_lease(activity_lock, watch, log, queued):
    """Block until the shared lease is held; a cancellation while queued exits without starting the shell. The lease
    is taken through the timing gate (`<activity_lock>.gate`, shared, released once the lease is held), so a waiting
    timed measurement (which holds the gate exclusively) is not starved by new shell work."""
    gate = os.open(activity_lock + '.gate', os.O_RDWR | os.O_CREAT, 0o600)
    lease = os.open(activity_lock, os.O_RDWR | os.O_CREAT, 0o600)
    for descriptor in (gate, lease):
        while True:
            if cancelled(watch):
                log.record('cancelled_before_acquire', wait_ns=time.monotonic_ns() - queued)
                os._exit(EXIT_CANCELLED)
            try:
                fcntl.flock(descriptor, fcntl.LOCK_SH | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                select.select([watch], [], [], 0.05)
    os.close(gate)
    return lease


def exec_bash(arguments, provider):
    for key in ('CLAUDE_CODE_SHELL', 'CLAUDE_CODE_SHELL_PREFIX'):
        os.environ.pop(key, None)  # nested shells are ordinary Bash, inside this lease
    os.environ['SHELL'] = '/bin/bash'
    os.environ['GENDB_AUTHOR_ACTIVITY_HELD'] = '1'
    os.environ['GENDB_BASH_CALL_GROUP'] = str(os.getpgrp())
    os.environ['GENDB_AUTHOR_PROVIDER_PID'] = str(provider)
    # Match subprocess restore_signals: Python ignores these internally, but Bash and pipelines need ordinary
    # signal and exit semantics.
    for name in ('SIGPIPE', 'SIGXFZ', 'SIGXFSZ'):
        if hasattr(signal, name):
            signal.signal(getattr(signal, name), signal.SIG_DFL)
    os.execv('/bin/bash', ['/bin/bash', *arguments])


def kill_descendants(pid):
    try:
        children = Path('/proc/%d/task/%d/children' % (pid, pid)).read_text().split()
    except FileNotFoundError:
        return
    for value in children:
        descendant = int(value)
        kill_descendants(descendant)
        try:
            os.kill(descendant, signal.SIGKILL)
        except ProcessLookupError:
            pass


def reap_all_descendants(shell, watch):
    """Reap the shell and every adopted descendant; after a cancellation, kill them first.
    Returns (shell exit status or None, whether cancelled)."""
    shell_status = None
    stopping = False
    while True:
        if cancelled(watch):
            stopping = True
        if stopping:
            kill_descendants(os.getpid())
        try:
            pid, status = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            return shell_status, stopping
        if pid == shell:
            shell_status = os.waitstatus_to_exitcode(status)
        if pid == 0:
            time.sleep(0.01)  # do not spin on a readable EOF during cancellation


if __name__ == '__main__':
    exit_like(main())
