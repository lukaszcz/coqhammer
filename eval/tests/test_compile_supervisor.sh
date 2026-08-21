#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
supervisor="$script_dir/../tools/rocq-compile-supervisor.sh"
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT HUP INT TERM

fail() {
  echo "test_compile_supervisor: $*" >&2
  exit 1
}

run_status() {
  set +e
  "$@"
  RUN_STATUS=$?
  set -e
}

output=$(
  "$supervisor" --timeout 2 --grace 1 --phase init \
    --source 'problems/a file.v' -- printf 'compiled\n'
)
[ "$output" = compiled ] || fail "successful command output was not preserved"

for expected in 7 124 137; do
  run_status "$supervisor" --timeout 2 --grace 1 --phase check \
    --source ordinary.v -- bash -c "exit $expected"
  [ "$RUN_STATUS" -eq "$expected" ] ||
    fail "ordinary exit $expected became $RUN_STATUS"
done

run_status "$supervisor" --timeout 1 --grace 1 --phase gen-atp \
  --source problems/equations-examples/POPLMark1a.v -- sleep 30 \
  >"$tmp/timeout.out" 2>"$tmp/timeout.err"
[ "$RUN_STATUS" -eq 124 ] || fail "timeout exited $RUN_STATUS instead of 124"
grep -Fq 'rocq-compile-supervisor: TIMEOUT' "$tmp/timeout.err" ||
  fail "timeout diagnostic was missing"
grep -Fq 'phase=gen-atp' "$tmp/timeout.err" || fail "diagnostic omitted phase"
grep -Fq 'source=problems/equations-examples/POPLMark1a.v' "$tmp/timeout.err" ||
  fail "diagnostic omitted source filename"
grep -Fq 'limit=1s grace=1s exit=124' "$tmp/timeout.err" ||
  fail "diagnostic omitted timeout policy/status"
grep -Fq 'KILLED' "$tmp/timeout.err" &&
  fail "a genuine timeout was reported as a premature kill"
grep -Fq 'invalid command status record' "$tmp/timeout.err" &&
  fail "the interrupted record leaked out of the timeout path"

# A command process killed well before the budget expires - the OOM killer is
# the reason that matters in the grids - must be reported as a kill, never
# folded into the timeout bucket. The command kills its own parent, the private
# wrapper, so that no completion record is ever written.
run_status "$supervisor" --timeout 30 --grace 1 --phase check \
  --source problems/oom.v -- bash -c 'kill -KILL "$PPID"' \
  >"$tmp/killed.out" 2>"$tmp/killed.err"
[ "$RUN_STATUS" -ne 124 ] || fail "a premature kill was counted as a timeout"
[ "$RUN_STATUS" -eq 137 ] || fail "premature kill exited $RUN_STATUS instead of 137"
grep -Fq 'rocq-compile-supervisor: KILLED' "$tmp/killed.err" ||
  fail "premature-kill diagnostic was missing"
grep -Fq 'phase=check source=problems/oom.v' "$tmp/killed.err" ||
  fail "premature-kill diagnostic omitted phase/source"
grep -Eq 'elapsed=[0-9]+\.[0-9][0-9]s' "$tmp/killed.err" ||
  fail "premature-kill diagnostic omitted the elapsed time"
grep -Fq 'out-of-memory' "$tmp/killed.err" ||
  fail "premature-kill diagnostic omitted the likely cause"
grep -Fq 'TIMEOUT' "$tmp/killed.err" &&
  fail "premature kill also emitted a timeout diagnostic"
grep -Fq 'invalid command status record' "$tmp/killed.err" &&
  fail "premature kill was reported as an invalid status record"

cat > "$tmp/resistant-tree.sh" <<'SCRIPT'
#!/usr/bin/env bash
trap '' TERM
(
  trap '' TERM
  while :; do sleep 30; done
) &
echo "$!" > "$1"
while :; do sleep 30; done
SCRIPT
chmod +x "$tmp/resistant-tree.sh"
# The budget is larger than one second so that the elapsed-time rule has to
# recognize a real overrun rather than accept every measurement.
run_status "$supervisor" --timeout 2 --grace 1 --phase reconstruction \
  --source descendant.v -- "$tmp/resistant-tree.sh" "$tmp/descendant.pid" \
  >"$tmp/tree.out" 2>"$tmp/tree.err"
[ "$RUN_STATUS" -eq 124 ] || fail "TERM-resistant tree exited $RUN_STATUS"
grep -Fq 'rocq-compile-supervisor: TIMEOUT' "$tmp/tree.err" ||
  fail "a command killed by --kill-after lost its timeout diagnostic"
grep -Fq 'KILLED' "$tmp/tree.err" &&
  fail "a real overrun killed by --kill-after was reported as a premature kill"
grep -Fq 'invalid command status record' "$tmp/tree.err" &&
  fail "the interrupted record leaked out of the --kill-after path"
descendant=$(cat "$tmp/descendant.pid")
for _ in 1 2 3 4 5 6 7 8 9 10; do
  kill -0 "$descendant" 2>/dev/null || break
  sleep 0.1
done
if kill -0 "$descendant" 2>/dev/null; then
  fail "TERM-resistant descendant $descendant survived process-group KILL"
fi

# Signals delivered to the supervisor itself must be forwarded immediately,
# must still escalate for resistant descendants, and must retain shell-standard
# statuses. The grace period is deliberately huge: once the supervised command
# has returned, only the wrapper's own resistance is left, and waiting it out
# would make every interrupted file cost the full grace. Python starts the
# supervisor without the SIGINT-ignore disposition that a non-interactive shell
# gives its own asynchronous children.
cat > "$tmp/signalled-tree.sh" <<'SCRIPT'
#!/usr/bin/env bash
set -u
pid_file=$1
signal_file=$2
trap 'printf "HUP\n" > "$signal_file"; exit 0' HUP
trap 'printf "INT\n" > "$signal_file"; exit 0' INT
trap 'printf "TERM\n" > "$signal_file"; exit 0' TERM
(
  trap '' HUP INT TERM
  while :; do sleep 30; done
) &
descendant=$!
printf '%s %s\n' "$$" "$descendant" > "$pid_file"
while :; do sleep 30; done
SCRIPT
chmod +x "$tmp/signalled-tree.sh"
mkdir "$tmp/supervisor-state"
python3 - "$supervisor" "$tmp/signalled-tree.sh" \
    "$tmp/supervisor-state" "$tmp" <<'PY'
import os
import pathlib
import signal
import stat
import subprocess
import sys
import time

supervisor, command, state_root_arg, output_root_arg = sys.argv[1:]
state_root = pathlib.Path(state_root_arg)
output_root = pathlib.Path(output_root_arg)

def wait_for(predicate, message, timeout=5):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.02)
    raise SystemExit(message)

def process_is_live(pid):
    try:
        state = pathlib.Path(f"/proc/{pid}/stat").read_text().split()[2]
    except FileNotFoundError:
        return False
    return state != "Z"

for name, sig, expected in (
    ("HUP", signal.SIGHUP, 129),
    ("INT", signal.SIGINT, 130),
    ("TERM", signal.SIGTERM, 143),
):
    pid_file = output_root / f"external-{name}.pids"
    signal_file = output_root / f"external-{name}.signal"
    env = os.environ.copy()
    env["TMPDIR"] = str(state_root)
    process = subprocess.Popen(
        [
            supervisor,
            "--timeout", "30",
            "--grace", "300",
            "--phase", "external-signal",
            "--source", f"{name}.v",
            "--", command, str(pid_file), str(signal_file),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
    )
    wait_for(pid_file.exists, f"{name}: supervised command did not start")
    wait_for(lambda: len(list(state_root.glob("rocq-compile-supervisor.*"))) == 1,
             f"{name}: private supervisor state directory was not created")
    state_dir, = state_root.glob("rocq-compile-supervisor.*")
    if stat.S_IMODE(state_dir.stat().st_mode) != 0o700:
        raise SystemExit(f"{name}: supervisor state directory is not mode 0700")
    status_file = state_dir / "status"
    if not status_file.is_file() or status_file.read_text() != "running\n":
        raise SystemExit(f"{name}: secure retained status sentinel is missing")
    if stat.S_IMODE(status_file.stat().st_mode) != 0o600:
        raise SystemExit(f"{name}: status sentinel is not mode 0600")

    started = time.monotonic()
    os.kill(process.pid, sig)
    wait_for(signal_file.exists, f"{name}: signal was not forwarded to the command")
    if process.poll() is None:
        # A second external signal must escalate, not be swallowed by a trap.
        os.kill(process.pid, sig)
    stdout, stderr = process.communicate(timeout=10)
    elapsed = time.monotonic() - started
    if process.returncode != expected:
        raise SystemExit(
            f"{name}: supervisor returned {process.returncode}, expected {expected}; "
            f"stdout={stdout!r}, stderr={stderr!r}"
        )
    if elapsed > 5:
        raise SystemExit(
            f"{name}: supervisor took {elapsed:.1f}s, close to the 300s grace period"
        )
    if "invalid command status record" in stderr:
        raise SystemExit(
            f"{name}: the interrupted record leaked out as an invalid record; "
            f"stderr={stderr!r}"
        )
    if signal_file.read_text().strip() != name:
        raise SystemExit(f"{name}: command recorded the wrong forwarded signal")
    pids = [int(value) for value in pid_file.read_text().split()]
    wait_for(lambda: not any(process_is_live(pid) for pid in pids),
             f"{name}: a supervised descendant survived process-group cleanup")
    wait_for(lambda: not any(state_root.iterdir()),
             f"{name}: supervisor state was not cleaned")
PY

# Simulate a signal trap running with identity retained after wait/reap while
# /proc already exposes a replacement process under the old PID and PGID. The
# fake kill function makes this deterministic and guarantees the regression
# test cannot signal any real, unrelated process.
fake_proc="$tmp/fake-proc"
mkdir -p "$fake_proc/4242"
python3 - "$fake_proc/4242/stat" <<'PY'
import pathlib
import sys

# Fields after comm: state, ppid, pgrp, session, ..., starttime (index 19).
fields = ["S", "1", "4242", "222"] + ["0"] * 15 + ["999", "0"]
pathlib.Path(sys.argv[1]).write_text(f"4242 (reused monitor) {' '.join(fields)}\n")
PY
set +e
(
  # Sourcing exposes only helpers; supervisor_main is guarded by BASH_SOURCE.
  # shellcheck source=eval/tools/rocq-compile-supervisor.sh
  source "$supervisor"
  proc_root=$fake_proc
  monitor_pid=4242
  monitor_starttime=111
  monitor_session=222
  monitor_pgid=4242
  grace_seconds=1
  state_dir=
  kill() {
    printf 'unsafe kill: %s\n' "$*" >> "$tmp/fake-kill.log"
  }
  handle_external_signal TERM 143
)
identity_status=$?
set -e
[ "$identity_status" -eq 143 ] ||
  fail "identity-mismatch trap exited $identity_status instead of 143"
[ ! -e "$tmp/fake-kill.log" ] ||
  fail "identity-mismatch trap attempted to signal a reused PID/PGID"

expect_usage_error() {
  local output status
  set +e
  output=$("$supervisor" "$@" 2>&1)
  status=$?
  set -e
  [ "$status" -eq 2 ] || fail "invalid arguments exited $status: $*"
  [[ "$output" == *Usage:* ]] || fail "invalid arguments omitted usage: $*"
}
expect_usage_error
expect_usage_error --timeout
expect_usage_error --timeout 0 --grace 1 --phase x --source x -- true
expect_usage_error --timeout nope --grace 1 --phase x --source x -- true
expect_usage_error --timeout 1 --grace 0 --phase x --source x -- true
expect_usage_error --timeout 1 --grace 1 --phase x --source x --
expect_usage_error --timeout 1 --grace 1 --source x -- true
expect_usage_error --unknown value

"$supervisor" --help | grep -Fq \
  'Usage: rocq-compile-supervisor.sh --timeout SEC --grace SEC' ||
  fail "help output drifted"

# All grid front ends expose the same policy, and reject missing/non-positive
# values before touching installs or checkpoints.
for driver in run-screening-grid.sh run-premise-screening-grid.sh \
    run-confirmation-grid.sh run-dry-sample.sh; do
  help=$("$script_dir/../$driver" --help)
  [[ "$help" == *'--compile-timeout'*'600'* ]] ||
    fail "$driver omitted the compile timeout/default"
  [[ "$help" == *'--compile-timeout-grace'* ]] ||
    fail "$driver omitted the compile grace"
done
for driver in run-screening-grid.sh run-premise-screening-grid.sh \
    run-confirmation-grid.sh; do
  run_status "$script_dir/../$driver" --compile-timeout 0 >/dev/null 2>&1
  [ "$RUN_STATUS" -eq 2 ] || fail "$driver accepted zero compile timeout"
  run_status "$script_dir/../$driver" --compile-timeout-grace nope >/dev/null 2>&1
  [ "$RUN_STATUS" -eq 2 ] || fail "$driver accepted invalid compile grace"
  run_status "$script_dir/../$driver" --compile-timeout >/dev/null 2>&1
  [ "$RUN_STATUS" -eq 2 ] || fail "$driver accepted a missing timeout value"
done
run_status "$script_dir/../run-dry-sample.sh" --label x --corpus x \
  --compile-timeout 0 >/dev/null 2>&1
[ "$RUN_STATUS" -eq 2 ] || fail "run-dry-sample.sh accepted zero compile timeout"

python3 - "$script_dir/../Makefile" "$script_dir/../grid-engine.sh" \
    "$script_dir/../run-confirmation-grid.sh" \
    "$script_dir/../run-dry-sample.sh" <<'PY'
import pathlib
import sys

makefile, engine, confirmation, dry = (
    pathlib.Path(path).read_text() for path in sys.argv[1:]
)
if makefile.count("$(SUPERVISED_COQC) --source") != 5:
    raise SystemExit("not every eval Makefile Rocq recipe is supervised")
for phase, target in (("init", "init"), ("check", "check"), ("gen-atp", "atp")):
    if f"run_compile_make {phase} {target}" not in engine:
        raise SystemExit(f"declarative engine omitted supervised {phase}")
    if f"run_compile_make {phase} {target}" not in confirmation:
        raise SystemExit(f"confirmation grid omitted supervised {phase}")
    if f"run_compile_make {phase} {target}" not in dry:
        raise SystemExit(f"dry sample omitted supervised {phase}")
if "run_compile_make reconstruction reconstr" not in confirmation:
    raise SystemExit("confirmation grid omitted supervised reconstruction")
if "run_compile_make reconstruction reconstr" not in dry:
    raise SystemExit("dry sample omitted supervised reconstruction")
if "compile-supervisor" not in engine or "compile_supervisor_sha256" not in engine:
    raise SystemExit("engine omitted supervisor hash provenance")
if "compile-supervisor" not in confirmation or "hash_harness_sources" not in confirmation:
    raise SystemExit("confirmation omitted supervisor composite provenance")
if "ls-files --error-unmatch" not in confirmation:
    raise SystemExit("confirmation dirty guard omitted the supervisor")
PY

echo "test_compile_supervisor: ok"
