#!/usr/bin/env bash
# Bound one per-file Rocq compilation and kill its whole process group.
# Signal and cleanup functions are invoked indirectly by traps.
# shellcheck disable=SC2317
set -u

proc_root=/proc
state_dir=
monitor_pid=
monitor_starttime=
monitor_session=
monitor_pgid=
sentinel_pid=
sentinel_starttime=
sentinel_session=
sentinel_pgid=
sentinel_file=
status_file=
command_start_cs=

# Elapsed wall time distinguishes a genuine budget overrun from an external
# SIGKILL, so it must come from a clock that cannot be stepped: /proc/uptime is
# the monotonic one a shell can read. Report centiseconds, and fall back to the
# shell's own second counter when /proc/uptime is unavailable.
monotonic_centiseconds() {
  local uptime seconds fraction
  if IFS=' ' read -r uptime _ < "$proc_root/uptime" 2>/dev/null; then
    seconds=${uptime%%.*}
    fraction=${uptime#*.}
    [ "$fraction" != "$uptime" ] || fraction=0
    fraction=${fraction}00
    fraction=${fraction:0:2}
    case "$seconds$fraction" in
      ''|*[!0-9]*) ;;
      *)
        printf '%s\n' "$((10#$seconds * 100 + 10#$fraction))"
        return 0
        ;;
    esac
  fi
  printf '%s\n' "$((SECONDS * 100))"
}

# Read the identity fields that remain stable for the lifetime of a Linux
# process. /proc/PID/stat puts the possibly parenthesized command first; strip
# through its final ") " before indexing the documented fields.
read_process_identity() {
  local pid="$1" stat_line stat_tail
  local -a fields
  [ -r "$proc_root/$pid/stat" ] || return 1
  IFS= read -r stat_line < "$proc_root/$pid/stat" || return 1
  stat_tail=${stat_line##*) }
  [ "$stat_tail" != "$stat_line" ] || return 1
  read -r -a fields <<< "$stat_tail"
  [ "${#fields[@]}" -ge 20 ] || return 1
  [ "${stat_line%% *}" = "$pid" ] || return 1
  PROCESS_STATE=${fields[0]}
  PROCESS_PGID=${fields[2]}
  PROCESS_SESSION=${fields[3]}
  PROCESS_STARTTIME=${fields[19]}
}

capture_monitor_identity() {
  local pid="$1"
  read_process_identity "$pid" || return 1
  monitor_pid=$pid
  monitor_starttime=$PROCESS_STARTTIME
  monitor_session=$PROCESS_SESSION
  monitor_pgid=$PROCESS_PGID
}

monitor_identity_matches() {
  [ -n "$monitor_pid" ] && [ -n "$monitor_starttime" ] || return 1
  read_process_identity "$monitor_pid" || return 1
  [ "$PROCESS_STARTTIME" = "$monitor_starttime" ] &&
    [ "$PROCESS_SESSION" = "$monitor_session" ] &&
    [ "$PROCESS_PGID" = "$monitor_pgid" ]
}

monitor_is_same_process() {
  [ -n "$monitor_pid" ] && [ -n "$monitor_starttime" ] || return 1
  read_process_identity "$monitor_pid" || return 1
  [ "$PROCESS_STARTTIME" = "$monitor_starttime" ] &&
    [ "$PROCESS_SESSION" = "$monitor_session" ]
}

# Terminal condition for the startup waits below: the monitor is gone from
# /proc, or Bash has reaped it, or it is a zombie awaiting our own wait. Any of
# those means no further polling can change what we observe.
monitor_has_exited() {
  monitor_is_same_process || return 0
  [ "$PROCESS_STATE" = Z ]
}

capture_sentinel_identity() {
  local pid starttime session pgid
  # Only the still-unreaped monitor may introduce its child as our anchor.
  # Never recapture a PID from the retained file after that identity is gone.
  monitor_is_same_process || return 1
  [ -s "$sentinel_file" ] || return 1
  IFS= read -r pid < "$sentinel_file" || return 1
  case "$pid" in ''|*[!0-9]*) return 1 ;; esac
  read_process_identity "$pid" || return 1
  starttime=$PROCESS_STARTTIME
  session=$PROCESS_SESSION
  pgid=$PROCESS_PGID
  [ "$session" = "$monitor_session" ] && [ "$pgid" = "$monitor_pid" ] || return 1
  sentinel_pid=$pid
  sentinel_starttime=$starttime
  sentinel_session=$session
  sentinel_pgid=$pgid
}

sentinel_identity_matches() {
  [ -n "$sentinel_pid" ] && [ -n "$sentinel_starttime" ] || return 1
  read_process_identity "$sentinel_pid" || return 1
  [ "$PROCESS_STARTTIME" = "$sentinel_starttime" ] &&
    [ "$PROCESS_SESSION" = "$sentinel_session" ] &&
    [ "$PROCESS_PGID" = "$sentinel_pgid" ]
}

group_identity_matches() {
  monitor_identity_matches || sentinel_identity_matches
}

# timeout moves itself into a process group whose PGID is its PID. Accept only
# that one expected transition from the identity captured immediately after
# fork; never adopt an arbitrary group observed under a stale/reused PID.
monitor_adopt_own_process_group() {
  monitor_is_same_process || return 1
  [ "$PROCESS_PGID" = "$monitor_pid" ] || return 1
  monitor_pgid=$PROCESS_PGID
}

process_group_exists() {
  [ "$monitor_pgid" = "$monitor_pid" ] && group_identity_matches &&
    kill -0 -- "-$monitor_pgid" 2>/dev/null
}

signal_process_group() {
  local signal="$1"
  # Validate immediately before every signal. If wait has reaped the monitor
  # and Linux has reused its PID/PGID, starttime/session/PGID cannot all match,
  # so neither the replacement process nor its group is touched. The inner
  # monitor is a signal-resistant identity anchor while descendants remain.
  if [ "$monitor_pgid" = "$monitor_pid" ] && group_identity_matches; then
    kill -s "$signal" -- "-$monitor_pgid" 2>/dev/null || true
  fi
  if monitor_identity_matches; then
    kill -s "$signal" "$monitor_pid" 2>/dev/null || true
  fi
  monitor_adopt_own_process_group || true
  if [ "$monitor_pgid" = "$monitor_pid" ] && group_identity_matches; then
    kill -s "$signal" -- "-$monitor_pgid" 2>/dev/null || true
  fi
}

# Once the monitor has been reaped its PID is eligible for reuse, so no later
# trap may act on the retained identity.
forget_supervised_identity() {
  monitor_pid=
  monitor_starttime=
  monitor_session=
  monitor_pgid=
  sentinel_pid=
  sentinel_starttime=
  sentinel_session=
  sentinel_pgid=
}

# The inner wrapper records that the supervised command itself has returned
# before it parks as a deliberate signal-resistant anchor. Once either record
# is present, nothing worth waiting for is left in the process group.
supervised_command_finished() {
  [ -n "$status_file" ] || return 1
  grep -Eq '^(done|interrupted):' -- "$status_file" 2>/dev/null
}

# A trap can run before supervisor_main has recorded the monitor it just
# started. $! is already set in that narrow interval, so the identity can still
# be recovered from it; the sentinel is only ever introduced by a live monitor.
recover_supervised_identity() {
  local latest_pid="$1"
  if [ -z "$monitor_pid" ] && [ -n "$latest_pid" ]; then
    capture_monitor_identity "$latest_pid" || true
  elif [ -n "$monitor_pid" ] && [ -z "$monitor_starttime" ]; then
    capture_monitor_identity "$monitor_pid" || true
  fi
  [ -n "$sentinel_starttime" ] || capture_sentinel_identity || true
}

# A second external signal must escalate rather than be swallowed: kill the
# group outright and end the wait. The blanket trap installed first keeps any
# further signal from re-entering either handler.
escalate_external_signal() {
  local status="$1" latest_pid=${!:-}
  trap '' HUP INT TERM
  recover_supervised_identity "$latest_pid"
  if group_identity_matches; then
    signal_process_group KILL
    wait "$monitor_pid" 2>/dev/null || true
  fi
  forget_supervised_identity
  exit "$status"
}

handle_external_signal() {
  local signal="$1" status="$2" attempts latest_pid=${!:-}
  trap 'escalate_external_signal 129' HUP
  trap 'escalate_external_signal 130' INT
  trap 'escalate_external_signal 143' TERM
  recover_supervised_identity "$latest_pid"
  if group_identity_matches; then
    signal_process_group "$signal"
    # Stop waiting as soon as the command itself is gone: what remains in the
    # group is then only the wrapper's deliberate resistance, which would
    # otherwise burn the whole grace period on every interrupted file.
    attempts=$((grace_seconds * 10))
    while [ "$attempts" -gt 0 ] && process_group_exists &&
      ! supervised_command_finished; do
      sleep 0.1
      attempts=$((attempts - 1))
    done
    if process_group_exists; then
      signal_process_group KILL
    fi
    # Reap the timeout monitor even when it exited before a resistant
    # descendant exhausted the grace period.
    wait "$monitor_pid" 2>/dev/null || true
  fi
  forget_supervised_identity
  exit "$status"
}

cleanup() {
  [ -z "$state_dir" ] || rm -rf -- "$state_dir"
}

usage() {
  cat <<'USAGE'
Usage: rocq-compile-supervisor.sh --timeout SEC --grace SEC \
         --phase PHASE --source FILE -- COMMAND [ARG ...]

Run COMMAND for at most SEC seconds. On expiry GNU timeout sends TERM to the
command process group, waits GRACE seconds, then sends KILL. A timeout is
reported on stderr and exits 124. A command process that is killed by a signal
before the time budget expires -- typically by the out-of-memory killer -- is
reported separately on stderr and exits 137, so that it is never counted as a
timeout. Otherwise COMMAND's exit status is preserved. External HUP, INT, and
TERM are forwarded to the process group and produce statuses 129, 130, and 143
after the group has been terminated; a second external signal kills the group
at once instead of waiting out GRACE. SEC and GRACE must be positive integers.
USAGE
}

fail_usage() {
  echo "rocq-compile-supervisor: $*" >&2
  usage >&2
  exit 2
}

# The reported policy fields are set by supervisor_main before any report.
# shellcheck disable=SC2154
report_timeout() {
  printf 'rocq-compile-supervisor: TIMEOUT phase=%s source=%s limit=%ss grace=%ss exit=124\n' \
    "$phase" "$source_file" "$timeout_seconds" "$grace_seconds" >&2
}

supervisor_main() {
  timeout_seconds=
  grace_seconds=
  phase=
  source_file=
  while [ "$#" -gt 0 ]; do
  case "$1" in
    --timeout)
      [ "$#" -ge 2 ] || fail_usage "missing value for --timeout"
      timeout_seconds=$2
      shift 2
      ;;
    --grace)
      [ "$#" -ge 2 ] || fail_usage "missing value for --grace"
      grace_seconds=$2
      shift 2
      ;;
    --phase)
      [ "$#" -ge 2 ] || fail_usage "missing value for --phase"
      phase=$2
      shift 2
      ;;
    --source)
      [ "$#" -ge 2 ] || fail_usage "missing value for --source"
      source_file=$2
      shift 2
      ;;
    --)
      shift
      break
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *) fail_usage "unknown argument: $1" ;;
  esac
  done

case "$timeout_seconds" in
  ''|*[!0-9]*|0*) fail_usage "--timeout must be a positive integer" ;;
esac
case "$grace_seconds" in
  ''|*[!0-9]*|0*) fail_usage "--grace must be a positive integer" ;;
esac
[ -n "$phase" ] || fail_usage "--phase must not be empty"
[ -n "$source_file" ] || fail_usage "--source must not be empty"
[ "$#" -gt 0 ] || fail_usage "missing command after --"
command -v timeout >/dev/null 2>&1 || {
  echo "rocq-compile-supervisor: GNU timeout is required" >&2
  exit 125
}
# One fork rather than the three a `timeout --version | head | grep` pipeline
# costs: the supervisor runs once per source file per phase, so a whole grid
# pays this check tens of thousands of times.
case "$(timeout --version 2>/dev/null)" in
  *'GNU coreutils'*) ;;
  *)
    echo "rocq-compile-supervisor: GNU timeout from coreutils is required" >&2
    exit 125
    ;;
esac

# The status path is never exposed in a shared directory or unlinked while the
# monitor is live. The private directory makes both the retained sentinel and
# the eventual status record immune to replacement by another user.
state_dir=$(mktemp -d "${TMPDIR:-/tmp}/rocq-compile-supervisor.XXXXXXXX") || exit 125
chmod 0700 -- "$state_dir" || {
  rm -rf -- "$state_dir"
  exit 125
}
status_file=$state_dir/status
sentinel_file=$state_dir/sentinel
(umask 077 && printf 'running\n' > "$status_file") || {
  rm -rf -- "$state_dir"
  exit 125
}
trap cleanup EXIT

trap 'handle_external_signal HUP 129' HUP
trap 'handle_external_signal INT 130' INT
trap 'handle_external_signal TERM 143' TERM

# The retained "running" sentinel distinguishes an actual timeout from a
# command that ordinarily returns 124 or 137. The inner Bash changes it to a
# completion record only after COMMAND has returned; all paths are private.
# If timeout sends TERM, keep its direct child alive until --kill-after fires:
# otherwise a TERM-resistant grandchild could remain after the direct child
# exits and timeout decides that its job is finished. Before parking, it
# records "interrupted" so that the supervisor knows the command has returned
# and only the deliberate anchor is left.
# The start time is taken before the fork: measuring more elapsed time than
# actually elapsed can only classify a kill as the timeout it may well be.
command_start_cs=$(monotonic_centiseconds)
# shellcheck disable=SC2016
# Bash starts asynchronous children with INT ignored when job control is off.
# Reset external-signal dispositions before timeout starts so INT can actually
# reach Rocq just like HUP and TERM.
env --default-signal=HUP,INT,TERM \
  timeout --signal=TERM --kill-after="$grace_seconds" "$timeout_seconds" \
  bash -c '
    status_file=$1
    sentinel_file=$2
    shift 2
    interrupted=false
    trap '\''interrupted=true'\'' HUP INT TERM
    printf "%s\n" "$$" > "$sentinel_file"
    env --default-signal=HUP,INT,TERM "$@" &
    command_pid=$!
    wait "$command_pid"
    command_status=$?
    if [ "$interrupted" = true ]; then
      trap "" HUP INT TERM
      printf "interrupted:%s\n" "$command_status" > "$status_file"
      while :; do
        sleep 3600 &
        wait "$!" || true
      done
    fi
    printf "done:%s\n" "$command_status" > "$status_file"
    exit "$command_status"
  ' bash "$status_file" "$sentinel_file" "$@" &
monitor_pid=$!
if ! capture_monitor_identity "$monitor_pid"; then
  wait "$monitor_pid" 2>/dev/null || true
  trap - HUP INT TERM
  echo "rocq-compile-supervisor: cannot capture timeout process identity" >&2
  exit 125
fi
# Normally timeout has already called setpgid by the first read. Keep the
# captured starttime/session while waiting for that sole safe PGID. Poll until
# an event settles the question rather than for a fixed number of ticks: a
# tick budget is really a bet on how promptly this shell is rescheduled, and a
# loaded machine loses that bet. The group matters only for signalling a live
# tree, so a monitor that is already gone settles it just as well as one that
# formed its group: a command can finish in the pre-exec child, and one that
# dies at once takes timeout with it, since timeout re-raises the child's
# fatal signal on itself. Neither leaves anything this supervisor could still
# signal, so both are reaped normally below; only a monitor that is still
# alive without a group of its own is the failure this cannot proceed past.
monitor_complete=false
monitor_gone=false
while :; do
  monitor_adopt_own_process_group || true
  [ "$monitor_pgid" = "$monitor_pid" ] && break
  if grep -q '^done:' "$status_file"; then
    monitor_complete=true
    break
  fi
  if monitor_has_exited; then
    monitor_gone=true
    break
  fi
  sleep 0.01
done
if [ "$monitor_pgid" = "$monitor_pid" ]; then
  # The inner Bash records the sentinel as its first action, so the same
  # reasoning applies: poll until it appears, the command reports completion,
  # or the monitor is gone and it never will.
  while :; do
    capture_sentinel_identity && break
    grep -q '^done:' "$status_file" && break
    monitor_has_exited && break
    sleep 0.01
  done
fi
if [ "$monitor_pgid" != "$monitor_pid" ] &&
   [ "$monitor_complete" = false ] && [ "$monitor_gone" = false ]; then
  signal_process_group TERM
  wait "$monitor_pid" 2>/dev/null || true
  trap - HUP INT TERM
  echo "rocq-compile-supervisor: timeout did not create an identifiable process group" >&2
  exit 125
fi
wait "$monitor_pid"
supervisor_status=$?
# No trap after this reap may act on monitor_pid: it is now eligible for reuse.
trap - HUP INT TERM
forget_supervised_identity

# Every writer terminates the record with a newline, so one `read` replaces a
# `cat` fork; an unreadable or truncated file leaves it empty and falls through
# to the invalid-record report below.
IFS= read -r status_record < "$status_file" || status_record=
case "$status_record" in
  done:*)
    command_status=${status_record#done:}
    case "$command_status" in
      ''|*[!0-9]*)
        echo "rocq-compile-supervisor: invalid command status record" >&2
        exit 125
        ;;
    esac
    exit "$command_status"
    ;;
  # The command returned but the wrapper parked as a signal-resistant anchor
  # and was killed there, so its status never became the supervised outcome:
  # classify the run exactly like a still-running sentinel.
  running|interrupted:*)
    ;;
  *)
    echo "rocq-compile-supervisor: invalid command status record" >&2
    exit 125
    ;;
esac

case "$supervisor_status" in
  124)
    report_timeout
    exit 124
    ;;
  137)
    # 137 is timeout's own --kill-after KILL, but also what it propagates when
    # something else SIGKILLed the wrapper -- under memory pressure, the OOM
    # killer. Only elapsed time separates them. Tolerate a whole second below
    # the budget, since the clock is coarse and timeout rounds its own sleep:
    # a real timeout must never be demoted to a spurious kill report.
    elapsed_cs=$(($(monotonic_centiseconds) - command_start_cs))
    if [ "$elapsed_cs" -ge "$((timeout_seconds * 100 - 100))" ]; then
      report_timeout
      exit 124
    fi
    printf 'rocq-compile-supervisor: KILLED phase=%s source=%s elapsed=%d.%02ds limit=%ss grace=%ss exit=137 (command process killed before the time budget expired; an out-of-memory kill is the usual cause)\n' \
      "$phase" "$source_file" "$((elapsed_cs / 100))" "$((elapsed_cs % 100))" \
      "$timeout_seconds" "$grace_seconds" >&2
    exit 137
    ;;
  *) exit "$supervisor_status" ;;
esac
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  supervisor_main "$@"
fi
