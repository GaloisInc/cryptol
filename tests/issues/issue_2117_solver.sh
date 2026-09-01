#!/usr/bin/env sh

allowed_checks=${1:-0}
checks=0
carriage_return=$(printf '\r')
watchdog_seconds=${ISSUE_2117_WATCHDOG_SECONDS:-30}
solver_pid=$$
watchdog_pid=

watchdog_expired()
{
  printf '(error issue_2117-fake-solver-watchdog-expired)\n'
  exit 2
}

cleanup_watchdog()
{
  if [ -n "$watchdog_pid" ]
  then
    kill "$watchdog_pid" 2>/dev/null || :
  fi
}

trap watchdog_expired USR1
trap cleanup_watchdog EXIT

# Ensure that this test cannot hang forever, even if the fake solver receives
# an unexpected command or Cryptol gets stuck while shutting it down.  Redirect
# every inherited handle so that the watchdog cannot itself keep the solver
# pipes open after Cryptol kills the main shell process.
(
  sleep "$watchdog_seconds"
  if kill -0 "$solver_pid" 2>/dev/null
  then
    kill -USR1 "$solver_pid" 2>/dev/null || :
    sleep 1
    kill -TERM "$solver_pid" 2>/dev/null || :
  fi
) </dev/null >/dev/null 2>&1 &
watchdog_pid=$!

# Respond normally until the requested check-sat, then simulate a solver that
# is permanently stuck. Cryptol should terminate this process.
while IFS= read -r command
do
  # Remove \r at the end of line, which might happen on Windows
  # so that the commands below match properly.
  case "$command" in
    *"$carriage_return")
      command=${command%"$carriage_return"}
      ;;
  esac

  case "$command" in
    "(check-sat)")
      checks=$((checks + 1))
      if [ "$checks" -le "$allowed_checks" ]
      then
        printf 'unsat\n'
      else
        # Delay long enough for Cryptol's timeout to fire, then return a bogus
        # response so that the test fails rather than hanging if it does not.
        # Redirect the child's handles so that it cannot keep the solver pipes
        # open if the shell is killed.
        sleep 30 >/dev/null 2>&1
        printf '(error not-killed)\n'
        exit 1
      fi
      ;;
    "(exit)")
      exit 0
      ;;
    *)
      printf 'success\n'
      ;;
  esac
done
