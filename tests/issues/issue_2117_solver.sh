#!/usr/bin/env sh

allowed_checks=${1:-0}
checks=0

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
