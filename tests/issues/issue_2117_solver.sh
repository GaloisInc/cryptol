#!/usr/bin/env sh

carriage_return=$(printf '\r')
marker_file=issue_2117_solver_exited.marker

record_self_exit()
{
  printf 'ERROR: fake solver pid=%s exited on its own: %s\n' \
    "$$" "$1" >> "$marker_file"
}

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
      # Delay long enough for Cryptol's timeout to fire, then return a bogus
      # response so that the test fails rather than hanging if it does not.
      sleep 30 >/dev/null 2>&1
      record_self_exit "30-second check-sat fallback expired"
      printf '(error not-killed)\n'
      exit 1
      ;;
    "(exit)")
      exit 0
      ;;
    *)
      printf 'success\n'
      ;;
  esac
done
