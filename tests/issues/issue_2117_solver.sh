#!/usr/bin/env sh

allowed_checks=${1:-0}
checks=0

# Respond normally until the requested check-sat, then simulate a solver that
# is permanently stuck. Cryptol should terminate this process.
while IFS= read -r command
do
  case "$command" in
    "(check-sat)")
      checks=$((checks + 1))
      if [ "$checks" -le "$allowed_checks" ]
      then
        printf 'unsat\n'
      else
        exec sleep 3600
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
