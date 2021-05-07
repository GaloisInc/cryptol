#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

pushd $DIR

cabal v2-build exe:cryptol-remote-api
cabal v2-build exe:cryptol-eval-server

pushd $DIR/python

NUM_FAILS=0
function run_test {
    "$@"
    if (( $? != 0 )); then NUM_FAILS=$(($NUM_FAILS+1)); fi
}

echo "Setting up python environment for remote server clients..."
poetry install

echo "Typechecking code with mypy..."
run_test poetry run mypy cryptol/ tests/

export CRYPTOL_SERVER=$(cabal v2-exec which cryptol-remote-api)
if [[ -x "$CRYPTOL_SERVER" ]]; then
  echo "Running cryptol-remote-api tests..."
  echo "Using server $CRYPTOL_SERVER"
  run_test poetry run python -m unittest discover tests/cryptol
else
  echo "could not find the cryptol-remote-api via `cabal v2-exec which`"
  NUM_FAILS=$(($NUM_FAILS+1))
fi

export CRYPTOL_SERVER=$(cabal v2-exec which cryptol-eval-server)
if [[ -x "$CRYPTOL_SERVER" ]]; then
  echo "Running cryptol-eval-server tests..."
  echo "Using server $CRYPTOL_SERVER"
  run_test poetry run python -m unittest discover tests/cryptol_eval
else
  echo "could not find the cryptol-eval-server via `cabal v2-exec which`"
  NUM_FAILS=$(($NUM_FAILS+1))
fi
popd

popd

if [ $NUM_FAILS -eq 0 ]
then
  echo "All RPC tests passed"
  exit 0
else
  echo "Some RPC tests failed"
  exit 1
fi
