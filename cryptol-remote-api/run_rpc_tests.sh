#!/usr/bin/env bash

set -euo pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

pushd $DIR/python

NUM_FAILS=0
run_test() {
    "$@"
    if (( $? != 0 )); then NUM_FAILS=$(($NUM_FAILS+1)); fi
}

cabal-which() {
    which $1 || cabal v2-exec which $1 || { echo "could not locate $1 executable" >&2 && exit 1; }
}

get_server() {
    CRYPTOL_SERVER=$(cabal-which $1)
    export CRYPTOL_SERVER
    echo "Using server $CRYPTOL_SERVER"
}

echo "Setting up python environment for remote server clients..."
poetry update
poetry install

echo "Typechecking code with mypy..."
run_test poetry run mypy --install-types --non-interactive cryptol/ tests/

get_server cryptol-remote-api
echo "Running cryptol-remote-api tests..."
run_test poetry run python -m unittest discover --verbose tests/cryptol

get_server cryptol-eval-server
echo "Running cryptol-eval-server tests..."
run_test poetry run python -m unittest discover --verbose tests/cryptol_eval

popd
