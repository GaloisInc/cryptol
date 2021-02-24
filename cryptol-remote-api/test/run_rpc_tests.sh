#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

if [ ! -d "$DIR/galois-py-toolkit/tests" ]; then
    echo "ERROR: could not find the python test directory -- is the galois-py-toolkit submodule initialzed?"
    exit 1
fi

pushd $DIR/galois-py-toolkit

NUM_FAILS=0

echo "Setting up python environment for remote server clients..."
python3 -m venv virtenv
. virtenv/bin/activate
pip install -r requirements.txt

export CRYPTOL_SERVER=$(cabal v2-exec which cryptol-remote-api)
echo "Running cryptol-remote-api tests..."
echo "Using server $CRYPTOL_SERVER"
python3 -m unittest discover tests/cryptol
if [ $? -ne 0 ]; then
    NUM_FAILS=$(($NUM_FAILS+1))
fi

echo "Running cryptol-eval-server tests..."
export CRYPTOL_SERVER=$(cabal v2-exec which cryptol-eval-server)
echo "Using server $CRYPTOL_SERVER"
python3 -m unittest discover tests/cryptol_eval
if [ $? -ne 0 ]; then
    NUM_FAILS=$(($NUM_FAILS+1))
fi

popd

if [ $NUM_FAILS -eq 0 ]
then
  echo "All RPC tests passed"
  exit 0
else
  echo "Some RPC tests failed"
  exit 1
fi
