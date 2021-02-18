#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

if [ ! -d "$DIR/galois-py-toolkit/tests" ]; then
    echo "ERROR: could not find the python test directory -- is the galois-py-toolkit submodule initialzed?"
    exit 1
fi

pushd $DIR/galois-py-toolkit

echo "Setting up python environment for remote server clients..."
python3 -m venv virtenv
. virtenv/bin/activate
pip install -r requirements.txt

echo "Running cryptol-remote-api tests..."
export CRYPTOL_SERVER=cryptol-remote-api
python3 -m unittest discover tests/cryptol
export CRYPTOL_SERVER=cryptol-eval-server

echo "Running cryptol-eval-server tests..."
python3 -m unittest discover tests/cryptol_eval

popd
