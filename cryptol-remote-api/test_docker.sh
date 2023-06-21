#!/usr/bin/env bash

set -euo pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

PROTO=${1:-"http"}
TAG=${2:-cryptol-remote-api}

pushd $DIR

rm -fr $DIR/python/tests/cryptol/test-files/examples
cp -r $DIR/../examples $DIR/python/tests/cryptol/test-files/

CONTAINER=$(docker run -d \
  -v $DIR/python/tests/cryptol/test-files:/home/cryptol/tests/cryptol/test-files \
  -p 8080:8080 \
  $([[ "$PROTO" == "https" ]] && echo "-e TLS_ENABLE=1") \
  $TAG)

popd

sleep 5 # let the server catch its breath and be ready for requests

pushd $DIR/python

NUM_FAILS=0

echo "Setting up python environment for remote server clients..."
poetry update
poetry install

export CRYPTOL_SERVER_URL="$PROTO://localhost:8080/"

echo "Running cryptol-remote-api tests with remote server at $CRYPTOL_SERVER_URL..."
poetry run python -m unittest discover --verbose tests/cryptol
if [ $? -ne 0 ]; then
    NUM_FAILS=$(($NUM_FAILS+1))
fi

popd

echo "killing docker container"

docker container kill $CONTAINER


if [ $NUM_FAILS -eq 0 ]
then
  echo "All Docker RPC tests passed"
  exit 0
else
  echo "Some Docker RPC tests failed"
  exit 1
fi
