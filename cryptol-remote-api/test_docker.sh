#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

TAG=${1:-cryptol-remote-api}

pushd $DIR

rm $PWD/python/tests/cryptol/test-files/examples
mv $PWD/../examples $PWD/python/tests/cryptol/test-files/

docker run --name=cryptol-remote-api -d \
  -v $PWD/python/tests/cryptol/test-files:/home/cryptol/tests/cryptol/test-files \
  -p 8080:8080 \
  $TAG

popd

sleep 5 # let the server catch its breath and be ready for requests

pushd $DIR/python

NUM_FAILS=0

echo "Setting up python environment for remote server clients..."
poetry install

export CRYPTOL_SERVER_URL="http://localhost:8080/"
poetry run python -m unittest discover tests/cryptol
if [ $? -ne 0 ]; then
    NUM_FAILS=$(($NUM_FAILS+1))
fi

popd

echo "killing docker container"

docker container kill cryptol-remote-api


if [ $NUM_FAILS -eq 0 ]
then
  echo "All Docker RPC tests passed"
  exit 0
else
  echo "Some Docker RPC tests failed"
  exit 1
fi
