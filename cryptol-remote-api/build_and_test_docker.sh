#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

pushd $DIR/..

docker build -t cryptol-remote-api --file cryptol-remote-api/Dockerfile .
popd

pushd $DIR

docker run --name=cryptol-remote-api -d \
  -v $PWD/python/tests/cryptol/test-files:/home/cryptol/tests/cryptol/test-files \
  -p 8080:8080 \
  cryptol-remote-api

popd

sleep 5 # let the server catch its breath and be ready for requests

pushd $DIR/python

NUM_FAILS=0

echo "Setting up python environment for remote server clients..."
python3 -m venv virtenv
. virtenv/bin/activate
pip install -r requirements.txt

export CRYPTOL_SERVER_URL="http://localhost:8080/"
python3 -m unittest discover tests/cryptol
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
