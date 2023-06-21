#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

pushd $DIR/docs
cabal run exe:cryptol-remote-api --verbose=0 -- doc > Cryptol.rst
popd
