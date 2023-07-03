#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

cd $DIR/docs

export CRYPTOL_SERVER=$(cabal v2-exec which cryptol-remote-api)
if [[ ! -x "$CRYPTOL_SERVER" ]]; then
  echo "could not locate cryptol-remote-api executable - try executing with cabal v2-exec"
  echo "or try building with 'cabal build cryptol-remote-api'"
  exit 1
fi

$CRYPTOL_SERVER doc > TEMP.rst
diff Cryptol.rst TEMP.rst
