#!/bin/sh

#
# Edit these paths to suit your needs; by default all of the python
# files for connecting to Cryptol are in the same directory as this
# script.
#

CRYNB_ROOT="$( cd "$(dirname "$0")" ; pwd -P )"
IPNB_MAGICS=$CRYNB_ROOT

#
# Leave everything below this line alone
#

export CRYNB_ROOT
export PYTHONPATH=$PYTHONPATH:$IPNB_MAGICS

pushd $CRYNB_ROOT
ipython notebook \
    --profile-dir=$CRYNB_ROOT/profile_cryptol #\
#    --ext=cryptolmagic
popd
