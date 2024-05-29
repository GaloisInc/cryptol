#!/usr/bin/env bash

# cryptol setup script
#
# Supported distribution(s):
#  * macOS 14 (AArch64)
#
# This script installs everything needed to get a working development
# environment for cryptol. Any new environment requirements should be
# added to this script.
#

set -e

HERE=$(cd `dirname $0`; pwd)
LOG=$HERE/dev_setup.log

function notice {
    echo "[NOTICE] $*"
}

# Requires: LOG set to log file path.
function logged {
    if ! [ -z "$LOG" ]
    then
        mkdir -p `dirname $LOG`
        echo $* >>$LOG
        if ! $* >>$LOG 2>&1
        then
            echo
            echo "An error occurred; please see $LOG"
            echo "Here are the last 50 lines:"
            tail -n 50 $LOG
            exit 1
        fi
    fi
}

function update_submodules {
    cd $HERE
    notice "Updating submodules"
    git submodule update --init
}

function install_ghcup {
    if ! ghcup --version &> /dev/null
    then
        notice "Installing ghcup, GHC, and cabal"
        # technically the installation only requires cabal, but it's 
        # recommended to get the whole GCH shebang in one package
        curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
    else
        notice "Using existing ghcup installation"
    fi

}

# Indicate whether this is running macOS on the Apple M series hardware.
function is_macos_aarch {
    # Is it running macOS?
    if [[ "$OSTYPE" != "darwin"* ]]; then
        notice "dev setup does not currently support your OS / hardware"
        exit 1 
    fi

    # Does it use an M-series chip?
    chip=$(system_profiler SPHardwareDataType | grep Chip)
    [[ $chip == *M1* || $chip == *M2* || $chip == *M3* ]]
}

function install_gmp {
    if is_macos_aarch; then
        notice "Installing gmp via Homebrew, if it's not already installed"
        logged brew list gmp || brew install gmp

        # on macOS 12 (x86_64), I think homebrew uses different locations
        notice "You may need to add the following environment variables to your '.profile': \n"\
            "export CPATH=/opt/homebrew/include\n"\
            "export LIBRARY_PATH=/opt/homebrew/lib\n"
    fi
}

function install_what4_solvers {
    if ! cvc4 --version &> /dev/null || ! cvc5 --version &> /dev/null; then
        notice "Installing cvc4 and/or cvc5 solvers"

        # There are different URLs for other supported platforms
        if is_macos_aarch; then
            what4_solvers_url="https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20240212/macos-14-ARM64-bin.zip"
        fi

        solvers_dir=$(mktemp -d)
        curl --proto '=https' --tlsv1.2 -sSfL $what4_solvers_url > "$solvers_dir/solvers.bin.zip"
        cd $solvers_dir
        logged unzip solvers.bin.zip
        rm solvers.bin.zip
        
        # If we want to install more solvers by default, we can do so here,
        # although we might need a different check than `--version`
        for solver in cvc4 cvc5; do
            if ! $solver --version &> /dev/null; then 
                notice "Installing $solver"
                chmod u+x $solver
                sudo mv $solver /usr/local/bin
            fi
        done
    fi
}

update_submodules
install_ghcup
install_gmp
install_what4_solvers
