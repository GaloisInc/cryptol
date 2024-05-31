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

WHAT4_SOLVERS_SNAPSHOT="snapshot-20240212"
WHAT4_SOLVERS_URL="https://github.com/GaloisInc/what4-solvers/releases/download/$WHAT4_SOLVERS_SNAPSHOT/"
WHAT4_SOLVERS_MACOS_12="macos-12-X64-bin.zip"
WHAT4_SOLVERS_MACOS_14="macos-14-ARM64-bin.zip"

function notice {
    echo -e "[NOTICE] $*"
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
    # todo: change names here
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

function is_macos {
    [ "$OSTYPE" = "darwin"* ]
}

# Indicate whether this is running macOS on the Apple M series hardware.
function is_macos_aarch {
    # Is it running macOS?
    if [ ! is_macos ]; then
        return 1
    fi

    # Does it use an M-series chip?
    # Actually this command apparently doesn't exist in macOS 12, so this will fail the wrong way
    chip=$(system_profiler SPHardwareDataType | grep Chip)
    [ $chip == *M1* || $chip == *M2* || $chip == *M3* ]
}

function install_gmp {
    if [ is_macos ]; then
        notice "Installing GMP via Homebrew, if it's not already installed"
        logged brew install gmp

        # `brew --prefix` is different on macOS 12 and macOS 14
        notice "You may need to add the following environment variables to your '.profile': \n"\
            "export CPATH=$(brew --prefix)/include\n"\
            "export LIBRARY_PATH=$(brew --prefix)/lib\n"
    else
        notice "Did not install GMP. This script only supports macOS 12 and 14"
    fi
}

# Installs the two solvers required to run the test suite for the repo.
# Users may want to install other solvers, and indeed the what4 solvers repo
# includes a half dozen other solvers that are compatible with cryptol. 
function install_what4_solvers {
    if ! cvc4 --version &> /dev/null || ! cvc5 --version &> /dev/null; then
        notice "Installing cvc4 and/or cvc5 solvers"

        if [ ! is_macos ]; then
            notice "Did not install what4 solvers. This script only supports macOS 12 and 14"
            return
        fi

        if [ is_macos_aarch ]; then
            solvers_version=$WHAT4_SOLVERS_MACOS_14
        else
            # This assumes that developers have read the docs and only run this
            # script if they're on 12 or 14. This might bork on older versions.
            solvers_version=$WHAT4_SOLVERS_MACOS_12
        fi

        solvers_dir=$(mktemp -d)
        curl --proto '=https' --tlsv1.2 -sSfL "$WHAT4_SOLVERS_URL$solvers_version" > "$solvers_dir/solvers.bin.zip"
        cd $solvers_dir
        logged unzip solvers.bin.zip
        
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
