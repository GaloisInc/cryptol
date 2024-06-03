#!/bin/sh

# cryptol setup script
#
# Supported distribution(s):
#  * macOS 14 (AArch64)
#
# This script installs everything needed to get a working development
# environment for cryptol. Any new environment requirements should be
# added to this script.
#
# There is some half-baked support for macOS 12 (x86_64), but it hasn't been
# tested.
#

set -e

HERE=$(cd `dirname $0`; pwd)
LOG=$HERE/dev_setup.log
ROOT=$HERE

# Create a new, empty file for environment variables
VAR_FILE=$ROOT/env.sh
truncate -s 0 $VAR_FILE
echo "# Generated environment variables. Manual changes will get clobbered by dev_setup.sh" >> $VAR_FILE

WHAT4_SOLVERS_SNAPSHOT="snapshot-20240212"
WHAT4_SOLVERS_URL="https://github.com/GaloisInc/what4-solvers/releases/download/$WHAT4_SOLVERS_SNAPSHOT/"
WHAT4_SOLVERS_MACOS_12="macos-12-X64-bin.zip"
WHAT4_SOLVERS_MACOS_14="macos-14-ARM64-bin.zip"
WHAT4_CVC4_VERSION="version 1.8"
WHAT4_CVC5_VERSION="version 1.1.1"

# Set of supported platforms:
MACOS14="macos14"
MACOS12="macos12" # actually, this isn't supported yet

# Returns a string indicating the platform (from the set above), or empty if
# a supported platform is not detected.
function supported_platform {
    # Make sure we're running on a supported platform
    case $(uname -s) in
        Darwin)
            if [ $(uname -m) = "arm64" ]; then
                echo $MACOS14
            # This is how we'd support macOS 12. Since this hasn't been tested yet,
            # we withhold official support.
            # This might bork on something running macOS <12, since we're basing
            # the it on the hardware, not the specific version.
            elif [ $(uname -m) = "x86_64" ]; then
                # CRYPTOL_PLATFORM=$MACOS12
                echo ""
            fi;;
        *) echo ""
    esac
}

RED="\033[0;31m"
function notice {
    echo "[NOTICE] $*"
}

function is_installed {
    command -v $* >/dev/null 2>&1
}

# Requires: LOG set to log file path.
function logged {
    if ! [ -z "$LOG" ]
    then
        # This may or may not be the same directory that this script lives in.
        mkdir -p `dirname $LOG`
        echo "$@" >>$LOG
        if ! "$@" >>$LOG 2>&1
        then
            echo
            tail -n 50 $LOG
            echo
            echo "[ERROR] An error occurred; please see $LOG"
            echo "[ERROR] The last 50 lines are printed above for convenience"
            exit 1
        fi
    fi
}

function update_submodules {
    cd $ROOT
    notice "Updating submodules"
    logged git submodule update --init
}

function install_ghcup {
    if ! is_installed ghcup
    then
        ghcup_url="https://get-ghcup.haskell.org"
        notice "ghcup not found; do you want to install from $ghcup_url"
        read -p "Press Enter to continue or 'n' to skip: " consent
        case $consent in
            [Nn]* ) notice "Skipping ghcup installation"; return;;
            * ) notice "Installing ghcup";;
        esac

        # Technically the installation only requires cabal, but it's
        # recommended to get the whole GCH shebang in one package.
        # The output is not routed to log because the installer is interactive.
        ghc_dir=$(mktemp -d)
        logged curl --proto '=https' --tlsv1.2 -sSf -o "$ghc_dir/ghcup.bin" $ghcup_url
        cd $ghc_dir
        sh ghcup.bin
        rm -r $ghc_dir
    else
        notice "Using existing ghcup installation"
    fi

}

function install_gmp {
    if [ $CRYPTOL_PLATFORM = $MACOS12 ] || [ $CRYPTOL_PLATFORM = $MACOS14 ]; then
        notice "Installing GMP via Homebrew, if it's not already installed"
        logged brew install gmp

        # `brew --prefix` is different on macOS 12 and macOS 14
        echo "export CPATH=$(brew --prefix)/include" >> $VAR_FILE
        echo "export LIBRARY_PATH=$(brew --prefix)/lib" >> $VAR_FILE
        notice "You may need to source new environment variables added here:\n" \
            "\$ source $VAR_FILE"
    else
        notice "Did not install GMP. This script only supports macOS 14"
    fi
}

# Installs the two solvers required to run the test suite for the repo.
# Users may want to install other solvers, and indeed the what4 solvers repo
# includes a half dozen other solvers that are compatible with cryptol. 
function install_what4_solvers {
    if ! is_installed cvc4 || ! is_installed cvc5; then
        notice "Installing cvc4 and/or cvc5 solvers from $WHAT4_SOLVERS_URL"

        if [ $CRYPTOL_PLATFORM = $MACOS14 ]; then
            solvers_version=$WHAT4_SOLVERS_MACOS_14
        elif [ $CRYPTOL_PLATFORM = $MACOS12 ]; then
            solvers_version=$WHAT4_SOLVERS_MACOS_12
        fi

        solvers_dir=$(mktemp -d)
        logged curl --proto '=https' --tlsv1.2 -sSfL -o "$solvers_dir/solvers.bin.zip" "$WHAT4_SOLVERS_URL$solvers_version"
        cd $solvers_dir
        logged unzip solvers.bin.zip
        
        # If we want to install more solvers by default, we can do so here
        for solver in cvc4 cvc5; do
            if ! is_installed $solver ; then
                notice "Installing $solver"
                chmod u+x $solver
                sudo mv $solver /usr/local/bin
            fi
        done

        rm -r $solvers_dir
    else
        notice "Not installing cvc4 or cvc5 solvers because they already exist"

        if ! (grep -q $WHAT4_CVC4_VERSION <<< "$(cvc4 --version)"); then
            notice "Your version of cvc4 is unexpected; expected $WHAT4_CVC4_VERSION"
            notice "Got: $(grep "cvc4 version" <<< "$(cvc4 --version)")"
            notice "To ensure compatibility, you might want to uninstall the "\
                "existing version and re-run this script."
        fi
        if ! (grep -q $WHAT4_CVC5_VERSION <<< "$(cvc5 --version)" ); then
            notice "Your version of cvc5 is unexpected; expected $WHAT5_CVC5_VERSION"
            notice "Got: $(grep "cvc5 version" <<< "$(cvc5 --version)")"
            notice "To ensure compatibility, you might want to uninstall the "\
                "existing version and re-run this script."
        fi
    fi
}


# Make sure script is running on a supported platform
CRYPTOL_PLATFORM=$(supported_platform)
if [ -z "$CRYPTOL_PLATFORM" ]; then
    echo "Unsupported platform"
    exit 1
fi

update_submodules
install_ghcup
install_gmp
install_what4_solvers
