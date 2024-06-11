#!/bin/sh

# cryptol setup script
#
# Supported distribution(s):
#  * macOS 14 (AArch64)
#  * Ubuntu 20.04 (x86_64)
#  * Ubuntu 22.04 (x86_64)
#
# This script installs everything needed to get a working development
# environment for cryptol. Any new environment requirements should be
# added to this script. This script is not interactive but it may define
# some environment variables that need to be loaded after it runs.
# Assumptions:
# - In Ubuntu, we assume that the system has already run `apt-get update`
#
# There is some half-baked support for macOS 12 (x86_64),
# but it hasn't been tested.
#

set -e

HERE=$(cd `dirname $0`; pwd)
LOG=$HERE/dev_setup.log
truncate -s 0 $LOG
ROOT=$HERE

# Create a new, empty file for environment variables
VAR_FILE=$ROOT/env.sh
truncate -s 0 $VAR_FILE
echo "# Generated environment variables. Manual changes will get clobbered by dev_setup.sh" >> $VAR_FILE

GHCUP_URL="https://downloads.haskell.org/~ghcup"
GHC_VERSION="9.4.8"
CABAL_VERSION="3.10.3.0"

WHAT4_SOLVERS_SNAPSHOT="snapshot-20240212"
WHAT4_SOLVERS_URL="https://github.com/GaloisInc/what4-solvers/releases/download/$WHAT4_SOLVERS_SNAPSHOT"
WHAT4_SOLVERS_MACOS_12="macos-12-X64-bin.zip"
WHAT4_SOLVERS_MACOS_14="macos-14-ARM64-bin.zip"
WHAT4_SOLVERS_UBUNTU_20="ubuntu-20.04-X64-bin.zip"
WHAT4_SOLVERS_UBUNTU_22="ubuntu-22.04-X64-bin.zip"
WHAT4_CVC4_VERSION="version 1.8"
WHAT4_CVC5_VERSION="version 1.1.1"
WHAT4_Z3_VERSION="version 4.8.14"

# Set of supported platforms:
MACOS14="macos14"
MACOS12="macos12" # actually, this isn't supported yet
UBUNTU20="ubuntu-20.04"
UBUNTU22="ubuntu-22.04"

USED_BREW=false

# Returns a string indicating the platform (from the set above), or empty if
# a supported platform is not detected.
supported_platform() {
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
                echo ""
            fi;;
        Linux)
            # Install lsb-release if not available to determine version
            if ! is_installed lsb_release; then
                logged apt-get install -y lsb-release
            fi
            version_file=$(mktemp)
            lsb_release -d > $version_file
            if $(grep -q "Ubuntu 20.04" $version_file); then
                echo $UBUNTU20
            elif $(grep -q "Ubuntu 22.04" $version_file); then
                echo $UBUNTU22
            else
                echo ""
            fi
            rm $version_file;;
        *) echo ""
    esac
}

notice() {
    echo "[NOTICE] $*"
}
unreachable() {
    RED="\033[0;31m"
    echo "${RED}[ERROR] $*"
}

is_installed() {
    command -v "$@" >/dev/null 2>&1
}

# Requires: LOG set to log file path.
logged() {
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

update_submodules() {
    cd $ROOT
    if ! is_installed git; then
        notice "Installing git"
        case $CRYPTOL_PLATFORM in
            $UBUNTU20 | $UBUNTU22) logged apt-get install -y git;;
            $MACOS12 | $MACOS14) logged brew install git && USED_BREW=true;;
            *) unreachable "Unsupported platform; did not install git"; return;;
        esac
    fi
    notice "Updating submodules"
    logged git submodule update --init
}

install_ghcup() {
    if ! is_installed ghcup; then
        # Manually install Haskell toolchain. If this doesn't work, try
        # using the install script at https://www.haskell.org/ghcup/
        case $CRYPTOL_PLATFORM in
            $MACOS12 | $MACOS14)
                notice "Installing GHCup via Homebrew"
                logged brew install ghcup && USED_BREW=true;;
            $UBUNTU20 | $UBUNTU22)
                notice "Installing any missing GHCup dependencies via apt-get"
                logged apt-get install -y build-essential curl libffi-dev libffi7 libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo5

                notice "Installing GHCup via direct download"
                logged curl --proto '=https' --tlsv1.2 -sSfL -o ghcup "$GHCUP_URL/$(uname -m)-linux-ghcup"

                chmod u+x ghcup
                mv ghcup /usr/local/bin/;;
            *) unreachable "Unsupported platform; did not install GHCup"; return;;
        esac
    else
        notice "Using existing GHCup installation"
    fi

    notice "Installing ghc and cabal via GHCup, if they're not already installed"
    notice "Also, setting the default version to ghc $GHC_VERSION"
    logged ghcup install ghc $GHC_VERSION
    logged ghcup set ghc $GHC_VERSION
    logged ghcup install cabal $CABAL_VERSION
    logged ~/.ghcup/bin/cabal-$CABAL_VERSION update

    if ! is_installed ghc || ! is_installed cabal; then
        echo "export PATH=$PATH:~/.ghcup/bin" >> $VAR_FILE
    fi

}

install_gmp() {
    case $CRYPTOL_PLATFORM in
        $MACOS12 | $MACOS14)
            notice "Installing GMP via Homebrew, if it's not already installed"
            logged brew install gmp && USED_BREW=true;;
        $UBUNTU20 | $UBUNTU22)
            notice "Installing GMP via apt-get, if it's not already installed"
            logged apt-get install -y libgmp-dev libgmp10;;
        *) unreachable "Unsupported platform; did not install GMP";;
    esac
}

install_zlib() {
    case $CRYPTOL_PLATFORM in
        $MACOS12 | $MACOS14)
            notice "Installing zlib via Homebrew, if it's not already installed"
            logged brew install zlib && USED_BREW=true;;
        $UBUNTU20 | $UBUNTU22)
            notice "Installing zlib via apt-get, if it's not already installed"
            logged apt-get install -y zlib1g-dev;;
        *) unreachable "Unsupported platform; did not install zlib";;
    esac

}

# Installs the solvers required to run the test suite for the repo.
# Users may want to install other solvers, and indeed the what4 solvers repo
# includes a half dozen other packages that are compatible with cryptol.
install_solvers() {
    # Install solvers using the cryptol-approved set of binaries
    if ! is_installed cvc4 || ! is_installed cvc5 || ! is_installed z3; then
        notice "Installing cvc4, cvc5, and/or z3 solvers via direct download"

        case $CRYPTOL_PLATFORM in
            $MACOS12) solvers_version=$WHAT4_SOLVERS_MACOS_12;;
            $MACOS14) solvers_version=$WHAT4_SOLVERS_MACOS_14;;
            $UBUNTU20) solvers_version=$WHAT4_SOLVERS_UBUNTU_20;;
            $UBUNTU22) solvers_version=$WHAT4_SOLVERS_UBUNTU_22;;
            *) unreachable "Unsupported platform; did not install solvers"; return;;
        esac

        solvers_dir=$(mktemp -d)
        logged curl --proto '=https' --tlsv1.2 -sSfL -o "$solvers_dir/solvers.bin.zip" "$WHAT4_SOLVERS_URL/$solvers_version"
        cd $solvers_dir

        if ! is_installed unzip; then
            case $CRYPTOL_PLATFORM in
                $MACOS12 | $MACOS14)
                    notice "Installing unzip via Homebrew"
                    logged brew install unzip && USED_BREW=true;;
                $UBUNTU20 | $UBUNTU22)
                    notice "Installing unzip via apt-get"
                    logged apt-get install -y unzip;;
                *) unreachable "Unsupported platform; did not install unzip"; return;;
            esac
        fi
        logged unzip solvers.bin.zip

        # If we want to install more solvers by default, we can do so here
        for solver in cvc4 cvc5 z3; do
            if ! is_installed $solver ; then
                notice "Installing $solver"
                chmod u+x $solver
                # Try installing without sudo first, because some environments
                # don't have it installed by default
                mv $solver /usr/local/bin || sudo mv $solver /usr/local/bin
            fi
        done

        cd $HERE
        rm -r $solvers_dir
    else
        notice "Not installing cvc4, cvc5, or z3 solvers because they already exist"
    fi

    # Make sure the installed versions are the versions that have been tested
    check_version cvc4 $WHAT4_CVC4_VERSION
    check_version cvc5 $WHAT4_CVC5_VERSION
    check_version z3 $WHAT4_Z3_VERSION
}

# Checks the version of the given command
# Usage: check_version <command> <expected version>
#
# Assumes that the command can be called with `--version`
check_version() {
    cmd="$1"
    expected="$@"
    version_file=$(mktemp)
    $cmd --version > $version_file
    if ! (grep -iq "$expected" $version_file); then
        actual_version=$(grep -i -m 1 "version" $version_file)
        notice "Your version of $cmd is unexpected; expected $expected"
        notice "    Got: $actual_version"
        notice "    To ensure compatibility, you might want to uninstall the "\
            "existing version and re-run this script."
    fi
    rm $version_file
}


put_brew_in_path() {
    if $USED_BREW; then
        # `brew --prefix` is different on macOS 12 and macOS 14
        echo "export CPATH=$(brew --prefix)/include" >> $VAR_FILE
        echo "export LIBRARY_PATH=$(brew --prefix)/lib" >> $VAR_FILE
    fi
}

set_ubuntu_language_encoding() {
    case $CRYPTOL_PLATFORM in
        $UBUNTU20 | $UBUNTU22)
            notice "Adding language environment variables to $VAR_FILE"
            echo "export LANG=C.UTF-8" >> $VAR_FILE
            echo "export LC_ALL=C.UTF-8" >> $VAR_FILE;;
        *) ;;
    esac
}

# Make sure script is running on a supported platform
notice "Checking whether platform is supported"
CRYPTOL_PLATFORM=$(supported_platform)
if [ -z "$CRYPTOL_PLATFORM" ]; then
    echo "Unsupported platform; this script supports Ubuntu 20.04, Ubuntu 22.04, and macOS 14"
    exit 1
fi

update_submodules
install_ghcup
install_gmp
install_zlib
install_solvers
put_brew_in_path
set_ubuntu_language_encoding

notice "You may need to source new environment variables added here:\n" \
    "\$ source $VAR_FILE"
