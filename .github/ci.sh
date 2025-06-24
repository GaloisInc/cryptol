#!/usr/bin/env bash
set -xEeuo pipefail

[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=${PWD}/bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

# The deps() function is primarily used for producing debug output to
# the CI logging files.  For each platform, it will indicate which
# shared libraries are needed and if they are present or not.  The
# '|| true' is used because statically linked binaries will cause
# ldd (and possibly otool) to exit with a non-zero status.
deps() {
  case "$RUNNER_OS" in
    Linux) ldd $1 || true ;;
    macOS) otool -L $1 || true ;;
    Windows) ldd $1 || true ;;
  esac
}

# Finds the cabal-built '$1' executable and copies it to the '$2'
# directory.
extract_exe() {
  exe="$(cabal list-bin -v0 "$1")"
  name="$(basename "$exe")"
  echo "Copying $name to $2"
  mkdir -p "$2"
  cp -f "$exe" "$2/$name"
  $IS_WIN || chmod +x "$2/$name"
}

retry() {
  echo "Attempting with retry:" "$@"
  local n=1
  while true; do
    if "$@"; then
      break
    else
      if [[ $n -lt 3 ]]; then
        sleep $n # don't retry immediately
        ((n++))
        echo "Command failed. Attempt $n/3:"
      else
        echo "The command has failed after $n attempts."
        return 1
      fi
    fi
  done
}

setup_dist_bins() {
  extract_exe "exe:cryptol" "dist/bin"
  extract_exe "exe:cryptol-html" "dist/bin"
  extract_exe "exe:cryptol-remote-api" "dist/bin"
  extract_exe "exe:cryptol-eval-server" "dist/bin"
  strip dist/bin/cryptol* || echo "Strip failed: Ignoring harmless error"
}

build() {
  ghc_ver="$(ghc --numeric-version)"
  cp cabal.GHC-"$ghc_ver".config cabal.project.freeze
  cabal v2-update
  cabal v2-configure -j2 --minimize-conflict-set --enable-tests
  git status --porcelain
  retry ./cry build exe:cryptol-html "$@" # retry due to flakiness with windows builds
  retry ./cry build exe:cryptol-remote-api "$@"
  retry ./cry build exe:cryptol-eval-server "$@"
  retry ./cry build test:cryptol-api-tests "$@"
  cd language-server && ./build && cd -
}

install_system_deps() {
  (cd $BIN && curl -o bins.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/$SOLVER_PKG_VERSION/$BIN_ZIP_FILE" && unzip -o bins.zip && rm bins.zip)
  chmod +x $BIN/*
  cp $BIN/yices_smt2$EXT $BIN/yices-smt2$EXT
  export PATH=$BIN:$PATH
  echo "$BIN" >> "$GITHUB_PATH"
  is_exe "$BIN" z3 && is_exe "$BIN" cvc4 && is_exe "$BIN" cvc5 && is_exe "$BIN" yices
}

check_docs() {
  ./cry build exe:check-exercises
  find ./docs/ProgrammingCryptol -name '*.tex' -print0 | xargs -0 -n1 cabal v2-exec -v0 check-exercises
}

test_rpc() {
  ./cry rpc-test
}

check_rpc_docs() {
  ./cry rpc-docs
}

bundle_files() {
  doc=dist/share/doc/cryptol
  lib=dist/share/cryptol
  mkdir -p $doc
  cp -R examples/ $doc/examples/
  rm -rf $doc/examples/cryptol-specs
  cp docs/*pdf $doc
  mkdir -p $lib
  cp -r lib/* $lib

  # Copy the two interesting examples over
  cp docs/ProgrammingCryptol/{aes/AES,enigma/Enigma}.cry $doc/examples/
  $IS_WIN || chmod +x dist/bin/*
}

sign() {
  # This is surrounded with `set +x; ...; set -x` to disable printing out
  # statements that could leak GPG-related secrets.
  set +x
  gpg --batch --import <(echo "$SIGNING_KEY")
  fingerprint="$(gpg --list-keys | grep Galois -a1 | head -n1 | awk '{$1=$1};1')"
  echo "$fingerprint:6" | gpg --import-ownertrust
  gpg --yes --no-tty --batch --pinentry-mode loopback --default-key "$fingerprint" --detach-sign -o "$1".sig --passphrase-file <(echo "$SIGNING_PASSPHRASE") "$1"
  set -x
}

zip_dist() {
  : "${VERSION?VERSION is required as an environment variable}"
  name="${name:-"cryptol-$VERSION-$OS_TAG-$ARCH_TAG"}"
  cp -r dist "$name"
  tar -cvzf "$name".tar.gz "$name"
}

zip_dist_with_solvers() {
  : "${VERSION?VERSION is required as an environment variable}"
  name="${name:-"cryptol-$VERSION-$OS_TAG-$ARCH_TAG"}"
  sname="${name}-with-solvers"
  cp "$(which abc)"        dist/bin/
  cp "$(which cvc4)"       dist/bin/
  cp "$(which cvc5)"       dist/bin/
  cp "$(which yices)"      dist/bin/
  cp "$(which yices-smt2)" dist/bin/
  cp "$(which z3)"         dist/bin/
  cp -r dist "$sname"
  tar -cvzf "$sname".tar.gz "$sname"
}

output() { echo "::set-output name=$1::$2"; }
ver() { grep Version cryptol.cabal | awk '{print $2}'; }
set_version() { output cryptol-version "$(ver)"; }
set_files() { output changed-files "$(files_since "$1" "$2")"; }
files_since() {
  changed_since="$(git log -1 --before="@{$2}")"
  files="${changed_since:+"$(git diff-tree --no-commit-id --name-only -r "$1" | xargs)"}"
  echo "$files"
}

COMMAND="$1"
shift

"$COMMAND" "$@"
