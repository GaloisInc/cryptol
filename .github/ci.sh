#!/usr/bin/env bash
set -Eeuo pipefail

[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

extract_exe() {
  exe="$(cabal v2-exec which "$1$EXT")"
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

setup_external_tools() {
  is_exe "$BIN" "test-runner" && return
  cabal v2-install --install-method=copy --installdir="$BIN" test-lib
}

setup_dist_bins() {
  is_exe "dist/bin" "cryptol" && is_exe "dist/bin" "cryptol-html" && return
  extract_exe "cryptol" "dist/bin"
  extract_exe "cryptol-html" "dist/bin"
  strip dist/bin/cryptol* || echo "Strip failed: Ignoring harmless error"
}

install_z3() {
  is_exe "$BIN" "z3" && return

  case "$RUNNER_OS" in
    Linux) file="ubuntu-16.04.zip" ;;
    macOS) file="osx-10.14.6.zip" ;;
    Windows) file="win.zip" ;;
  esac
  curl -o z3.zip -sL "https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION/z3-$Z3_VERSION-x64-$file"

  if $IS_WIN; then 7z x -bd z3.zip; else unzip z3.zip; fi
  cp z3-*/bin/z3$EXT $BIN/z3$EXT
  $IS_WIN || chmod +x $BIN/z3
  rm z3.zip
}

install_cvc4() {
  is_exe "$BIN" "cvc4" && return
  version="${CVC4_VERSION#4.}" # 4.y.z -> y.z

  case "$RUNNER_OS" in
    Linux) file="x86_64-linux-opt" ;;
    Windows) file="win64-opt.exe" ;;
    macOS) file="macos-opt" ;;
  esac
  # Temporary workaround
  if [[ "$RUNNER_OS" == "Linux" ]]; then
    curl -o cvc4$EXT -sL "https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/unstable/cvc4-2020-08-18-x86_64-linux-opt"
  else
    curl -o cvc4$EXT -sL "https://github.com/CVC4/CVC4/releases/download/$version/cvc4-$version-$file"
  fi
  $IS_WIN || chmod +x cvc4$EXT
  mv cvc4$EXT "$BIN/cvc4$EXT"
}

install_yices() {
  is_exe "$BIN" "yices" && return
  ext=".tar.gz"
  case "$RUNNER_OS" in
    Linux) file="pc-linux-gnu-static-gmp.tar.gz" ;;
    macOS) file="apple-darwin18.7.0-static-gmp.tar.gz" ;;
    Windows) file="pc-mingw32-static-gmp.zip" && ext=".zip" ;;
  esac
  curl -o "yices$ext" -sL "https://yices.csl.sri.com/releases/$YICES_VERSION/yices-$YICES_VERSION-x86_64-$file"

  if $IS_WIN; then
    7z x -bd "yices$ext"
    mv "yices-$YICES_VERSION"/bin/*.exe "$BIN"
  else
    tar -xzf "yices$ext"
    pushd "yices-$YICES_VERSION" || exit
    sudo ./install-yices
    popd || exit
  fi
  rm -rf "yices$ext" "yices-$YICES_VERSION"
}

build() {
  ghc_ver="$(ghc --numeric-version)"
  cp cabal.GHC-"$ghc_ver".config cabal.project.freeze
  cabal v2-update
  cabal v2-configure -j2 --minimize-conflict-set
  retry ./cry build exe:cryptol-html "$@" # retry due to flakiness with windows builds
}

install_system_deps() {
  install_z3 &
  install_cvc4 &
  install_yices &
  wait
  export PATH=$PWD/$BIN:$PATH
  echo "::add-path::$PWD/$BIN"
  is_exe "$BIN" z3 && is_exe "$BIN" cvc4 && is_exe "$BIN" yices
}

test_dist() {
  setup_dist_bins
  setup_external_tools
  if $IS_WIN; then
    echo "Warning: janky hacky workaround to #764"
    sed -i 's!/!\\!g' tests/modsys/T14.icry.stdout
  fi
  $BIN/test-runner --ext=.icry -F -b --exe=dist/bin/cryptol tests
}

bundle_files() {
  doc=dist/share/doc/cryptol
  mkdir -p $doc
  cp -R examples/ $doc/examples/
  rm -rf $doc/examples/cryptol-specs
  cp docs/*md docs/*pdf $doc

  # Copy the two interesting examples over
  cp docs/ProgrammingCryptol/{aes/AES,enigma/Enigma}.cry $doc/examples/
  $IS_WIN || chmod +x dist/bin/*
}

sign() {
  gpg --batch --import <(echo "$SIGNING_KEY")
  fingerprint="$(gpg --list-keys | grep galois -a1 | head -n1 | awk '{$1=$1};1')"
  echo "$fingerprint:6" | gpg --import-ownertrust
  gpg --yes --no-tty --batch --pinentry-mode loopback --default-key "$fingerprint" --detach-sign -o "$1".sig --passphrase-file <(echo "$SIGNING_PASSPHRASE") "$1"
}

zip_dist() {
  : "${VERSION?VERSION is required as an environment variable}"
  name="${name:-"cryptol-$VERSION-$RUNNER_OS-x86_64"}"
  mv dist "$name"
  tar -czf "$name".tar.gz "$name"
  sign "$name".tar.gz
  [[ -f "$name".tar.gz.sig ]] && [[ -f "$name".tar.gz ]]
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
