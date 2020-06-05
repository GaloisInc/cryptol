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

setup_external_tools() {
  is_exe "$BIN" "test-runner" && return
  cabal v2-install --install-method=copy --installdir="$BIN" test-lib
}

setup_dist_bins() {
  is_exe "dist" "cryptol" && is_exe "dist" "cryptol-html" && return
  extract_exe "cryptol" "dist"
  extract_exe "cryptol-html" "dist"
  strip dist/cryptol*
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
    macOS) brew tap cvc4/cvc4 && brew install cvc4/cvc4/cvc4 && return ;;
  esac
  curl -o cvc4$EXT -sL "https://github.com/CVC4/CVC4/releases/download/1.7/cvc4-$version-$file"
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
  # Limit jobs on windows due to: https://gitlab.haskell.org/ghc/ghc/issues/17926
  if [[ "$ghc_ver" == "8.8.3" && "$RUNNER_OS" == 'Windows' ]]; then JOBS=1; else JOBS=2; fi
  cabal v2-configure -j$JOBS --minimize-conflict-set
  cabal v2-build "$@" exe:cryptol exe:cryptol-html
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
  $BIN/test-runner --ext=.icry -F -b --exe=dist/cryptol tests
}

bundle_files() {
  doc=dist/share/doc/cryptol
  mkdir -p $doc
  cp -R examples/ $doc/examples/
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
  name="cryptol-$VERSION-$RUNNER_OS-x86_64"
  mv dist "$name"
  if [[ "$RUNNER_OS" == Windows ]]; then 7z a -tzip -mx9 "$name".zip "$name"; else zip -r "$name".zip "$name"; fi
  sign "$name".zip
  [[ -f "$name".zip.sig ]] && [[ -f "$name".zip ]]
}

set_outputs() {
  echo "::set-output name=changed-files::$(git diff-tree --no-commit-id --name-only -r "$1" | xargs)"
  echo "::set-output name=cryptol-version::$(grep Version cryptol.cabal | awk '{print $2}')"
}

COMMAND="$1"
shift

"$COMMAND" "$@"
