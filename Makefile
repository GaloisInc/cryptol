HERE := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

UNAME   := $(shell uname -s)
ARCH    := $(shell uname -m)

TESTS ?= issues regression renamer mono-binds
TEST_DIFF ?= meld

IGNORE_EXPECTED ?= --ignore-expected

CABAL_BUILD_FLAGS   ?= -j
CABAL_INSTALL_FLAGS ?= $(CABAL_BUILD_FLAGS)

CABAL         := cabal
CABAL_BUILD   := $(CABAL) build $(CABAL_BUILD_FLAGS)
CABAL_INSTALL := $(CABAL) install $(CABAL_INSTALL_FLAGS)
CS            := $(HERE)/.cabal-sandbox
CS_BIN        := $(CS)/bin

# Used only for windows, to find the right Program Files.
PROGRAM_FILES = Program\ Files\ \(x86\)
# Windows installer tools; assumes running on Cygwin and using WiX 3.8
WiX      := /cygdrive/c/${PROGRAM_FILES}/WiX\ Toolset\ v3.8
CANDLE   := ${WiX}/bin/candle.exe
HEAT     := ${WiX}/bin/heat.exe
LIGHT    := ${WiX}/bin/light.exe

REV         ?= $(shell git rev-parse --short=7 HEAD || echo "unknown")
VERSION     := $(shell grep -i ^Version cryptol.cabal | awk '{ print $$2}')
SYSTEM_DESC ?= ${UNAME}-${ARCH}_${REV}
PKG         := cryptol-${VERSION}-${SYSTEM_DESC}

# Windows-specific stuff
ifneq (,$(findstring _NT,${UNAME}))
  DIST := ${PKG}.msi
  EXE_EXT := .exe
  adjust-path = '$(shell cygpath -w $1)'
  PREFIX ?=
  # For a systemwide distribution .msi, use:
  # PREFIX ?= ${PROGRAM_FILES}/Galois/Cryptol\ ${VERSION}
  # split this up because `cabal copy` strips drive letters
  PREFIX_ABS    := /cygdrive/c/${PREFIX}
  # since Windows installs aren't overlapping like /usr/local, we
  # don't need this extra prefix
  PREFIX_SHARE  :=
  # goes under the share prefix
  PREFIX_DOC    := /doc
  PKG_PREFIX    := ${PKG}/${PREFIX}
  ROOT_PATH     := /cygdrive/c
else
  DIST := ${PKG}.tar.gz ${PKG}.zip
  EXE_EXT :=
  adjust-path = '$1'
  PREFIX ?=
  # For a systemwide distribution like an .rpm or .pkg, use something like:
  # PREFIX ?= /usr/local
  PREFIX_ABS := ${PREFIX}
  PREFIX_SHARE := /share
  # goes under the share prefix
  PREFIX_DOC   := /doc/cryptol
  PKG_PREFIX   := ${PKG}${PREFIX}
  ROOT_PATH    := /
endif

CRYPTOL_EXE  := ./dist/build/cryptol/cryptol${EXE_EXT}

.PHONY: all
all: ${CRYPTOL_EXE}

.PHONY: run
run: ${CRYPTOL_EXE}
	CRYPTOLPATH=$(call adjust-path,$(CURDIR)/lib) ${CRYPTOL_EXE}

.PHONY: docs
docs:
	(cd docs; make)

.PHONY: dist
dist: ${DIST}

.PHONY: tarball
tarball: ${PKG}.tar.gz

.PHONY: zip
zip: ${PKG}.zip

.PHONY: msi
msi: ${PKG}.msi

# TODO: piece this apart a bit more; if right now if something fails
# during initial setup, you have to invoke this target again manually
${CS}:
	$(CABAL) sandbox init

${CS_BIN}/alex: | ${CS}
	$(CABAL_INSTALL) alex

${CS_BIN}/happy: | ${CS} ${CS_BIN}/alex
	$(CABAL_INSTALL) happy

GIT_INFO_FILES :=
ifneq ("$(wildcard .git/index)","")
GIT_INFO_FILES := ${GIT_INFO_FILES} .git/index
endif
ifneq ("$(wildcard .git/HEAD)","")
GIT_INFO_FILES := ${GIT_INFO_FILES} .git/HEAD
endif
ifneq ("$(wildcard .git/packed-refs)","")
GIT_INFO_FILES := ${GIT_INFO_FILES} .git/packed-refs
endif

CRYPTOL_SRC := \
  $(shell find src cryptol \
            \( -name \*.hs -or -name \*.x -or -name \*.y \) \
            -and \( -not -name \*\#\* \) -print) \
  $(shell find lib -name \*.cry) \
  ${GIT_INFO_FILES}

print-%:
	@echo $* = $($*)

# We do things differently based on whether we have a PREFIX set by
# the user. If we do, then we know the eventual path it'll wind up in
# (useful for stuff like RPMs or Homebrew). If not, we try to be as
# relocatable as possible.
ifneq (,${PREFIX})
  PREFIX_ARG      := --prefix=$(call adjust-path,${PREFIX_ABS})
  DESTDIR_ARG     := --destdir=${PKG}
  CONFIGURE_ARGS  := -f-relocatable -f-self-contained \
                     --docdir=$(call adjust-path,${PREFIX}/${PREFIX_SHARE}/${PREFIX_DOC})
else
  # This is kind of weird: 1. Prefix argument must be absolute; Cabal
  # doesn't yet fully support relocatable packages. 2. We have to
  # provide *some* prefix here even if we're not using it, otherwise
  # `cabal copy` will make a mess in the PKG directory.
  PREFIX_ARG      := --prefix=$(call adjust-path,${ROOT_PATH})
  DESTDIR_ARG     := --destdir=${PKG}
  CONFIGURE_ARGS  := -f-self-contained \
                     --docdir=$(call adjust-path,${PREFIX_SHARE}/${PREFIX_DOC})
endif

dist/setup-config: cryptol.cabal Makefile | ${CS_BIN}/alex ${CS_BIN}/happy
	$(CABAL_INSTALL) --only-dependencies
	$(CABAL) configure ${PREFIX_ARG} --datasubdir=cryptol \
          ${CONFIGURE_ARGS}

${CRYPTOL_EXE}: $(CRYPTOL_SRC) dist/setup-config
	$(CABAL_BUILD)


PKG_BIN       := ${PKG_PREFIX}/bin
PKG_SHARE     := ${PKG_PREFIX}${PREFIX_SHARE}
PKG_CRY       := ${PKG_SHARE}/cryptol
PKG_DOC       := ${PKG_SHARE}${PREFIX_DOC}
PKG_EXAMPLES  := ${PKG_DOC}/examples
PKG_EXCONTRIB := ${PKG_EXAMPLES}/contrib

PKG_EXAMPLE_FILES := docs/ProgrammingCryptol/aes/AES.cry       \
                     docs/ProgrammingCryptol/enigma/Enigma.cry \
                     examples/DES.cry                          \
                     examples/Cipher.cry                       \
                     examples/DEStest.cry                      \
                     examples/Test.cry                         \
                     examples/SHA1.cry                         \

PKG_EXCONTRIB_FILES := examples/contrib/mkrand.cry \
                       examples/contrib/RC4.cry    \
                       examples/contrib/simon.cry  \
                       examples/contrib/speck.cry

${PKG}: ${CRYPTOL_EXE} \
        docs/*.md docs/*.pdf LICENSE LICENSE.rtf \
        ${PKG_EXAMPLE_FILES} ${PKG_EXCONTRIB_FILES}
	$(CABAL) copy ${DESTDIR_ARG}
	mkdir -p ${PKG_CRY}
	mkdir -p ${PKG_DOC}
	mkdir -p ${PKG_EXAMPLES}
	mkdir -p ${PKG_EXCONTRIB}
	cp docs/*.md ${PKG_DOC}
	cp docs/*.pdf ${PKG_DOC}
	for EXAMPLE in ${PKG_EXAMPLE_FILES}; do \
          cp $$EXAMPLE ${PKG_EXAMPLES}; done
	for EXAMPLE in ${PKG_EXCONTRIB_FILES}; do \
          cp $$EXAMPLE ${PKG_EXCONTRIB}; done
# cleanup unwanted files
# don't want to bundle the cryptol library in the binary distribution
	rm -rf ${PKG_PREFIX}/lib; rm -rf ${PKG_PREFIX}/*windows-ghc*
# don't ship haddock
	rm -rf ${PKG_DOC}/html

.PHONY: install
install: ${PKG}
	[ -n "${PREFIX}" ] \
          || (echo "[error] Can't install without PREFIX set"; false)
	(cd ${PKG_PREFIX}; \
          find .          -type d -exec install -d        ${PREFIX}/{} \; ; \
          find bin   -not -type d -exec install -m 755 {} ${PREFIX}/{} \; ; \
          find share -not -type d -exec install -m 644 {} ${PREFIX}/{} \;)

${PKG}.tar.gz: ${PKG}
	tar -czvf $@ $<

${PKG}.zip: ${PKG}
	zip -r $@ $<

${PKG}.msi: ${PKG} win32/cryptol.wxs
	${HEAT} dir ${PKG_PREFIX} -o allfiles.wxs -nologo -var var.pkg \
          -ag -wixvar -cg ALLFILES -srd -dr INSTALLDIR -sfrag
	${CANDLE} -ext WixUIExtension -ext WixUtilExtension            \
          -dversion=${VERSION} -dpkg=${PKG_PREFIX} win32/cryptol.wxs
	${CANDLE} -ext WixUIExtension -ext WixUtilExtension            \
          -dversion=${VERSION} -dpkg=${PKG_PREFIX} allfiles.wxs
	${LIGHT} -ext WixUIExtension -ext WixUtilExtension             \
	  -sval -o $@ cryptol.wixobj allfiles.wixobj
	rm -f allfiles.wxs
	rm -f *.wixobj
	rm -f *.wixpdb

${CS_BIN}/cryptol-test-runner: \
  ${PKG}                       \
  $(CURDIR)/tests/Main.hs      \
  $(CURDIR)/tests/cryptol-test-runner.cabal
	$(CABAL_INSTALL) ./tests

.PHONY: test
test: ${CS_BIN}/cryptol-test-runner
	( cd tests &&                                                      \
	echo "Testing on $(UNAME)-$(ARCH)" &&                              \
	$(realpath $(CS_BIN)/cryptol-test-runner)                          \
	  $(TESTS)                                                         \
	  -c $(call adjust-path,${CURDIR}/${PKG_BIN}/cryptol${EXE_EXT})    \
	  -r output                                                        \
	  -T --hide-successes                                              \
	  -T --jxml=$(call adjust-path,$(CURDIR)/results.xml)              \
	  $(IGNORE_EXPECTED)                                               \
	  $(if $(TEST_DIFF),-p $(TEST_DIFF),)                              \
	)

.PHONY: clean
clean:
	cabal clean
	rm -f $(CS_BIN)/cryptol-test-suite
	rm -rf cryptol-${VERSION}*/
	rm -rf cryptol-${VERSION}*.tar.gz
	rm -rf cryptol-${VERSION}*.zip
	rm -rf cryptol-${VERSION}*.msi

.PHONY: squeaky
squeaky: clean
	-$(CABAL) sandbox delete
	(cd docs; make clean)
	rm -rf dist
	rm -rf tests/dist
