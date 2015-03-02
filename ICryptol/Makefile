HERE := $(dir $(lastword $(MAKEFILE_LIST)))

UNAME       := $(shell uname -s)
ARCH        := $(shell uname -m)
REV         ?= $(shell git rev-parse --short=7 HEAD || echo "unknown")
VERSION     := $(shell grep -i ^Version ICryptol.cabal | awk '{ print $$2}')
SYSTEM_DESC ?= ${UNAME}-${ARCH}_${REV}
PKG         := ICryptol-${VERSION}-${SYSTEM_DESC}

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

# Windows-specific stuff
ifneq (,$(findstring _NT,${UNAME}))
  DIST := ${PKG}.msi
  EXE_EXT := .exe
  adjust-path = '$(shell cygpath -w $1)'
  PREFIX ?= ${PROGRAM_FILES}/Galois/ICryptol\ ${VERSION}
  # split this up because `cabal copy` strips drive letters
  PREFIX_ABS    := /cygdrive/c/${PREFIX}
  # since Windows installs aren't overlapping like /usr/local, we
  # don't need this extra prefix
  PREFIX_SHARE  :=
  # goes under the share prefix
  PREFIX_DOC    := /doc
  PKG_PREFIX    := ${PKG}/${PREFIX}
else
  DIST := ${PKG}.tar.gz ${PKG}.zip
  EXE_EXT :=
  adjust-path = '$1'
  PREFIX ?= /usr/local
  PREFIX_ABS := ${PREFIX}
  PREFIX_SHARE := /share
  # goes under the share prefix
  PREFIX_DOC   := /doc/ICryptol
  PKG_PREFIX   := ${PKG}${PREFIX}
endif

ICRYPTOL_EXE := ./dist/build/cryptol/icryptol-kernel${EXE_EXT}

ICRYPTOL_SRC := \
  $(shell find src \
            \( -name \*.hs -or -name \*.x -or -name \*.y \) \
            -and \( -not -name \*\#\* \) -print)

${ICRYPTOL_EXE}: ${ICRYPTOL_SRC} dist/setup-config
	${CABAL_BUILD}


# TODO: piece this apart a bit more; if right now if something fails
# during initial setup, you have to invoke this target again manually
${CS}:
	$(CABAL) sandbox init

${CS_BIN}/alex: | ${CS}
	$(CABAL_INSTALL) alex

${CS_BIN}/happy: | ${CS} ${CS_BIN}/alex
	$(CABAL_INSTALL) happy

dist/setup-config: ICryptol.cabal | ${CS_BIN}/alex ${CS_BIN}/happy
	$(CABAL_INSTALL) --only-dependencies
	$(CABAL) configure                            \
          --prefix=$(call adjust-path,${PREFIX_ABS})  \
          --datasubdir=ICryptol

.PHONY: all
all: ${ICRYPTOL_EXE}

.PHONY: dist
dist: ${DIST}

.PHONY: tarball
tarball: ${PKG}.tar.gz

.PHONY: zip
zip: ${PKG}.zip

.PHONY: msi
msi: ${PKG}.msi

.PHONY: notebook
notebook: ${PKG}
	mkdir -p $(CURDIR)/.ipython
	IPYTHONDIR=$(CURDIR)/.ipython \
	PATH=$(call adjust-path,${CURDIR}/${PKG_BIN}):$$PATH \
	CRYPTOLPATH=$(call adjust-path,$(CURDIR)/lib) \
	${PKG_BIN}/icryptol --notebook-dir=$(call adjust-path,${PKG_EXAMPLES})

PROFILE_CRYPTOL_SRC := profile_cryptol/ipython_config.py \
                       profile_cryptol/static/base/images/ipynblogo.png \
                       profile_cryptol/static/custom/custom.css \
                       profile_cryptol/static/custom/custom.js
profile.tar: ${PROFILE_CRYPTOL_SRC}
	tar -cvf profile.tar profile_cryptol

PKG_BIN       := ${PKG_PREFIX}/bin
PKG_SHARE     := ${PKG_PREFIX}${PREFIX_SHARE}
PKG_ICRY      := ${PKG_SHARE}/ICryptol
PKG_DOC       := ${PKG_SHARE}${PREFIX_DOC}
PKG_EXAMPLES  := ${PKG_DOC}/examples

PKG_EXAMPLE_FILES := examples/AES.ipynb

${PKG}: ${ICRYPTOL_EXE} icryptol profile.tar LICENSE \
        ${PKG_EXAMPLE_FILES}
	$(CABAL) copy --destdir=${PKG}
# script not included in the copy
	cp icryptol ${PKG_BIN}
# don't want to bundle the cryptol library in the binary distribution
	rm -rf ${PKG_PREFIX}/lib
	mkdir -p ${PKG_ICRY}
	mkdir -p ${PKG_DOC}
	mkdir -p ${PKG_EXAMPLES}
	cp LICENSE ${PKG_DOC}
	for EXAMPLE in ${PKG_EXAMPLE_FILES}; do \
          cp $$EXAMPLE ${PKG_EXAMPLES}; done
	cp -r profile.tar ${PKG_ICRY}

${PKG}.tar.gz: ${PKG}
	tar -czvf $@ $<

${PKG}.zip: ${PKG}
	zip -r $@ $<

${PKG}.msi: ${PKG} win32/ICryptol.wxs
	${HEAT} dir ${PKG_PREFIX} -o allfiles.wxs -nologo -var var.pkg \
          -ag -wixvar -cg ALLFILES -srd -dr INSTALLDIR -sfrag
	${CANDLE} -ext WixUIExtension -ext WixUtilExtension            \
          -dversion=${VERSION} -dpkg=${PKG_PREFIX} win32/ICryptol.wxs
	${CANDLE} -ext WixUIExtension -ext WixUtilExtension            \
          -dversion=${VERSION} -dpkg=${PKG_PREFIX} allfiles.wxs
	${LIGHT} -ext WixUIExtension -ext WixUtilExtension             \
	  -sval -o $@ ICryptol.wixobj allfiles.wixobj
	rm -f allfiles.wxs
	rm -f *.wixobj
	rm -f *.wixpdb

.PHONY: clean
clean:
	cabal clean
	rm -rf ICryptol-${VERSION}*/
	rm -rf ICryptol-${VERSION}*.tar.gz
	rm -rf ICryptol-${VERSION}*.zip
	rm -rf ICryptol-${VERSION}*.msi
	rm -rf .ipython
	rm -rf profile.tar

.PHONY: squeaky
squeaky: clean
	-$(CABAL) sandbox delete
	rm -rf dist
