UNAME   := $(shell uname -s)
ARCH    := $(shell uname -m)

TESTS ?= issues regression renamer
TEST_DIFF ?= meld

CABAL_FLAGS ?= -j

CABAL_EXE   := cabal
CABAL       := $(CABAL_EXE) $(CABAL_FLAGS)
CS          := ./.cabal-sandbox
CS_BIN      := $(CS)/bin

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
else
  DIST := ${PKG}.tar.gz ${PKG}.zip
  EXE_EXT :=
  adjust-path = '$1'
endif

.PHONY: all
all: ${CS_BIN}/cryptol

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

${CS}:
	$(CABAL_EXE) sandbox init

# order-only dependency: we just want the sandbox to exist
${CS_BIN}/alex: | ${CS}
	$(CABAL) install alex

# order-only dependency: we just want the sandbox to exist
${CS_BIN}/happy: | ${CS}
	$(CABAL) install happy

src/GitRev.hs:
	sh configure


CRYPTOL_DEPS := \
  $(shell find src cryptol \( -name \*.hs -or -name \*.x -or -name \*.y \) -print) \
  $(shell find lib -name \*.cry)

print-%:
	@echo $* = $($*)

${CS_BIN}/cryptol: ${CS_BIN}/alex ${CS_BIN}/happy $(CRYPTOL_DEPS) | ${CS}
	$(CABAL) install .

${CS_BIN}/cryptolnb: ${CS_BIN}/alex ${CS_BIN}/happy | ${CS}
	$(CABAL) install . -fnotebook

${PKG}: ${CS_BIN}/cryptol
	mkdir -p ${PKG}/bin
	mkdir -p ${PKG}/lib
	mkdir -p ${PKG}/doc/examples
	cp ${CS_BIN}/cryptol ${PKG}/bin/cryptol
	cp -R docs/*.md ${PKG}/doc
	cp -R docs/*.pdf ${PKG}/doc
	cp -R lib/* ${PKG}/lib
	cp docs/ProgrammingCryptol/aes/AES.cry ${PKG}/doc/examples
	cp docs/ProgrammingCryptol/enigma/Enigma.cry ${PKG}/doc/examples
	cp examples/DES.cry ${PKG}/doc/examples
	cp examples/Cipher.cry ${PKG}/doc/examples
	cp examples/DEStest.cry ${PKG}/doc/examples
	cp examples/Test.cry ${PKG}/doc/examples
	cp examples/SHA1.cry ${PKG}/doc/examples
	cp examples/contrib/simon.cry ${PKG}/doc/examples/contrib
	cp examples/contrib/speck.cry ${PKG}/doc/examples/contrib
	cp LICENSE ${PKG}/doc

${PKG}.tar.gz: ${PKG}
	tar -czvf $@ $<

${PKG}.zip: ${PKG}
	zip -r $@ $<

${PKG}.msi: ${PKG} win32/cryptol.wxs
	${HEAT} dir ${PKG} -o allfiles.wxs -nologo -var var.pkg -ag -wixvar -cg ALLFILES -srd -dr INSTALLDIR -sfrag
	${CANDLE} -ext WixUIExtension -ext WixUtilExtension -dversion=${VERSION} -dpkg=${PKG} win32/cryptol.wxs
	${CANDLE} -ext WixUIExtension -ext WixUtilExtension -dversion=${VERSION} -dpkg=${PKG} allfiles.wxs
	${LIGHT} -ext WixUIExtension -ext WixUtilExtension -sval -o $@ cryptol.wixobj allfiles.wixobj
	rm -f allfiles.wxs
	rm -f *.wixobj
	rm -f *.wixpdb

${CS_BIN}/cryptol-test-runner: \
  $(CS_BIN)/cryptol            \
  $(CURDIR)/tests/Main.hs      \
  $(CURDIR)/tests/cryptol-test-runner.cabal
	$(CABAL) install ./tests

.PHONY: test
test: ${CS_BIN}/cryptol-test-runner
	( cd tests &&                                                      \
	echo "Testing on $(UNAME)-$(ARCH)" &&                              \
	$(realpath $(CS_BIN)/cryptol-test-runner)                          \
	  $(foreach t,$(TESTS),-d $t)                                      \
	  -c $(call adjust-path,$(realpath $(CS_BIN)/cryptol$(EXE_EXT))) \
	  -r output                                                        \
	  -T --hide-successes                                              \
	  -T --jxml=$(call adjust-path,$(CURDIR)/results.xml)              \
	  $(if $(TEST_DIFF),-p $(TEST_DIFF),)                              \
	)

.PHONY: notebook
notebook: ${CS_BIN}/cryptolnb
	cd notebook && ./notebook.sh


.PHONY: clean
clean:
	cabal clean
	rm -f src/GitRev.hs
	rm -f $(CS_BIN)/cryptol
	rm -f $(CS_BIN)/cryptol-test-suite
	rm -f $(CS_BIN)/cryptolnb
	rm -rf cryptol-${VERSION}*/
	rm -rf cryptol-${VERSION}*.tar.gz
	rm -rf cryptol-${VERSION}*.zip
	rm -rf cryptol-${VERSION}*.msi

.PHONY: squeaky
squeaky: clean
	-$(CABAL_EXE) sandbox delete
	(cd docs; make clean)
	rm -rf dist
	rm -rf tests/dist
