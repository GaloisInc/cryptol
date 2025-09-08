MACHINE = $(shell $(CC) -dumpmachine)
ifneq (, $(findstring darwin, $(MACHINE)))
EXT = .dylib
else ifneq (, $(findstring cygwin, $(MACHINE)))
EXT = .dll
else ifneq (, $(findstring mingw, $(MACHINE)))
EXT = .dll
else ifneq (, $(findstring windows, $(MACHINE)))
EXT = .dll
else
EXT = .so
endif

all: Example$(EXT)

Example$(EXT): src/*.rs
	cargo build --examples
	cp $$(find target/ -iname "libexample$(EXT)") $@

.PHONY: test-example
test-example: Example.icry Example.cry Example$(EXT)
	cryptol -b Example.icry

.PHONY: clean
clean:
	rm -f *$(EXT)
