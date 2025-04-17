TOP=../../..

CFLAGS += -Wall -Werror -I$(TOP)/lib
LDLIBS += -lgmp

# For each C file foo.c, we make a phony target foo, then depending on the OS
# map that to foo.dylib, foo.so, or foo.dll.

CFILES = $(wildcard *.c)
TARGETS = $(CFILES:.c=)

all: $(TARGETS)

.PHONY: all clean $(TARGETS)

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

$(TARGETS): %: %$(EXT)

%.dylib: %.c
	$(CC) $(CFLAGS) -dynamiclib $< $(LDLIBS) -o $@

%.so: %.c
	$(CC) $(CFLAGS) -fPIC -shared $< $(LDLIBS) -o $@

%.dll: %.c
	$(CC) $(CFLAGS) -fPIC -shared $< $(LDLIBS) -o $@

clean:
	rm *$(EXT)
