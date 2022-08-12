CFLAGS += -Wall -Werror

# For each C file foo.c, we make a phony target foo, then depending on the OS
# map that to either foo.dylib or foo.so.

CFILES = $(wildcard *.c)
TARGETS = $(CFILES:.c=)

all: $(TARGETS)

.PHONY: all clean $(TARGETS)

ifeq ($(shell uname),Darwin)
EXT = .dylib
else
EXT = .so
endif

$(TARGETS): %: %$(EXT)

%.dylib: %.c
	$(CC) $(CFLAGS) -dynamiclib $< -o $@

%.so: %.c
	$(CC) $(CFLAGS) -fPIC -shared $< -o $@

clean:
	rm *$(EXT)
