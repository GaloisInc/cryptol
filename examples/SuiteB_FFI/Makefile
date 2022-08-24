SHELL = /bin/bash
CFLAGS = -O3 -Wall -Wextra -Werror

.PHONY: test clean

ifeq ($(shell uname -m),x86_64)

ifdef PORTABLE
CFLAGS += -maes -mssse3
else
CFLAGS += -march=native
endif

endif

ifeq ($(shell uname),Darwin)

SO = SuiteB_FFI.dylib
TEST_OUT_EXT = .stdout.darwin

$(SO): SuiteB_FFI.c
	$(CC) $(CFLAGS) -dynamiclib $< -o $@

else

SO = SuiteB_FFI.so
TEST_OUT_EXT = .stdout

$(SO): SuiteB_FFI.c
	$(CC) $(CFLAGS) -fPIC -shared $< -o $@

endif

test: $(SO)
	diff tests/aes-vectors.icry$(TEST_OUT_EXT) <(cryptol -b tests/aes-vectors.icry)
	diff tests/aes-mct-ecb.icry$(TEST_OUT_EXT) <(cryptol -b tests/aes-mct-ecb.icry)

clean:
	rm $(SO)
