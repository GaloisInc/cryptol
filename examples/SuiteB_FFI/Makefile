SHELL = /bin/bash
CFLAGS = -O3 -Wall -Wextra -Werror

.PHONY: clean

ifeq ($(shell uname -m),x86_64)

ifdef PORTABLE
CFLAGS += -maes -mssse3
else
CFLAGS += -march=native
endif

endif

ifeq ($(shell uname),Darwin)

SO = SuiteB_FFI.dylib

$(SO): SuiteB_FFI.c
	$(CC) $(CFLAGS) -dynamiclib $< -o $@

else

SO = SuiteB_FFI.so

$(SO): SuiteB_FFI.c
	$(CC) $(CFLAGS) -fPIC -shared $< -o $@

endif

clean:
	rm $(SO)
