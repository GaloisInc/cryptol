CFLAGS += -O3 -Wall -Wextra -Werror

.PHONY: clean

ifeq ($(shell uname -m),x86_64)

CFLAGS += -maes -mssse3

endif

ifeq ($(shell uname),Darwin)

SuiteB_FFI.dylib: SuiteB_FFI.c
	$(CC) $(CFLAGS) -dynamiclib $< -o $@

clean:
	rm SuiteB_FFI.dylib

else

SuiteB_FFI.so: SuiteB_FFI.c
	$(CC) $(CFLAGS) -fPIC -shared $< -o $@

clean:
	rm SuiteB_FFI.so

endif
